module

public import CFSG.Assembly.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple.Factors

public section

open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

private theorem coe_sup_eq_mul_of_commute {H K : Subgroup G}
    (h : Commute (H : Set G) (K : Set G)) : ((H ⊔ K : Subgroup G) : Set G) = H * K := by
  have hKH : (K : Set G) * H = H * K := h.symm.eq
  let P : Subgroup G :=
    { carrier := (H : Set G) * K
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        obtain ⟨e, he, f, hf, hef⟩ : b * c ∈ (H : Set G) * K := by
          rw [← hKH]
          exact Set.mul_mem_mul hb hc
        exact ⟨a * e, mul_mem ha he, f * d, mul_mem hf hd, by
          rw [show a * b * (c * d) = a * (b * c) * d by group, ← hef]
          group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        obtain ⟨e, he, f, hf, hef⟩ : b⁻¹ * a⁻¹ ∈ (H : Set G) * K := by
          rw [← hKH]
          exact Set.mul_mem_mul (inv_mem hb) (inv_mem ha)
        exact ⟨e, he, f, hf, by rw [mul_inv_rev, ← hef]⟩ }
  have hsup : H ⊔ K = P :=
    le_antisymm
      (sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩)
        (fun b hb => ⟨1, H.one_mem, b, hb, one_mul b⟩))
      (by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact Subgroup.mul_mem_sup ha hb)
  rw [hsup]
  rfl

private theorem coe_iSup_eq_prod {n : ℕ} (K' : Fin n → Subgroup G)
    (hperm : ∀ i j, (K' i : Set G) * K' j = K' j * K' i) :
    ((⨆ i, K' i : Subgroup G) : Set G) = (List.ofFn fun i => (K' i : Set G)).prod := by
  induction n with
  | zero => simp [Set.singleton_one]
  | succ n ih =>
    have hsup : (⨆ i, K' i : Subgroup G) = (⨆ i : Fin n, K' i.castSucc) ⊔ K' (Fin.last n) :=
      le_antisymm
        (iSup_le (Fin.lastCases le_sup_right fun i =>
          le_sup_of_le_left (le_iSup (fun j : Fin n => K' j.castSucc) i)))
        (sup_le (iSup_le fun i => le_iSup _ _) (le_iSup _ _))
    have hih := ih (fun i => K' i.castSucc) fun i j => hperm _ _
    have hc : Commute ((⨆ i : Fin n, K' i.castSucc : Subgroup G) : Set G)
        (K' (Fin.last n) : Set G) := by
      rw [hih]
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hperm _ _
    rw [hsup, List.ofFn_succ', List.prod_concat, ← hih]
    exact coe_sup_eq_mul_of_commute hc

private theorem le_normalizer_iSup {ι : Type*} {A : Subgroup G} (K' : ι → Subgroup G)
    (hinv : ∀ i, A ≤ Subgroup.normalizer (K' i : Set G)) :
    A ≤ Subgroup.normalizer ((⨆ i, K' i : Subgroup G) : Set G) := by
  have key : ∀ a ∈ A, ∀ m ∈ (⨆ i, K' i : Subgroup G), a * m * a⁻¹ ∈ (⨆ i, K' i : Subgroup G) := by
    intro a ha m hm
    refine Subgroup.iSup_induction K' (C := fun m => a * m * a⁻¹ ∈ (⨆ i, K' i : Subgroup G)) hm
      (fun i x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_normalizer_iff.mp (hinv i ha) x).mp hx)
    · rw [show a * (x * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹) by group]
      exact mul_mem hx hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨key a ha m, fun h => ?_⟩
  simpa [mul_assoc] using key a⁻¹ (inv_mem ha) _ h

private theorem list_prod_subset (J : Subgroup G) :
    ∀ l : List (Set G), (∀ s ∈ l, s ⊆ (J : Set G)) → l.prod ⊆ (J : Set G)
  | [], _ => by simp
  | s :: l, h => by
    rw [List.prod_cons]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (h s (by simp) hx)
      (list_prod_subset J l (fun t ht => h t (by simp [ht])) hy)

theorem exists_mul_of_mem_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {A K₁ K₂ : Subgroup G}
    (hA : IsPGroup p A) (h₁ : Nat.Coprime p (Nat.card K₁))
    (hA₁ : A ≤ Subgroup.normalizer (K₁ : Set G)) (hA₂ : A ≤ Subgroup.normalizer (K₂ : Set G))
    {x : G} (hx : x ∈ (K₁ : Set G) * K₂) (hxA : x ∈ Subgroup.centralizer (A : Set G)) :
    ∃ a ∈ K₁ ⊓ Subgroup.centralizer (A : Set G), ∃ b ∈ K₂ ⊓ Subgroup.centralizer (A : Set G),
      x = a * b := by
  have := Fact.mk hp
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := Set.mem_mul.mp hx
  replace ha₀ : a₀ ∈ K₁ := ha₀
  replace hb₀ : b₀ ∈ K₂ := hb₀
  have hΩ₀ : a₀⁻¹ * x ∈ K₂ := by
    rw [← hab₀, inv_mul_cancel_left]
    exact hb₀
  have hmem : ∀ (α : A) (a : G), a ∈ K₁ ∧ a⁻¹ * x ∈ K₂ →
      (α : G) * a * (α : G)⁻¹ ∈ K₁ ∧ ((α : G) * a * (α : G)⁻¹)⁻¹ * x ∈ K₂ := by
    rintro α a ⟨ha₁, ha₂⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hA₁ α.2) a).mp ha₁, ?_⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (hA₂ α.2) _).mp ha₂
    have hcomm : (α : G)⁻¹ * x = x * (α : G)⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp hxA) _ (inv_mem α.2)
    convert h2 using 1
    calc ((α : G) * a * (α : G)⁻¹)⁻¹ * x = (α : G) * a⁻¹ * ((α : G)⁻¹ * x) := by group
      _ = (α : G) * a⁻¹ * (x * (α : G)⁻¹) := by rw [hcomm]
      _ = (α : G) * (a⁻¹ * x) * (α : G)⁻¹ := by group
  let Ω : Type _ := {a : G // a ∈ K₁ ∧ a⁻¹ * x ∈ K₂}
  let _ : MulAction A Ω :=
    { smul := fun α a => ⟨(α : G) * a.1 * (α : G)⁻¹, hmem α a.1 a.2⟩
      one_smul := fun a => Subtype.ext (by
        change ((1 : A) : G) * a.1 * ((1 : A) : G)⁻¹ = a.1
        simp)
      mul_smul := fun α β a => Subtype.ext (by
        change ((α * β : A) : G) * a.1 * ((α * β : A) : G)⁻¹ =
          (α : G) * ((β : G) * a.1 * (β : G)⁻¹) * (α : G)⁻¹
        simp [mul_assoc]) }
  let e : ↥(K₁ ⊓ K₂) ≃ Ω :=
    { toFun := fun d => ⟨a₀ * d, Subgroup.mul_mem _ ha₀ (Subgroup.mem_inf.mp d.2).1, by
        rw [mul_inv_rev, mul_assoc]
        exact mul_mem (inv_mem (Subgroup.mem_inf.mp d.2).2) hΩ₀⟩
      invFun := fun a => ⟨a₀⁻¹ * a.1, Subgroup.mem_inf.mpr
        ⟨mul_mem (inv_mem ha₀) a.2.1, by
          have := mul_mem hΩ₀ (inv_mem a.2.2)
          convert this using 1
          group⟩⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun a => Subtype.ext (by simp) }
  have hcard : Nat.card Ω = Nat.card ↥(K₁ ⊓ K₂) := (Nat.card_congr e).symm
  have hnd : ¬ p ∣ Nat.card Ω := by
    rw [hcard]
    exact hp.coprime_iff_not_dvd.mp
      (h₁.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨⟨a, haΩ⟩, hfix⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card Ω hnd
  have hfix' : ∀ α : A, (α : G) * a * (α : G)⁻¹ = a := fun α =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp hfix α)
  have haC : a ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := hfix' ⟨h, hh⟩
    calc h * a = h * a * h⁻¹ * h := by group
      _ = a * h := by rw [show h * a * h⁻¹ = a from this]
  exact ⟨a, Subgroup.mem_inf.mpr ⟨haΩ.1, haC⟩, a⁻¹ * x,
    Subgroup.mem_inf.mpr ⟨haΩ.2, mul_mem (inv_mem haC) hxA⟩, (mul_inv_cancel_left a x).symm⟩

theorem centralizer_eq_prod_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {A K : Subgroup G}
    (hA : IsPGroup p A) (hK : Nat.Coprime p (Nat.card K)) {n : ℕ} (K' : Fin n → Subgroup G)
    (hinv : ∀ i, A ≤ Subgroup.normalizer (K' i : Set G))
    (hperm : ∀ i j, (K' i : Set G) * K' j = K' j * K' i) (hgen : ⨆ i, K' i = K) :
    ((K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) =
      (List.ofFn fun i => ((K' i ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G)).prod :=
  by
  induction n generalizing K with
  | zero =>
    have hK0 : K = ⊥ := by rw [← hgen]; exact iSup_of_empty K'
    subst hK0
    simp [Set.singleton_one]
  | succ n ih =>
    have hsup : (⨆ i, K' i : Subgroup G) = (⨆ i : Fin n, K' i.castSucc) ⊔ K' (Fin.last n) :=
      le_antisymm
        (iSup_le (Fin.lastCases le_sup_right fun i =>
          le_sup_of_le_left (le_iSup (fun j : Fin n => K' j.castSucc) i)))
        (sup_le (iSup_le fun i => le_iSup _ _) (le_iSup _ _))
    have hK₁le : (⨆ i : Fin n, K' i.castSucc : Subgroup G) ≤ K := by
      rw [← hgen, hsup]
      exact le_sup_left
    have hK₂le : K' (Fin.last n) ≤ K := by
      rw [← hgen, hsup]
      exact le_sup_right
    have hK₁cop : Nat.Coprime p (Nat.card (⨆ i : Fin n, K' i.castSucc : Subgroup G)) :=
      hK.coprime_dvd_right (Subgroup.card_dvd_of_le hK₁le)
    have hrec := ih (K := (⨆ i : Fin n, K' i.castSucc : Subgroup G)) (hK := hK₁cop)
      (K' := fun i => K' i.castSucc) (hinv := fun i => hinv _) (hperm := fun i j => hperm _ _)
      (hgen := rfl)
    have hc : Commute ((⨆ i : Fin n, K' i.castSucc : Subgroup G) : Set G)
        (K' (Fin.last n) : Set G) := by
      rw [coe_iSup_eq_prod (fun i => K' i.castSucc) fun i j => hperm _ _]
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hperm _ _
    have hKmul : (K : Set G) = (⨆ i : Fin n, K' i.castSucc : Subgroup G) * K' (Fin.last n) := by
      rw [← hgen, hsup]
      exact coe_sup_eq_mul_of_commute hc
    rw [List.ofFn_succ', List.prod_concat, ← hrec]
    ext x
    constructor
    · rintro ⟨hxK, hxC⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_centralizer hp hA hK₁cop
        (le_normalizer_iSup _ fun i => hinv _) (hinv _) (hKmul ▸ hxK) hxC
      exact Set.mul_mem_mul ha hb
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨mul_mem (hK₁le ha.1) (hK₂le hb.1), mul_mem ha.2 hb.2⟩

theorem centralizer_eq_iSup_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {A K : Subgroup G}
    (hA : IsPGroup p A) (hK : Nat.Coprime p (Nat.card K)) {n : ℕ} (K' : Fin n → Subgroup G)
    (hinv : ∀ i, A ≤ Subgroup.normalizer (K' i : Set G))
    (hperm : ∀ i j, (K' i : Set G) * K' j = K' j * K' i) (hgen : ⨆ i, K' i = K) :
    K ⊓ Subgroup.centralizer (A : Set G) = ⨆ i, K' i ⊓ Subgroup.centralizer (A : Set G) := by
  refine le_antisymm ?_
    (iSup_le fun i => inf_le_inf_right _ (hgen ▸ le_iSup (fun j => K' j) i))
  intro x hx
  have hx' : x ∈ ((K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := hx
  rw [centralizer_eq_prod_centralizer hp hA hK K' hinv hperm hgen] at hx'
  refine list_prod_subset (⨆ i, K' i ⊓ Subgroup.centralizer (A : Set G)) _ (fun s hs => ?_) hx'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  exact fun y hy => Subgroup.mem_iSup_of_mem i hy

end CFSG.SignalizerFunctorTheorem.McBride
