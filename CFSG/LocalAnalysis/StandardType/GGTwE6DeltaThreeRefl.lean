module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONTools
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeReflCore
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Open

section Refl

variable {R : Type} [Group R]

@[expose] def ReflData (Y : Subgroup (MulAut R)) : Prop :=
  ∃ ρ h : Fin 5 → MulAut R, (∀ i, ρ i ∈ (MulAut.conj : R →* MulAut R).range) ∧ (∀ i, h i ∈ Y) ∧
    (∀ i, ∀ y ∈ Y, ∃ k : ℕ, ρ i * y * (ρ i)⁻¹ = h i ^ k * y) ∧
    (∀ i, ρ i * h i * (ρ i)⁻¹ = (h i)⁻¹) ∧ 3 ^ 5 ≤ Nat.card (Subgroup.closure (Set.range h))

theorem congr_conj {R' : Type} [Group R'] (e : R ≃* R') (r : R) :
    MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext x
  simp [MulAut.conj_apply]

theorem ReflData.of_comap {R' : Type} [Group R'] (e : R ≃* R') {Y' : Subgroup (MulAut R')}
    (hY : ReflData (Y'.comap (MulAut.congr e).toMonoidHom)) : ReflData Y' := by
  obtain ⟨ρ, h, hρ, hh, hρy, hρh, hcard⟩ := hY
  set Φ := MulAut.congr e with hΦ
  refine ⟨fun i => Φ (ρ i), fun i => Φ (h i), fun i => ?_, hh, fun i y hy => ?_, fun i => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hρ i
    refine ⟨e r, ?_⟩
    change MulAut.conj (e r) = Φ (ρ i)
    rw [← hr]
    exact (congr_conj e r).symm
  · obtain ⟨k, hk⟩ := hρy i (Φ.symm y) (show Φ (Φ.symm y) ∈ Y' by rwa [MulEquiv.apply_symm_apply])
    refine ⟨k, ?_⟩
    have h1 := congrArg Φ.toMonoidHom hk
    rwa [map_mul, map_mul, map_inv, map_mul, map_pow, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] at h1
  · have h1 := congrArg Φ.toMonoidHom (hρh i)
    rwa [map_mul, map_mul, map_inv, map_inv, MulEquiv.coe_toMonoidHom] at h1
  · have hr : Set.range (fun i => Φ (h i)) = Φ.toMonoidHom '' Set.range h := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← MonoidHom.map_closure,
      Subgroup.card_map_of_injective (f := Φ.toMonoidHom) (fun a b hab => Φ.injective hab)]
    exact hcard

end Refl

theorem exists_fixed_of_reflData {R L' : Type} [Group R] [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ3 : Nat.card (Subgroup.center L') = 3) (hZR : Subgroup.center R = ⊥)
    {Y : Subgroup (MulAut R)} (hY : IsElemAbelian 3 Y) (hρ : ReflData Y) :
    ∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E ∧
      ∀ a : MulAut L', a ^ 3 = 1 → (∃ φ ∈ Y, ∀ l, φ (ψ l) = ψ (a l)) → ∀ e ∈ E, a e = e := by
  classical
  obtain ⟨ρ, h, hρ, hhY, hρy, hρh, hcard⟩ := hρ
  have hcinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hrZ : r ∈ Subgroup.center R := Subgroup.mem_center_iff.mpr fun g => by
      have h1 := congrArg (fun f : MulAut R => f g) hr
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * r = r * g * r⁻¹ * r := by rw [h1]
        _ = r * g := by group
    rwa [hZR] at hrZ
  have hconj : ∀ (φ : MulAut R) (r : R), φ * MulAut.conj r * φ⁻¹ = MulAut.conj (φ r) := by
    intro φ r
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := fun x hx y hy => hY.comm hx hy
  have hinn : ∀ i, ∃ s : R, MulAut.conj s = h i := by
    intro i
    obtain ⟨r, hr⟩ := hρ i
    refine ⟨r * h i r⁻¹, ?_⟩
    rw [map_mul, ← hconj, map_inv, hr]
    calc ρ i * (h i * (ρ i)⁻¹ * (h i)⁻¹) = ρ i * h i * (ρ i)⁻¹ * (h i)⁻¹ := by group
      _ = h i * (h i ^ 3)⁻¹ := by rw [hρh i]; group
      _ = h i := by rw [hY.2 _ (hhY i), inv_one, mul_one]
  choose s hs using hinn
  choose r hr using fun i => MonoidHom.mem_range.1 (hρ i)
  choose η hη using fun i => hψ (s i)
  choose m hm using fun i => hψ (r i)
  have hrs : ∀ i j, ∃ k : ℕ, r i * s j * (r i)⁻¹ = s i ^ k * s j := fun i j => by
    obtain ⟨k, hk⟩ := hρy i (h j) (hhY j)
    exact ⟨k, hcinj (by simpa only [map_mul, map_inv, map_pow, hr, hs] using hk)⟩
  have hrsi : ∀ i, r i * s i * (r i)⁻¹ = (s i)⁻¹ := fun i =>
    hcinj (by simpa only [map_mul, map_inv, hr, hs] using hρh i)
  have hφs : ∀ φ ∈ Y, ∀ i, φ (s i) = s i := fun φ hφ i =>
    hcinj (by rw [← hconj, hs, hYc _ hφ _ (hhY i), mul_inv_cancel_right])
  have hφr : ∀ φ ∈ Y, ∀ i, ∃ k : ℕ, φ (r i) = (s i ^ k)⁻¹ * r i := by
    intro φ hφ i
    obtain ⟨k, hk⟩ := hρy i φ hφ
    refine ⟨k, hcinj ?_⟩
    rw [← hconj]
    simp only [map_mul, map_inv, map_pow, hr, hs]
    rw [show h i ^ k = ρ i * φ * (ρ i)⁻¹ * φ⁻¹ by rw [hk, mul_inv_cancel_right]]
    group
  have hZ3' : ∀ z ∈ Subgroup.center L', z ^ 3 = 1 := fun z hz => by
    have h1 : (⟨z, hz⟩ : Subgroup.center L') ^ 3 = 1 := by rw [← hZ3]; exact pow_card_eq_one'
    simpa using congrArg Subtype.val h1
  have hmη : ∀ i, ψ (m i * η i * (m i)⁻¹) = ψ (η i)⁻¹ := fun i => by
    simpa only [map_mul, map_inv, hη, hm] using hrsi i
  have hcomm : ∀ i j, η i * η j = η j * η i := by
    intro i j
    obtain ⟨k, hk⟩ := hrs i j
    refine (commute_of_refl hker hZ3' (w := m i) (k := k) ?_ ?_ (hmη i)).symm
    · have hss : s j * s i = s i * s j :=
        hcinj (by simpa only [map_mul, hs] using hYc _ (hhY j) _ (hhY i))
      refine hker (MonoidHom.mem_ker.2 ?_)
      simp only [map_mul, map_inv, hη]
      rw [hss]
      group
    · simpa only [map_mul, map_inv, map_pow, hη, hm] using hk
  have hη3 : ∀ i, η i ^ 3 = 1 := fun i => pow_three_of_refl hker hZ3'
    (hker (MonoidHom.mem_ker.2 (hcinj (by
      rw [map_pow, hη, map_pow, hs, hY.2 _ (hhY i), map_one])))) (hmη i)
  set E : Subgroup L' := Subgroup.closure ((Subgroup.center L' : Set L') ∪ Set.range η) with hE
  have hEel : IsElemAbelian 3 E := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro x (hx | ⟨i, rfl⟩) y (hy | ⟨j, rfl⟩)
      · exact Subgroup.mem_center_iff.mp hy x
      · exact (Subgroup.mem_center_iff.mp hx (η j)).symm
      · exact Subgroup.mem_center_iff.mp hy (η i)
      · exact hcomm i j
    · rintro x (hx | ⟨i, rfl⟩)
      · exact hZ3' x hx
      · exact hη3 i
  haveI : Finite R := Finite.of_surjective ψ hψ
  let f : E →* R := ψ.comp E.subtype
  have hZf : Nat.card (Subgroup.center L') ≤ Nat.card f.ker := by
    refine Nat.card_le_card_of_injective
      (fun z => (⟨⟨z, Subgroup.subset_closure (Or.inl z.2)⟩, MonoidHom.mem_ker.2 ?_⟩ : f.ker))
      fun z w hzw => Subtype.ext (congrArg (fun x : f.ker => ((x : E) : L')) hzw)
    have hψz : ψ z ∈ Subgroup.center R := Subgroup.mem_center_iff.mpr fun g => by
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [hZR] at hψz
    exact hψz
  have hsf : Subgroup.closure (Set.range s) ≤ f.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨η i, Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)⟩, hη i⟩
  have hhs : Nat.card (Subgroup.closure (Set.range h)) =
      Nat.card (Subgroup.closure (Set.range s)) := by
    have h1 : Set.range h = (MulAut.conj : R →* MulAut R) '' Set.range s := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => (hs i).symm)
    rw [h1, ← MonoidHom.map_closure, Subgroup.card_map_of_injective hcinj]
  have hcardE : 3 ^ 6 ≤ Nat.card E := by
    have h1 := (hcard.trans hhs.le).trans (Subgroup.card_le_of_le hsf)
    rw [hZ3] at hZf
    rw [← Subgroup.card_ker_mul_card_range f]
    calc 3 ^ 6 = 3 * 3 ^ 5 := by norm_num
      _ ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul hZf h1
  refine ⟨E, hEel, hcardE, fun a ha3 ⟨φ, hφ, hφa⟩ => ?_⟩
  have haZ := CFSG.RankThree.PartTwo.Sec14.Res148.fix_center_of_pow_three a ha3 hZ3
  have hfix : Set.EqOn a.toMonoidHom (MonoidHom.id L')
      ((Subgroup.center L' : Set L') ∪ Set.range η) := by
    rintro x (hx | ⟨i, rfl⟩)
    · exact haZ x hx
    · obtain ⟨k, hk⟩ := hφr φ hφ i
      refine fix_of_refl hker hZ3' haZ (w := m i) (k := k) ?_ ?_ (hmη i)
      · rw [← hφa, hη, hφs φ hφ i]
      · rw [← hφa, hm, hk, map_mul, map_inv, map_pow, hη, hm]
  exact fun e he => MonoidHom.eqOn_closure hfix he

end CFSG.StandardType.TwE6D3
