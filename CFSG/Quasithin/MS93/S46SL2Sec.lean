module

public import CFSG.Quasithin.MS93.S46SL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups Matrix commutatorElement

theorem exists_odd_preimage_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    {f : A →* B} (hf : Function.Surjective f) {g : B} (hg : Odd (orderOf g)) :
    ∃ a : A, f a = g ∧ Odd (orderOf a) := by
  obtain ⟨q, rfl⟩ := hf g
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
  have hr : orderOf (q ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hcop : (2 ^ k).Coprime (orderOf (f q)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hg.not_two_dvd_nat)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(q ^ 2 ^ k) ^ t, by rw [map_pow, map_pow, ht], ?_⟩
  have hdvd : orderOf ((q ^ 2 ^ k) ^ t) ∣ m := hr ▸ orderOf_pow_dvd t
  exact Odd.of_dvd_nat hm hdvd

variable {G : Type*} [Group G] {K V Z : Subgroup G}

theorem subgroupOf_normal_of_comm (hZV : Z ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z) :
    (Z.subgroupOf V).Normal := ⟨fun z hz v => by
  rw [Subgroup.mem_subgroupOf] at hz ⊢
  have h := hVc v v.2 z (hZV hz)
  have he : ((v * z * v⁻¹ : ↥V) : G) = ⁅(v : G), (z : G)⁆ * z := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [he]
  exact Z.mul_mem h hz⟩

theorem natural_sec_of_ff [Finite K] [Finite V] {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (θ : ↥K →* SL(2, F)) (hθ : Function.Surjective θ)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hZV : Z ≤ V) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z) (hV2 : ∀ v ∈ V, v * v ∈ Z)
    (hker : ∀ k : ↥K, θ k = 1 → ∀ v ∈ V, ⁅(k : G), v⁆ ∈ Z)
    {X : Subgroup G} (hX : IsPGroup 2 ((X.subgroupOf K).map θ))
    (hXc : Nat.card ((X.subgroupOf K).map θ) = Nat.card F)
    {C : Subgroup G} (hCX : ∀ x ∈ X, ∀ c ∈ C, ⁅x, c⁆ ∈ Z)
    (hCi : C.relIndex V ≤ Fintype.card F) :
    (∀ k ∈ K, Odd (orderOf k) → ∀ v ∈ V, ⁅k, v⁆ ∈ Z) ∨
    ∃ β : ↥V →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
      (∀ v : ↥V, β v = 1 ↔ ∀ k ∈ K, Odd (orderOf k) → ⁅k, (v : G)⁆ ∈ Z) ∧
      ∀ (k : ↥K) (u v : ↥V), (v : G) = k * u * k⁻¹ →
        Multiplicative.toAdd (β v) =
          (θ k : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β u) := by
  classical
  have hN : (Z.subgroupOf V).Normal := subgroupOf_normal_of_comm hZV hVc
  let _ : CommGroup (V ⧸ Z.subgroupOf V) :=
    { (QuotientGroup.Quotient.group (Z.subgroupOf V)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h := hVc _ (V.inv_mem b.2) _ (V.inv_mem a.2)
            have he : (((a * b)⁻¹ * (b * a) : ↥V) : G) = ⁅((b : G))⁻¹, ((a : G))⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
              group
            rw [he]
            exact h }
  have hmk : ∀ q : Additive (V ⧸ Z.subgroupOf V), ∃ v : ↥V,
      q = Additive.ofMul (v : V ⧸ Z.subgroupOf V) := fun q => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨v, by rw [hv]; rfl⟩
  have h2 : ∀ q : Additive (V ⧸ Z.subgroupOf V), 2 • q = 0 := by
    intro q
    obtain ⟨v, rfl⟩ := hmk q
    rw [← ofMul_pow, ← ofMul_one, ← QuotientGroup.mk_pow]
    congr 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
    exact hV2 _ v.2
  let _ : Module (ZMod 2) (Additive (V ⧸ Z.subgroupOf V)) := AddCommGroup.zmodModule h2
  have : Finite (Additive (V ⧸ Z.subgroupOf V)) :=
    Finite.of_surjective (fun v : ↥V => Additive.ofMul (v : V ⧸ Z.subgroupOf V)) fun q => by
      obtain ⟨v, rfl⟩ := hmk q
      exact ⟨v, rfl⟩
  let cj : ↥K → (↥V →* ↥V) := fun k =>
    { toFun := fun v => ⟨(k : G) * v * (k : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hKV k.2) v).mp v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcj : ∀ (k : ↥K) (v : ↥V), ((cj k v : ↥V) : G) = (k : G) * v * (k : G)⁻¹ :=
    fun k v => rfl
  let cq : ↥K → (V ⧸ Z.subgroupOf V →* V ⧸ Z.subgroupOf V) := fun k =>
    QuotientGroup.map (Z.subgroupOf V) (Z.subgroupOf V) (cj k) (fun z hz => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hcj]
      exact (Subgroup.mem_normalizer_iff.mp (hKZ k.2) z).mp (Subgroup.mem_subgroupOf.mp hz))
  have hcq : ∀ (k : ↥K) (v : ↥V), cq k (v : V ⧸ Z.subgroupOf V) =
      ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) := fun k v => rfl
  let act : ↥K →* (Additive (V ⧸ Z.subgroupOf V) →ₗ[ZMod 2] Additive (V ⧸ Z.subgroupOf V)) :=
    { toFun := fun k => (MonoidHom.toAdditive (cq k)).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq 1 (v : V ⧸ Z.subgroupOf V)) = Additive.ofMul _
        rw [hcq]
        congr 2
        exact Subtype.ext (by rw [hcj]; simp)
      map_mul' := fun k k' => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨v, rfl⟩ := hmk q
        show Additive.ofMul (cq (k * k') (v : V ⧸ Z.subgroupOf V)) =
          Additive.ofMul (cq k (cq k' (v : V ⧸ Z.subgroupOf V)))
        rw [hcq, hcq, hcq]
        congr 2
        exact Subtype.ext (by rw [hcj, hcj, hcj]; simp [mul_assoc]) }
  have hact : ∀ (k : ↥K) (v : ↥V), act k (Additive.ofMul (v : V ⧸ Z.subgroupOf V)) =
      Additive.ofMul ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) := fun k v => rfl
  have hZconj : ∀ w ∈ V, ∀ z ∈ Z, w * z * w⁻¹ ∈ Z := by
    intro w hw z hz
    have e : w * z * w⁻¹ = ⁅w, z⁆ * z := by rw [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (hVc w hw z (hZV hz)) hz
  have hfix : ∀ (k : ↥K) (v : ↥V), act k (Additive.ofMul (v : V ⧸ Z.subgroupOf V)) =
      Additive.ofMul (v : V ⧸ Z.subgroupOf V) ↔ ⁅(k : G), (v : G)⁆ ∈ Z := by
    intro k v
    rw [hact]
    have key : Additive.ofMul ((cj k v : ↥V) : V ⧸ Z.subgroupOf V) =
        Additive.ofMul (v : V ⧸ Z.subgroupOf V) ↔
        ((k : G) * v * (k : G)⁻¹)⁻¹ * v ∈ Z := by
      rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv, hcj]
    rw [key]
    constructor
    · intro h
      have e : ⁅(k : G), (v : G)⁆ = (v : G) * (((k : G) * v * (k : G)⁻¹)⁻¹ * v)⁻¹ * (v : G)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact hZconj _ v.2 _ (Z.inv_mem h)
    · intro h
      have e : ((k : G) * v * (k : G)⁻¹)⁻¹ * v =
          (v : G)⁻¹ * ⁅(k : G), (v : G)⁆⁻¹ * (v : G)⁻¹⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact hZconj _ (V.inv_mem v.2) _ (Z.inv_mem h)
  have hkerle : θ.ker ≤ act.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := hmk q
    rw [Module.End.one_apply]
    exact (hfix k v).mpr (hker k hk v v.2)
  let e := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let ρ : Representation (ZMod 2) SL(2, F) (Additive (V ⧸ Z.subgroupOf V)) :=
    (QuotientGroup.lift θ.ker act hkerle).comp e.symm.toMonoidHom
  have hρ : ∀ k, ρ (θ k) = act k := by
    intro k
    have he : e.symm (θ k) = (k : ↥K ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift θ.ker act hkerle (e.symm (θ k)) = act k
    rw [he, QuotientGroup.lift_mk]
  set Xθ := (X.subgroupOf K).map θ with hXθ
  have hoff : Nat.card (Additive (V ⧸ Z.subgroupOf V)) ≤
      Nat.card F * Nat.card (sl2Fix ρ (Xθ : Set SL(2, F))) := by
    set I := (C.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V)) with hIdef
    have hI1 : I.index ≤ Fintype.card F := by
      have h1 := Subgroup.index_map_dvd (C.subgroupOf V) (QuotientGroup.mk'_surjective
        (Z.subgroupOf V))
      have h2 : (C.subgroupOf V).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1).trans hCi
    have hI2 := I.index_mul_card
    have hmemI : ∀ q ∈ I, Additive.ofMul q ∈ sl2Fix ρ (Xθ : Set SL(2, F)) := by
      rintro _ ⟨c, hc, rfl⟩ g ⟨x, hx, rfl⟩
      rw [hρ]
      exact (hfix x c).mpr (hCX _ (Subgroup.mem_subgroupOf.mp hx) _
        (Subgroup.mem_subgroupOf.mp hc))
    have hI3 : Nat.card I ≤ Nat.card (sl2Fix ρ (Xθ : Set SL(2, F))) :=
      Nat.card_le_card_of_injective
        (fun q : I => (⟨Additive.ofMul (q : V ⧸ Z.subgroupOf V), hmemI q q.2⟩ :
          sl2Fix ρ (Xθ : Set SL(2, F))))
        (fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Additive.ofMul.injective h'))
    calc Nat.card (Additive (V ⧸ Z.subgroupOf V)) = I.index * Nat.card I := hI2.symm
      _ ≤ Fintype.card F * Nat.card (sl2Fix ρ (Xθ : Set SL(2, F))) := Nat.mul_le_mul hI1 hI3
      _ = Nat.card F * Nat.card (sl2Fix ρ (Xθ : Set SL(2, F))) := by
        rw [Nat.card_eq_fintype_card (α := F)]
  have hoddK : ∀ k : ↥K, Odd (orderOf (k : G)) → Odd (orderOf (θ k)) := fun k hk =>
    Odd.of_dvd_nat (by rwa [Subgroup.orderOf_coe] at hk) (orderOf_map_dvd θ k)
  rcases natural_of_sl2Fix ρ hF Xθ hX hXc hoff with hall | ⟨φ, hφs, hφeq, hφker⟩
  · left
    intro k hk hodd v hv
    have hmem : Additive.ofMul ((⟨v, hv⟩ : ↥V) : V ⧸ Z.subgroupOf V) ∈ sl2OddFix ρ :=
      hall ▸ Submodule.mem_top
    have h1 := (mem_sl2OddFix ρ).mp hmem _ (hoddK ⟨k, hk⟩ hodd)
    rw [hρ] at h1
    exact (hfix ⟨k, hk⟩ ⟨v, hv⟩).mp h1
  · right
    let β : ↥V →* Multiplicative (Fin 2 → F) :=
      { toFun := fun v => Multiplicative.ofAdd (φ (Additive.ofMul (v : V ⧸ Z.subgroupOf V)))
        map_one' := by
          show Multiplicative.ofAdd (φ (Additive.ofMul ((1 : ↥V) : V ⧸ Z.subgroupOf V))) = 1
          rw [QuotientGroup.mk_one, ofMul_one, map_zero, ofAdd_zero]
        map_mul' := fun a b => by
          show Multiplicative.ofAdd (φ (Additive.ofMul ((a * b : ↥V) : V ⧸ Z.subgroupOf V))) =
            Multiplicative.ofAdd (φ (Additive.ofMul (a : V ⧸ Z.subgroupOf V))) *
              Multiplicative.ofAdd (φ (Additive.ofMul (b : V ⧸ Z.subgroupOf V)))
          rw [QuotientGroup.mk_mul, ofMul_mul, map_add, ofAdd_add] }
    have hβ : ∀ v, β v = Multiplicative.ofAdd (φ (Additive.ofMul (v : V ⧸ Z.subgroupOf V))) :=
      fun v => rfl
    refine ⟨β, fun y => ?_, fun v => ?_, fun k u v huv => ?_⟩
    · obtain ⟨q, hq⟩ := hφs (Multiplicative.toAdd y)
      obtain ⟨v, rfl⟩ := hmk q
      exact ⟨v, by rw [hβ, hq, ofAdd_toAdd]⟩
    · rw [hβ, ofAdd_eq_one, hφker, mem_sl2OddFix]
      constructor
      · intro h k hk hodd
        have h1 := h _ (hoddK ⟨k, hk⟩ hodd)
        rw [hρ] at h1
        exact (hfix ⟨k, hk⟩ v).mp h1
      · intro h g hg
        obtain ⟨k, rfl, hkodd⟩ := exists_odd_preimage_of_surjective hθ hg
        rw [hρ]
        refine (hfix k v).mpr (h k k.2 ?_)
        rwa [Subgroup.orderOf_coe]
    · have hv : v = cj k u := Subtype.ext (by rw [hcj]; exact huv)
      rw [hβ, hβ, toAdd_ofAdd, toAdd_ofAdd, ← hφeq, hρ, hact, hv]

end CFSG.Quasithin.MS93.S46
