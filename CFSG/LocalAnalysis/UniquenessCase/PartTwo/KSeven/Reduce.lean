module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.Open Subgroup

private def ksred_conj {A : Type*} [Group A] (J : Subgroup A) (y : A)
    (hy : y ∈ normalizer (J : Set A)) : ↥J ≃* ↥J where
  toFun x := ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy x).1 x.2⟩
  invFun x := ⟨y⁻¹ * x * y, by
    have h2 := (Subgroup.mem_normalizer_iff.1 hy (y⁻¹ * x * y)).2
    have e : y * (y⁻¹ * (x : A) * y) * y⁻¹ = x := by group
    rw [e] at h2
    exact h2 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y' := Subtype.ext (by simp [mul_assoc])

private theorem ksred_conj_apply {A : Type*} [Group A] (J : Subgroup A) (y : A)
    (hy : y ∈ normalizer (J : Set A)) (x : ↥J) :
    ((ksred_conj J y hy x : ↥J) : A) = y * x * y⁻¹ := rfl

@[expose] def SevenCore (J : Type) [Group J] : Prop :=
  ∀ W : Subgroup (MulAut J), IsPGroup 7 W → W ≠ ⊥ → ∀ (Z : Sylow 3 J) (T : Sylow 2 J),
    (∀ w ∈ W, ∀ z ∈ (Z : Subgroup J), w z = z) →
      normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W ⊔ (T : Subgroup J) = ⊤

theorem ksevenGen_of_sevenCore
    (h : ∀ (J : Type) [Group J] [Finite J], IsKGroup J → IsSimpleGroup J → 3 ∣ Nat.card J →
      ¬ 9 ∣ Nat.card J → ¬ 7 ∣ Nat.card J → SevenCore J) : KSevenGen := by
  intro A _ _ hK J Y Z T hJs h3 h9 h7 hY hYN hYC hZ hZY hT
  obtain ⟨Z', hZ'⟩ := hZ
  obtain ⟨T', hT'⟩ := hT
  have hKJ : CFSG.Open.IsKGroup ↥J := hK.subgroup J
  have hKJ' : IsKGroup ↥J :=
    KCore.KGroupNonab.kGroupAllSimple Assembly.inCatalog_isoInvariant
      Assembly.inCatalog_containsAbelianSimple hKJ
  let ρ : ↥Y →* MulAut ↥J :=
    { toFun := fun y => ksred_conj J (y : A) (hYN y.2)
      map_one' := by
        ext x
        simp [ksred_conj_apply]
      map_mul' := fun a b => by
        ext x
        simp only [ksred_conj_apply, MulAut.mul_apply, Subgroup.coe_mul]
        group }
  have hρ : ∀ (y : ↥Y) (x : ↥J), ((ρ y x : ↥J) : A) = (y : A) * (x : A) * (y : A)⁻¹ :=
    fun y x => rfl
  let W : Subgroup (MulAut ↥J) := ρ.range
  have hWp : IsPGroup 7 W := by
    have := hY.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    simpa [W] using this
  have hWne : W ≠ ⊥ := by
    obtain ⟨y, hyY, hyC⟩ := Set.not_subset.1
      (show ¬ (Y : Set A) ⊆ (centralizer (J : Set A) : Set A) from hYC)
    have hyC' : ¬ ∀ j ∈ (J : Set A), j * y = y * j :=
      fun h => hyC (Subgroup.mem_centralizer_iff.2 h)
    obtain ⟨j, hj⟩ := not_forall.1 hyC'
    obtain ⟨hjJ, hjy⟩ := not_imp.1 hj
    have hyj : y * j ≠ j * y := fun heq => hjy heq.symm
    have hne : ksred_conj J y (hYN hyY) ⟨j, hjJ⟩ ≠ ⟨j, hjJ⟩ := by
      intro heq
      apply hyj
      have hval : y * j * y⁻¹ = j := by
        have h := congrArg (Subtype.val) heq
        simpa [ksred_conj_apply] using h
      exact mul_inv_eq_iff_eq_mul.1 hval
    intro hbot
    have hmem : ksred_conj J y (hYN hyY) ∈ W := ⟨⟨y, hyY⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne (by
      have h := congrArg (fun f : MulAut ↥J => f ⟨j, hjJ⟩) hmem
      simpa using h)
  have hfix : ∀ w ∈ W, ∀ z ∈ (Z' : Subgroup ↥J), w z = z := by
    intro w hw z hz
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 (show w ∈ ρ.range from hw)
    apply Subtype.ext
    have hzZ : (z : A) ∈ Z := by
      rw [← hZ', Subgroup.mem_map]
      exact ⟨z, hz, rfl⟩
    have hyz : (y : A) * (z : A) = (z : A) * (y : A) :=
      (Subgroup.mem_centralizer_iff.1 (hZY y.2) (z : A) hzZ).symm
    rw [hρ]
    exact mul_inv_eq_iff_eq_mul.2 hyz
  have hcore := h ↥J hKJ' hJs h3 h9 h7 W hWp hWne Z' T' hfix
  have hcore' : (normalizer ((Z' : Subgroup ↥J) : Set ↥J)).map J.subtype ⊔
      (fixedBy W).map J.subtype ⊔ (T' : Subgroup ↥J).map J.subtype = J := by
    have h1 := congrArg (Subgroup.map J.subtype) hcore
    simpa only [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] using h1
  have hmap_norm : (normalizer ((Z' : Subgroup ↥J) : Set ↥J)).map J.subtype ≤
      J ⊓ normalizer (Z : Set A) := by
    refine le_inf (Subgroup.map_subtype_le (normalizer ((Z' : Subgroup ↥J) : Set ↥J))) ?_
    simpa [hZ'] using Subgroup.le_normalizer_map (H := (Z' : Subgroup ↥J)) J.subtype
  have hmap_fix : (fixedBy W).map J.subtype ≤ J ⊓ centralizer (Y : Set A) := by
    refine le_inf (Subgroup.map_subtype_le (fixedBy W)) ?_
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hw : ρ ⟨y, hy⟩ ∈ W := ⟨⟨y, hy⟩, rfl⟩
    have hfix' := (mem_fixedBy.1 hx') (ρ ⟨y, hy⟩) hw
    have hval : (y : A) * (x' : A) * (y : A)⁻¹ = (x' : A) := by
      have h := congrArg (Subtype.val) hfix'
      rw [hρ] at h
      exact h
    exact mul_inv_eq_iff_eq_mul.1 hval
  have hA : (normalizer ((Z' : Subgroup ↥J) : Set ↥J)).map J.subtype ≤
      (J ⊓ normalizer (Z : Set A)) ⊔ (J ⊓ centralizer (Y : Set A)) ⊔ T :=
    le_sup_of_le_left (le_sup_of_le_left hmap_norm)
  have hB : (fixedBy W).map J.subtype ≤
      (J ⊓ normalizer (Z : Set A)) ⊔ (J ⊓ centralizer (Y : Set A)) ⊔ T :=
    le_sup_of_le_left (le_sup_of_le_right hmap_fix)
  have hC : (T' : Subgroup ↥J).map J.subtype ≤
      (J ⊓ normalizer (Z : Set A)) ⊔ (J ⊓ centralizer (Y : Set A)) ⊔ T := by
    rw [hT']
    exact le_sup_of_le_right le_rfl
  calc J = (normalizer ((Z' : Subgroup ↥J) : Set ↥J)).map J.subtype ⊔
        (fixedBy W).map J.subtype ⊔ (T' : Subgroup ↥J).map J.subtype := hcore'.symm
    _ ≤ (J ⊓ normalizer (Z : Set A)) ⊔ (J ⊓ centralizer (Y : Set A)) ⊔ T :=
        sup_le (sup_le hA hB) hC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
