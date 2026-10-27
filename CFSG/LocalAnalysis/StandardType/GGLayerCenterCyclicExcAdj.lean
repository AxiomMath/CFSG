module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSz
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitE7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace LayerCycExc

theorem commutator_eq_top_of_simple {R : Type*} [Group R] (hs : IsSimpleGroup R)
    (hnab : ∃ a b : R, a * b ≠ b * a) : commutator R = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (commutator R) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hmem : ⁅a, b⁆ ∈ commutator R := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp hmem)
  · exact h

theorem dvd_or_of_largeEvenSplit_untwisted {p : ℕ} {lab : LargeEvenLabel}
    (hu : LargeEvenUntwisted lab.tag) (hs : LargeEvenSplit p lab) :
    p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  rcases hs with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | h
  · exact Or.inl h
  · exact absurd hu h
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at h hu
    rcases h with h | h <;> subst h <;> exact absurd hu id
  · exact Or.inr h

end LayerCycExc

section PSections

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem ggPSections_adjointGroup_G2
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (adjointGroup .G2 K) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.Steinberg.CentralExt.G2Four.g2_exists_section_of_coprime E η hη hker
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk))

theorem ggPSections_adjointGroup_F4
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (adjointGroup .F4 K) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.Steinberg.CentralExt.F4Two.f4_exists_section_of_coprime E η hη hker
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk))

theorem ggPSections_adjointGroup_E8
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (adjointGroup .E8 K) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨O⟩, -, -⟩ := CFSG.LieType.Steinberg.Adjoint.e8_conclusionB K
  obtain ⟨C, -, hC⟩ := CFSG.LieType.Steinberg.Adjoint.e8_commutatorFormula K O
  exact CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
    (CFSG.LieType.Steinberg.Adjoint.e8_isCTGroupDatum K)
    (CFSG.LieType.Steinberg.Adjoint.e8_steinbergExtras K)
    (CFSG.LieType.Steinberg.Adjoint.e8_chevalleyExtras K O C hC) E η hη hker
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk))

theorem ggPSections_adjointGroup_E7
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (adjointGroup .E7 K) := by
  intro E _ _ η hη hker hpk
  exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_adjointGroup_E7 K E η hη hker
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk)))

end PSections

theorem ggLayerCenterCyclic_of_mulEquiv_inn {p : ℕ} (hp : p.Prime) {R H : Type} [Group R]
    [Group H] [Finite H] (e : R ≃* H) {I : Set (MulAut R)} (hI : I ⊆ LargeEvenInnSet R)
    (hR : commutator R = ⊤) (hsec : GGPSections p H)
    (hmodel : ∀ h : H, GGModelLayerCyclic p (MulAut.conj h)) : GGLayerCenterCyclic p R I := by
  have hH : commutator H = ⊤ := by
    have : Group.IsPerfect R := ⟨hR⟩
    have : Group.IsPerfect H := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.commutator_eq_top
  refine ggLayerCenterCyclic_of_model hp e.symm.toMonoidHom e.symm.surjective (fun x hx => ?_) hH
    hsec fun φ hφ => ?_
  · have hx1 : x = 1 := e.symm.injective (by
      rw [map_one]
      exact MonoidHom.mem_ker.mp hx)
    rw [hx1]
    exact one_mem _
  · obtain ⟨r, rfl⟩ := hI hφ
    refine ⟨MulAut.conj (e r), fun h => ?_, hmodel (e r)⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.symm_apply_apply]

theorem ggLayerCenterCyclic_recipeChevalley_of_adj
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hT : TableB.torusSubgroup τ.cartan K = ⊤)
    (hR : commutator (TableBExc.RecipeGroup τ K) = ⊤) (hsec : GGPSections p (adjointGroup τ K))
    (hmodel : ∀ h : adjointGroup τ K, GGModelLayerCyclic p (MulAut.conj h)) :
    GGLayerCenterCyclic p (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
  have : Finite (adjointGroup τ K) := CFSG.LieType.Chevalley.generated_group_finite τ K
  exact ggLayerCenterCyclic_of_mulEquiv_inn hp (TableBExc.recipeEquiv τ K)
    (TableBExc.idImage_subset_inn_of_top τ K hT) hR hsec hmodel

@[expose] def GGExcAdjLayerCycInput (τ : Tag) (n₀ : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), n₀ ≤ n → Nat.card K = 2 ^ n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) →
      ∀ h : adjointGroup τ K, GGModelLayerCyclic p (MulAut.conj h)

theorem largeEvenLabelAll_layerCenterCyclic_adj
    (hG2 : GGExcAdjLayerCycInput .G2 2) (hF4 : GGExcAdjLayerCycInput .F4 1)
    (hE7 : GGExcAdjLayerCycInput .E7 1) (hE8 : GGExcAdjLayerCycInput .E8 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  have hu : LargeEvenUntwisted lab.tag := by
    rcases ht with h | h | h | h <;> rw [h] <;> exact trivial
  have hsplit := LayerCycExc.dvd_or_of_largeEvenSplit_untwisted hu hs
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at ht hsplit hn hl
  intro Q hQ
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨-, hn2⟩ := hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun hsimple hnab => ?_⟩
    have := LayerCC.charP_two_of_natCard hK
    exact ggLayerCenterCyclic_recipeChevalley_of_adj (τ := .G2) hp
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
      (LayerCycExc.commutator_eq_top_of_simple hsimple hnab) (ggPSections_adjointGroup_G2 hp hp2)
      (hG2 K n hn2 hK p hp hp2 hsplit)
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun hsimple hnab => ?_⟩
    have := LayerCC.charP_two_of_natCard hK
    exact ggLayerCenterCyclic_recipeChevalley_of_adj (τ := .F4) hp
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩)
      (LayerCycExc.commutator_eq_top_of_simple hsimple hnab) (ggPSections_adjointGroup_F4 hp hp2)
      (hF4 K n hn hK p hp hp2 hsplit)
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun hsimple hnab => ?_⟩
    have := LayerCC.charP_two_of_natCard hK
    exact ggLayerCenterCyclic_recipeChevalley_of_adj (τ := .E7) hp
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE7_adj
        (TableB.exists_sq_eq_of_charTwo K))
      (LayerCycExc.commutator_eq_top_of_simple hsimple hnab) (ggPSections_adjointGroup_E7 hp hp2)
      (hE7 K n hn hK p hp hp2 hsplit)
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun hsimple hnab => ?_⟩
    have := LayerCC.charP_two_of_natCard hK
    exact ggLayerCenterCyclic_recipeChevalley_of_adj (τ := .E8) hp
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩)
      (LayerCycExc.commutator_eq_top_of_simple hsimple hnab) (ggPSections_adjointGroup_E8 hp hp2)
      (hE8 K n hn hK p hp hp2 hsplit)

end CFSG.StandardType

end
