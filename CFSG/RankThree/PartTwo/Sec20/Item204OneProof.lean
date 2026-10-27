module

import CFSG.RankThree.PartTwo.Late.Item2010
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_mem_maxInvariant {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) {i : Fin 4}
    (hNi : Subgroup.normalizer
      (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) i : Set G) ≤ M) :
    CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ∈
      maxInvariantPiSubgroups ⊤ (kTwenty M c ⊔ T) (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hXM : K ⊔ T ≤ M := sup_le hKM hT.sylow.le
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXR : K ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hmem : R ∈ invariantPiSubgroups ⊤ (K ⊔ T) (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hR2, hXR⟩
  refine mem_maxInvariantPiSubgroups_iff.mpr ⟨hmem, fun Y hY hRY => ?_⟩
  obtain ⟨-, hY2, hXY⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hY
  by_contra hne
  obtain ⟨y, hyY, hyR, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hY2
    (lt_of_le_of_ne hRY (Ne.symm hne))
  have hyM : y ∈ M := hNi (normalizer_le_normalizer_fourChar R i hyN)
  have hYM2 : IsPGroup 2 (Y ⊓ M : Subgroup G) := hY2.to_le inf_le_left
  have hXYM : K ⊔ T ≤ Subgroup.normalizer ((Y ⊓ M : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf_of_mem (hXY hx) (Subgroup.le_normalizer (hXM hx))
  set X' := (Y ⊓ M) ⊔ (K ⊔ T) with hX'
  have hX'M : X' ≤ M := sup_le inf_le_right hXM
  have hTX' : CFSG.ABGLocalTools.IsSylowOf 2 T X' :=
    hT.sylow.of_le (le_sup_right.trans le_sup_right) hX'M
  have hYMT : Y ⊓ M ≤ T :=
    le_of_isSylowOf_of_normal hYM2 le_sup_left le_rfl
      (sup_le Subgroup.le_normalizer hXYM) hTX'
  have hYMR : Y ⊓ M ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYMT.trans le_sup_right) hXYM hYM2
  exact hyR (hYMR ⟨hyY, hyM⟩)

omit [Finite G] in
theorem not_case_two {A P : Subgroup G} {c : G} (hcA : c ∈ A)
    (hconj : Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c}) (hAP : A ≤ P)
    (h9 : (Sec13.orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)).ncard = 9) :
    False := by
  have hsub : Sec13.orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) ⊆
      {Subgroup.zpowers c} := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hconj]
    refine ⟨⟨w, rfl⟩, ?_⟩
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hAP ((Subgroup.mem_normalizer_iff.mp hw c).mp hcA)
  have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [h9, Set.ncard_singleton] at this
  omega

end CFSG.RankThree.PartTwo.Sec20
