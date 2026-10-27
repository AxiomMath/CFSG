module

public import CFSG.RankThree.PartTwo.Sec18.Item187Min
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

private theorem mem_invariantPiSubgroups_two {Y : Subgroup G} (hY : IsPGroup 2 Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y ∈ invariantPiSubgroups (⊤ : Subgroup G) A (piOf 2) :=
  ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two Y).mpr hY, hAY⟩

theorem isSylowOf_of_mem_scriptX (h186 : Item186H) (hH : Sec18H G A M H c)
    (h187 : Hyp187 A M H c) {X : Subgroup G} (hX : X ∈ scriptX A M H) :
    CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M)
  have hmax : Maximal (· ∈ invariantPiSubgroups (⊤ : Subgroup G) A (piOf 2)) S :=
    (h186 G A M H c hH h187).2.1.1
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  have hSX : S ≤ X := hX.2
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_sup_left.trans hX.1.2.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf hH)
  have hX3 : ¬ 3 ∣ Nat.card X := (isPiSubgroup_piCompl_iff Nat.prime_three X).mp hX.1.2.1
  have hA3 : IsPGroup 3 A := (isE27_of_mem_partTwoE hH.mem_partTwoE).isPGroup
  obtain ⟨T, hTS, hST, hAT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hX3 hAX hSX hS2 hAS
  have hTeq : T = S :=
    le_antisymm (hmax.2 (mem_invariantPiSubgroups_two hTS.2.1 hAT) hST) hST
  rw [hTeq] at hTS
  have hS' : IsPGroup 2 (S.subgroupOf X) := hS2.comap_subtype
  obtain ⟨Q, hSQ⟩ := IsPGroup.exists_le_sylow hS'
  have hPX : (Q : Subgroup X).map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 ((Q : Subgroup X).map X.subtype) := Q.isPGroup'.map X.subtype
  have hSP : S ≤ (Q : Subgroup X).map X.subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hSX).symm.le.trans (Subgroup.map_mono hSQ)
  exact ⟨Q, hTS.2.2 _ hPX hP2 hSP⟩

theorem pCoreOf_le_pCoreOf_of_mem_scriptX (h186 : Item186H) (hH : Sec18H G A M H c)
    (h187 : Hyp187 A M H c) {X : Subgroup G} (hX : X ∈ scriptX A M H) (hXM : X ≤ M) :
    CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X ∧
      CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M)
  have hmax : Maximal (· ∈ invariantPiSubgroups (⊤ : Subgroup G) A (piOf 2)) S :=
    (h186 G A M H c hH h187).2.1.1
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  have hSX : S ≤ X := hX.2
  have hSM : S ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_right
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf hH)
  have hAX : A ⊔ S ≤ Subgroup.normalizer (X : Set G) := hX.1.2.2
  have hAM : A ≤ M :=
    (isE27_of_mem_partTwoE hH.mem_partTwoE).le_gamma.trans
      (SetLike.coe_subset_coe.mp (mem_scriptM_iff.mp hH.mem_scriptM).2)
  have hMN : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hpM : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hOMS : CFSG.Open.pCoreOf 2 M ≤ S := by
    have hSN : S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := hSM.trans hMN
    have hAN : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := hAM.trans hMN
    have hsup : CFSG.Open.pCoreOf 2 M ⊔ S ≤ S :=
      hmax.2 (mem_invariantPiSubgroups_two (hpM.to_sup_of_normal_left' hS2 hSN)
        (le_normalizer_sup hAN hAS)) le_sup_right
    exact le_sup_left.trans hsup
  have hOXS : CFSG.Open.pCoreOf 2 X ≤ S := by
    have hpX : IsPGroup 2 (CFSG.Open.pCoreOf 2 X) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    have hSNX : S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
      hSX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    have hAX' : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
      (le_sup_left.trans hAX).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
    have hsup : CFSG.Open.pCoreOf 2 X ⊔ S ≤ S :=
      hmax.2 (mem_invariantPiSubgroups_two (hpX.to_sup_of_normal_left' hS2 hSNX)
        (le_normalizer_sup hAX' hAS)) le_sup_right
    exact le_sup_left.trans hsup
  refine ⟨?_, hOXS⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOMS.trans hSX)
    (hXM.trans hMN) hpM

theorem inf_centralizer_le_of_mem_scriptX (h186 : Item186H) (hH : Sec18H G A M H c)
    (h187 : Hyp187 A M H c) {X : Subgroup G} (hX : X ∈ scriptX A M H) (hXM : X ≤ M) :
    X ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨hMX, -⟩ := pCoreOf_le_pCoreOf_of_mem_scriptX h186 hH h187 hX hXM
  have hM2 : CFSG.Open.IsTwoLocal M := (mem_scriptM_iff.mp hH.mem_scriptM).1.1
  have hcharM : M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤
      CFSG.Open.pCoreOf 2 M :=
    hH.charTwoType M hM2
  have hcen : Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hMX)
  have hle : X ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤
      M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    le_inf (inf_le_left.trans hXM) (inf_le_right.trans hcen)
  exact hle.trans (hcharM.trans hMX)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
