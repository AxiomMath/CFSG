module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.Holt.General.DLineTools
import CFSG.Milestones.ASVolI.A3Aut.SBSp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22p2214_bor_sylow {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) : ∃ Q : Sylow 2 X, (Q : Subgroup X) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  rw [Subgroup.relIndex_top_right] at hidx
  exact ⟨hp.toSylow hidx, rfl⟩

theorem uc22p2214_bor_bender_L2 {X : Type} [Group X] {n : ℕ} (hX : IsL2 X n) : fusionIsBenderGroup X :=
  CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isPSL
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))

theorem uc22p2214_bor_bender_Sz {X : Type} [Group X] {n : ℕ} (hX : IsSz X n) : fusionIsBenderGroup X := by
  obtain ⟨a, ha, -, he⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hX
  exact Or.inr (Or.inr ⟨a, ha, he⟩)

theorem uc22p2214_bor_bender_U3 {X : Type} [Group X] {n : ℕ} (hX : IsU3 X n) : fusionIsBenderGroup X :=
  Or.inr (Or.inl ⟨n, CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hX,
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_psu3_of_lieModel_PSU3 hX⟩)

theorem uc22p2214_bor_not_isSolvable {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X) :
    ¬ Group.IsSolvable X := by
  intro hsolv
  haveI : IsSimpleGroup X := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨f, k, hf, hBor⟩ := CFSG.Holt.General.exists_fusionBenderBorel_two_pow_of_fusionIsBenderGroup hB
  have h4f : 4 ∣ 2 ^ f := by
    have h := Nat.pow_dvd_pow 2 hf
    norm_num at h
    exact h
  obtain ⟨E, -, hE⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_four_of_fusionBenderBorel hBor h4f
  have h4 : 4 ∣ Nat.card X := hE ▸ Subgroup.card_subgroup_dvd_card E
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_four_dvd_card h4
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem uc22p2214_bor_ne_top_of_bender {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X)
    {Y : Subgroup X} (hY : Group.IsSolvable ↥Y) : Y ≠ ⊤ := by
  rintro rfl
  exact uc22p2214_bor_not_isSolvable hB
    (solvable_of_surjective (f := (⊤ : Subgroup X).subtype) (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩))

theorem uc22p2214_bor_solvBorel_of_bender {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X)
    {S : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {Y : Subgroup X} (hSY : S ≤ Y)
    (hY : Group.IsSolvable ↥Y) : Y ≤ normalizer (S : Set X) := by
  haveI : IsSimpleGroup X := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨Q, rfl⟩ := uc22p2214_bor_sylow hS
  exact CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB Q hSY (uc22p2214_bor_ne_top_of_bender hB hY)

theorem uc22p2214_bor_sp4_model {X : Type} [Group X] {n : ℕ} (hX : IsSp4 X n) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 n ∧ 2 ≤ n := by
  have hcl := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  refine ⟨hcl, ?_⟩
  obtain ⟨⟨-, hn1, -, h22⟩, -⟩ := hcl
  by_contra hlt
  obtain rfl : n = 1 := by omega
  exact h22 (by simp)

theorem uc22p2214_solvBorel_L2 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsL2 X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {Y : Subgroup X} (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) :
    Y ≤ normalizer (S : Set X) :=
  uc22p2214_bor_solvBorel_of_bender (uc22p2214_bor_bender_L2 hX) hS hSY hY

theorem uc22p2214_solvBorel_Sz {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSz X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {Y : Subgroup X} (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) :
    Y ≤ normalizer (S : Set X) :=
  uc22p2214_bor_solvBorel_of_bender (uc22p2214_bor_bender_Sz hX) hS hSY hY

theorem uc22p2214_solvBorel_Sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSp4 X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {Y : Subgroup X} (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) :
    Y ≤ normalizer (S : Set X) := by
  obtain ⟨hcl, hn⟩ := uc22p2214_bor_sp4_model hX
  exact CFSG.ASVolI.burnsideAut_solvBorel_Sp4 X n hn hcl S
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hS) Y hSY hY

theorem uc22p2214_solvBorel_U3 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3 X n) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) {Y : Subgroup X} (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) :
    Y ≤ normalizer (S : Set X) :=
  uc22p2214_bor_solvBorel_of_bender (uc22p2214_bor_bender_U3 hX) hS hSY hY

end CFSG.LocalAnalysis.UniquenessCase.UC22
