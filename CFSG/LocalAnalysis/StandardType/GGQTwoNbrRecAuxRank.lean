module

public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G]

variable [Finite G]

theorem qTwoNbrRec_rank_ne_six
    {B Bs L D J : Subgroup G} {x : G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {d : ℕ} (hd : 5 ≤ d) (hd6 : d ≠ 6)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ 1) ^ 2) (hperf : commutator ↥K = ⊤)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ 1))) :
    3 ^ (d / 3 + 2) ≤ Nat.card (ggGamma K hN).range := by
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    rintro h'
    have hd3 : d = 3 := congrArg Prod.fst h'
    omega
  have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ 1))) :=
    ggTorusLift_unitary (K := F) (n := 1) (d := d) (p := 3) hF le_rfl (by omega) hdq
      Nat.prime_three (by norm_num)
  have h1 := pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnbr hperf θ hN hlift
  have hle : d / 3 + 2 ≤ ggUnitaryTorusRank 3 d := by
    unfold ggUnitaryTorusRank
    split_ifs with h3
    · obtain ⟨k, rfl⟩ := h3
      omega
    · omega
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 3) hle).trans h1

theorem qTwoNbrRec_rank_six
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = (⟨.twA, 6 - 1, 1⟩ : LargeEvenLabel)) 3 Bs K) :
    3 ^ (6 / 3 + 2) ≤ Nat.card (ggGamma K hN).range := by
  have hM : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K :=
    GGInnerDiagOnLabel.mono_label
      (S := fun _ lab' => lab' = (⟨.twA, 6 - 1, 1⟩ : LargeEvenLabel))
      (T := GGNbrInner937U63Label) (p := 3)
      (fun lab hlab => by
        rw [hlab]
        exact ⟨⟨rfl, by norm_num, by norm_num, by norm_num⟩, rfl, rfl⟩) hmark
  have h4 : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    (ggUnitDvd63NbrRankInput_holds hLB hPJ) G 3 B Bs x L D J hcfg y K hnbr hN hM
  rwa [show 6 / 3 + 2 = 4 by norm_num]

theorem qTwoNbrRec_frame {Bs K : Subgroup G} {F : Type} [Field F] [Finite F] {d : ℕ}
    (h : UnitaryFieldData 2 1 F) (hd : 5 ≤ d) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 1 F d))
    (hperf : commutator ↥K = ⊤) (hBs : IsElemAbelian 3 Bs)
    (hind : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
        (LargeEvenGUSet (Fin d) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hrank : 3 ^ (d / 3 + 2) ≤ Nat.card (ggGamma K hN).range) :
    ∃ P ∈ primeFormUnitary h (idGram F d), ∀ a ∈ (ggBeta K θ hN).range,
      ∃ (M : GL (Fin d) F) (hM : M ∈ LargeEvenGUSet (Fin d) F (2 ^ 1)),
        ((P⁻¹ * M * P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).IsDiag ∧
          a = TableB.projConj (unitarySU 2 1 F d) ⟨M, TableBUE.gu_subset_normalizer h hM⟩ := by
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by
    rw [h.card]
    norm_num
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    rintro h'
    have hd3 : d = 3 := congrArg Prod.fst h'
    omega
  have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
    simpa using hBs.subgroupOf Bs
  have hAb : IsElemAbelian 3 (ggBeta K θ hN).range := by
    have hh := htop.map (ggBeta K θ hN)
    rwa [← MonoidHom.range_eq_map] at hh
  have hAbI : ∀ a ∈ (ggBeta K θ hN).range,
      a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
        (LargeEvenGUSet (Fin d) F (2 ^ 1)) := by
    rintro a ⟨b, rfl⟩
    exact ggBeta_mem K θ hN hind b
  have hcard : 3 ^ (d / 3 + 2) ≤ Nat.card (ggBeta K θ hN).range := by
    have hcomp := QTwoCav.markingAutHom_comp_gamma θ hN
    have hinj := QTwoCav.markingAutHom_injective θ hperf
    have hcards : Nat.card (ggBeta K θ hN).range = Nat.card (ggGamma K hN).range := by
      rw [← hcomp, MonoidHom.range_comp, Subgroup.card_map_of_injective hinj]
    rw [hcards]
    exact hrank
  exact TableBUD.exists_unitary_frame h hK (by omega) hdq Nat.prime_three (by norm_num)
    hAb hAbI hcard

end CFSG.StandardType.QTwo

end
