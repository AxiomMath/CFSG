module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InJ
public import CFSG.Monster.VisQuot.SylowT
public import CFSG.Monster.VisQuot.OctMembers
public import CFSG.Monster.Existence.Simple
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMRankT
import CFSG.Monster.VisQuot.OctInter

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open Subgroup

theorem octMember_le_Tvis (j : Fin 6) :
    CFSG.Monster.VisQuot.octMember j ≤ CFSG.Monster.VisQuot.Tvis := by
  intro g hg
  obtain ⟨n, hn⟩ := CFSG.Monster.VisQuot.exists_PhiV_eq_inl hg
  exact CFSG.Monster.VisQuot.mem_Tvis_of_PhiV_eq_inl n hn

theorem isMaxElemAbelian_toMat_octMember (hFB : CFSG.Monster.VisQuot.FixBound) (j : Fin 6) :
    CFSG.Quasithin.IsMaxElemAbelian CFSG.Monster.VisQuot.Tmat
      (CFSG.Monster.VisQuot.toMat (CFSG.Monster.VisQuot.octMember j)) := by
  refine ⟨CFSG.Monster.VisQuot.toMat_mono (octMember_le_Tvis j), ?_, ?_⟩
  · exact CFSG.Monster.VisQuot.isElemAbelian_toMat_iff.2
      (CFSG.Monster.VisQuot.octMember_isElemAbelian j)
  · intro B hBT hB
    calc Nat.card B ≤ 2 ^ 15 :=
          card_le_two_pow_fifteen_of_le_Tmat hFB hBT hB
      _ ≤ Nat.card (CFSG.Monster.VisQuot.octMember j) :=
          CFSG.Monster.VisQuot.two_pow_le_card_octMember j
      _ = Nat.card (CFSG.Monster.VisQuot.toMat (CFSG.Monster.VisQuot.octMember j)) :=
          (CFSG.Monster.VisQuot.natCard_toMat _).symm

theorem card_iInf_toMat_octMember_le :
    Nat.card (⨅ j, CFSG.Monster.VisQuot.toMat (CFSG.Monster.VisQuot.octMember j) :
      Subgroup CFSG.Monster.Generated.Gmat) ≤ 4 := by
  rw [← CFSG.Monster.VisQuot.toMat_iInf (fun j => CFSG.Monster.VisQuot.octMember j),
    CFSG.Monster.VisQuot.natCard_toMat]
  exact CFSG.Monster.VisQuot.card_iInf_octMember_le

theorem exists_isSylowTwoOf_k105In_thompsonJ_Gmat
    (hFB : CFSG.Monster.VisQuot.FixBound)
    (hG : Nat.card CFSG.Monster.Generated.Gmat = CFSG.Open.monsterOrder)
    (hC : ∀ T : Subgroup CFSG.Monster.Generated.Gmat,
      CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ →
      T ≤ Subgroup.centralizer {CFSG.Monster.Existence.xGmat} →
      K105In (Subgroup.centralizer {CFSG.Monster.Existence.xGmat}) T) :
    ∃ T : Subgroup CFSG.Monster.Generated.Gmat,
      CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ ∧
      T ≤ Subgroup.centralizer {CFSG.Monster.Existence.xGmat} ∧
      K105In (Subgroup.normalizer
        (CFSG.Quasithin.thompsonJ T : Set CFSG.Monster.Generated.Gmat)) T := by
  have hT := CFSG.Monster.VisQuot.isSylowTwoOf_Tmat hG
  have hTz : CFSG.Monster.VisQuot.Tmat ≤
      Subgroup.centralizer {CFSG.Monster.Existence.xGmat} :=
    CFSG.Monster.VisQuot.toMat_le_centralizer CFSG.Monster.VisQuot.Tvis
  refine ⟨CFSG.Monster.VisQuot.Tmat, hT, hTz, ?_⟩
  refine k105In_normalizer_thompsonJ_of_iInf hT
    CFSG.Monster.VisQuot.xGmat_mem_Tmat ?_ ?_
    (hC CFSG.Monster.VisQuot.Tmat hT hTz)
    (fun j => CFSG.Monster.VisQuot.toMat (CFSG.Monster.VisQuot.octMember j))
    (fun j => isMaxElemAbelian_toMat_octMember hFB j) card_iInf_toMat_octMember_le
  · intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTz ht)
  · simpa [CFSG.Monster.Existence.orderOf_xGmat] using
      pow_orderOf_eq_one CFSG.Monster.Existence.xGmat

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
