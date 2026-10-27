module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenGen
import CFSG.LocalAnalysis.WeakClosure81.EightTwelveBridge
import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qv
import CFSG.Quasithin.Background.E3Gen
import CFSG.Quasithin.Background.RonanE111MemE1
import CFSG.Quasithin.Background.C126NatDMin
import CFSG.Holt.General.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.C1PackC126B
import CFSG.Quasithin.Background.C1PackNat
import CFSG.Quasithin.Background.C1PackSolvBasic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2TwoProofDefs
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.RonanE111Ind
import CFSG.Quasithin.Background.RonanE111Jsub
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S14117Coprime
import CFSG.Quasithin.EmptyFaithful.S14117Rank
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
import CFSG.Quasithin.Vol2.Ch11SecBTCIso
import CFSG.Quasithin.Vol2.Ch11StatementsE
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC
open CFSG.Quasithin (IsSylowIn conjSubgroup conjSubgroup_one rk card_eq_two_pow_of_isPGroup twoResidual)
open CFSG.Quasithin.E3 (wClos cClos sParam)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Thm111)
open CFSG.LocalAnalysis.WeakClosure81 (InFSq)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22tb_dich {V H S : Subgroup G} (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j : ℕ}
    (hF : InFSq j H) (hij : i + j < sParam hV) :
    H ≤ normalizer (wClos V i S : Set G) ∨ ⁅cClos V (i + j) S, twoResidual H⁆ = ⊥ := by
  by_cases hHN : H ≤ normalizer (wClos V i S : Set G)
  · exact Or.inl hHN
  right
  set J := H ⊓ centralizer (cClos V (i + j) S : Set G) with hJ
  have hSJ : S ≤ normalizer (J : Set G) :=
    CFSG.Quasithin.A1a.le_normalizer_inf (hS.le.trans Subgroup.le_normalizer)
      (CFSG.Quasithin.A1a.le_normalizer_centralizer
        (Subgroup.le_normalizer.trans (CFSG.Quasithin.E3.normalizer_le_normalizer_cClos (V := V) (i := i + j) S)))
  suffices hres : twoResidual H ≤ J by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hres.trans inf_le_right)
  by_cases hHM : H ≤ J ⊔ S
  · exact CFSG.Quasithin.RonanE111.twoResidual_le_of_le_sup_two hSJ hS.isPGroup hHM
  · exfalso
    obtain ⟨A, hA, -, K, hK, hKM⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isE_not_le_of_inF2 hV hS hF
      le_sup_right hHM (PartTwo.TwelveEighteen.exists_gammaSet_not_le_pCoreOf hS hHN)
    have hcomm := CFSG.Quasithin.E3.e3_19_comm hV hS hij hA hK
    apply hKM
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    rw [← CFSG.Quasithin.sup_twoResidual_eq hSK]
    refine sup_le (inf_le_left.trans le_sup_right) (le_sup_of_le_left (le_inf ?_ ?_))
    · exact (CFSG.Quasithin.twoResidual_le K).trans hK.1
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

theorem uc22p22tb_eq_mul {V H S : Subgroup G} (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j : ℕ}
    (hF : InFSq j H) (hij : i + j < sParam hV) :
    (H : Set G) = ((H ⊓ centralizer (cClos V (i + j) S : Set G) : Subgroup G) : Set G) *
      ((H ⊓ normalizer (wClos V i S : Set G) : Subgroup G) : Set G) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases uc22p22tb_dich hV hS hF hij with hN | hC
    · exact ⟨1, ⟨one_mem _, one_mem _⟩, x, ⟨hx, hN hx⟩, one_mul x⟩
    · rw [Subgroup.commutator_comm] at hC
      have hRC := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
      have hSN : S ≤ normalizer (twoResidual H : Set G) :=
        hS.le.trans (CFSG.Quasithin.le_normalizer_twoResidual H)
      have hx' : x ∈ ((twoResidual H ⊔ S : Subgroup G) : Set G) := by
        rw [sup_comm, CFSG.Quasithin.sup_twoResidual_eq hS]
        exact hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (twoResidual H) S hSN] at hx'
      obtain ⟨r, hr, s, hs, rfl⟩ := hx'
      exact ⟨r, ⟨CFSG.Quasithin.twoResidual_le H hr, hRC hr⟩, s,
        ⟨hS.le hs, CFSG.Quasithin.E3.normalizer_le_normalizer_wClos (V := V) (i := i) S (le_normalizer hs)⟩, rfl⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact H.mul_mem ha.1 hb.1

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
