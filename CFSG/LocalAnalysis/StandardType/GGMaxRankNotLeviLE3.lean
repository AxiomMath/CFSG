module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankSide
public import CFSG.LocalAnalysis.StandardType.GGMaxRankNotLevi
public import CFSG.LocalAnalysis.StandardType.GGMaxRankLeviIndep
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggMaxRank_notLeviLE3 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X Y J : Subgroup G} (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs))
    (hX : GGMaxRankSideChain p Bs X J eJ) : ¬ GGResLeviSideDatumLE3 p Bs Y J := by
  classical
  rintro ⟨Λ, instFL, instDL, S, M, C, MJ, V', instAC', instM', ι', φ', h', α',
    hS2, hS3, hM, hC, hMJ, hMJe, hlin', hrefl', hpair', hfY, hAY, hfJ, hAJgen, hconj⟩
  letI : Fintype Λ := instFL
  letI : DecidableEq Λ := instDL
  letI : AddCommGroup V' := instAC'
  letI : Module (ZMod p) V' := instM'
  exact ggMaxRank_levi_false (ΛJ := {j : Λ // j ∉ S}) (MJ := MJ) eJ hX hMJ ι'
    (fun j => φ' j) (fun j => h' j) (fun j => α' j)
    (fun i w => hlin' i w) (fun i => hrefl' i) hfJ hAJgen hconj
    (fun hcardJ => by
      have h1 : Fintype.card {j : Λ // j ∉ S} = Fintype.card Λ - S.card := by
        rw [Fintype.card_subtype_compl (fun j : Λ => j ∈ S), Fintype.card_coe]
      have hcard : Fintype.card Λ = 8 + S.card := by
        have hle : S.card ≤ Fintype.card Λ := Finset.card_le_univ S
        rw [← hcardJ, h1, Nat.sub_add_cancel hle]
      have hcardL : Fintype.card Λ = 10 ∨ Fintype.card Λ = 11 := by omega
      by_cases hA : Fintype.card Λ = 11 ∧ GGIsTypeA M
      · have hcard11 : Fintype.card Λ = 11 := hA.1
        have hScard : S.card = 3 := by omega
        have hconn : GGDeletedConnectedS M S := by
          intro i j
          exact Relation.ReflTransGen.mono
            (fun u v huv => ⟨huv.1, by rw [← hMJe u v]; exact huv.2⟩) i j
            (ggRC_weyl_connected hMJ i j)
        exact ggMaxRank_A11_indep hX.1 hcard11 hA.2 hC h' α' hpair' S hScard hconn
      · have hindall : LinearIndependent (ZMod p) h' :=
          ggMaxRank_big_indep hX.1 hcardL hM hC hA h' α' hpair'
        simpa only [Function.comp_def] using
          hindall.comp (Subtype.val : {j : Λ // j ∉ S} → Λ) (fun _ _ hh => Subtype.ext hh))

end CFSG.StandardType

end
