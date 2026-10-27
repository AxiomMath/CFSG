module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147UDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

open Subgroup

theorem lgConj_eq_of_isQuasisimple {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hq : CFSG.Open.IsQuasisimple ↥(lgConj L)) : lgConj L = L := by
  have hle : L ≤ lgConj L := by
    refine le_trans (le_of_eq ?_) (le_iSup (fun g : G => L.map (MulAut.conj g).toMonoidHom) 1)
    ext x
    simp
  have hX : CFSG.Open.IsComponentOf (lgConj L) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.step le_top ((uc22p22r_lgConj_normal L).subgroupOf ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤), hq⟩
  exact (CFSG.ComponentClassification.LocalComponents.eq_of_le L (lgConj L) hL hX hle).symm

theorem two_le_of_case147SpU {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (h : Case147SpU L n) :
    2 ≤ n := by
  rcases h with ⟨h1, -⟩ | hsu
  · omega
  · exact uc22p22a_two_le_of_isU3 hsu.2

theorem not_isL2_of_case147SpU {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) {n : ℕ} (h : Case147SpU L n) (m : ℕ) : ¬ IsL2 ↥L m := by
  have hY : SpU3Quot ↥L := by
    rcases h with ⟨-, -, hsp, -⟩ | hsu
    · obtain ⟨hs, hnab⟩ := uc22p22a_sp4_simple _ n hsp
      haveI := hs
      have heq := lgConj_eq_of_isQuasisimple hL (uc22p22a_isQuasisimple_of_simple hnab)
      have hsp' : IsSp4 (↥(lgConj L) ⧸ center ↥(lgConj L)) n :=
        CFSG.Blueprint.LieModel.of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq (uc22p22a_center_eq_bot hnab)).trans
            QuotientGroup.quotientBot).symm hsp
      rw [heq] at hsp'
      exact Or.inl ⟨n, hsp'⟩
    · have heq := lgConj_eq_of_isQuasisimple hL hsu.1
      have hU := hsu.2
      rw [heq] at hU
      exact Or.inr ⟨n, hU⟩
  exact uc22p21k_not_isL2 hL.2.2 hY m

theorem K147U.toK147 (h : K147U) : K147 := by
  intro G _ _ V _ _ _ ρ hK hO hf hi L hL n hc hm
  rcases case147_iff.1 hc with hSpU | hSzJ1 | hL2
  · exact absurd (h.1 G V ρ hK hO hf hi L hL n (two_le_of_case147SpU hSpU) hSpU hm)
      (not_isL2_of_case147SpU hL hSpU n)
  · exact absurd hm (Nat.not_le.2 (h.2.1 G V ρ hf hi L hL n hSzJ1))
  · exact h.2.2 G V ρ hK hO hf hi L hL n hL2 hm

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
