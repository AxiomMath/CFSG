module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213TDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Ta
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213t_sp4 (D : Data G) (Ch : Choice2011 G) (h117 : R117W D)
    (hV : S22_V D Ch) (h8 : S21_8Sp4 D Ch) (h8P : S21_8P D Ch) (he : CFSG.Open.evenRank G = 3)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (hodd : Odd n) (hsp : IsSp4 (Bar2 L) n) : K2213 D c p L n := by
  have hLM : L ≤ D.M := uc22p22a_le_of_isSubnormal hL.1
  have hLV := uc22p2213t_not_le_centralizer D Ch h117 hV h1930 c hL (uc22p2213t_not_thin_sp4 hsp)
  have hO : ∀ x ∈ CFSG.pCore 2 ↥L, (x : G) ∈ centralizer (c.V : Set G) := fun x hx =>
    uc22p22f_pCoreOf_le_cent hV h1930 c (uc22p22r_pCoreOf_le_of_isSubnormal hL.1 ⟨x, hx, rfl⟩)
  obtain ⟨ψ, hψs, hψk, hψc⟩ := uc22p2213t_onto c.hVM hLM hO hL.2.2 hLV
  haveI : IsSimpleGroup (Bar2 L) :=
    uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inr (Or.inl rfl))) hsp
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← P22w.center_eq_bot_of_isSimpleGroup hL.2.2]
    exact hψk
  set e : Bar2 L ≃* ↥(mbarImage D.M c.V L) := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩
  obtain ⟨t, htT, ht⟩ := h8 h1930 c.toCtx21 L hL n hodd hsp
  have htM : t ∈ D.M := D.sylowM.le htT
  exact ⟨hL, Or.inr (Or.inl (h8P he h1930 c.toCtx21 L hL n hodd hsp p hp)),
    Or.inl ⟨CFSG.Blueprint.LieModel.of_mulEquiv e hsp, hodd, ⟨t, htM⟩, htT,
      uc22p2213t_diag hLM e hψc htM ht⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
