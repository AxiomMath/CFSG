module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaAssembly
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaCheckA6
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaCheckL3
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix MatrixGroups

theorem _root_.CFSG.Quasithin.IsTypeH2.exists_beta_of_quotient
    {G : Type} [Group G] [Finite G] {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {e : Fin 7 → G} (hD8 : ∀ r ∈ d8Rels, evalWord e r = 1)
    (hy : e 0 ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : orderOf (e 0) = 3) (hz : e 3 ≠ 1) :
    ∃ β ∈ CK (e 0), ∀ r ∈ a2Rels, evalWord (Function.update e 6 β) r = 1 := by
  obtain ⟨F, hF, hFf, hcard, ⟨ψ⟩⟩ := h.exists_psl2_of_centralizer_quotient hone hy hy3
  rcases hcard with h7 | h9
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    let ρ : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by norm_num) (by rw [h7])
    let e1 := CFSG.GorensteinWalter.psl2RingEquiv ρ
    obtain ⟨e2⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
    let e3 : SL(3, ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
      MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
    exact exists_beta_of_check hy3 betaCheck_L3 (((ψ.trans e1.symm).trans e2.symm).trans e3.symm)
      rfl hD8 hz
  · obtain ⟨e9⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        F h9
    exact exists_beta_of_check hy3 betaCheck_A6 (ψ.trans e9) rfl hD8 hz

end CFSG.Quasithin.Kleidman.ThreeLocal
