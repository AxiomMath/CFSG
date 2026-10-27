module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
public import CFSG.RankThree.PartOne.S15K.FamilyForms
public import CFSG.LocalAnalysis.StandardType.FS81.OrthParity
public import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.StandardType.FS81.D6NormAux
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8D4Rank
public import CFSG.LocalAnalysis.GLTheoremA.S4.L49b
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
public import CFSG.LieType.SeitzGeneration.OrthSdLines
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.RankThree.PartOne.FOC.CompCommutator

public section

namespace CFSG.StandardType.FrameRoute.FS81

open Module QuadraticMap CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
  CFSG.LieType.SeitzGeneration.OrthBlk CFSG.LieType.Universal.Spin
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

theorem eq_one_of_mem_framePlane {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hdim : finrank (ZMod 2) V = 2 * r) (hU : ∀ i, finrank (ZMod 2) (F.U i) = 2)
    (i : Fin r) {v : V} (hv : v ∈ F.U i) (hv0 : v ≠ 0) : Q v = 1 := by
  have htop : (⨆ k, F.U k) = ⊤ := F.iSup_pieces_eq_top hdim hU
  exact (F.exists_rot_pair hAO htop i (hU i) hv hv0).1.qa

theorem isPlusType_restrict_perpOf_framePlane {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (F : SevOm.Frame Q 3 A r) (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hdim : finrank (ZMod 2) V = 2 * r) (hU : ∀ i, finrank (ZMod 2) (F.U i) = 2)
    (i : Fin r) (hr : 2 ≤ r) (hQminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict (perpOf Q (F.U i))) := by
  have hnd : PolarNondegOn Q (F.U i) := fun v hv hvw =>
    F.nondeg i v hv fun w hw => by rw [polar_comm]; exact hvw w hw
  have hUa : ∀ v ∈ F.U i, Q v = 0 → v = 0 := by
    intro v hv hQv
    by_contra hv0
    have h1 := eq_one_of_mem_framePlane F hAO hdim hU i hv hv0
    rw [h1] at hQv
    exact one_ne_zero hQv
  have hWm : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (F.U i).subtype) :=
    CFSG.RankThree.PartOne.S15K.not_isPlusType_of_aniso_plane (hU i) hUa
  have hWnd : (polarBilin (Q.comp (F.U i).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.S15K.polarBilin_comp_subtype_nondegenerate hnd
  have hplusComp : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (perpOf Q (F.U i)).subtype) :=
    (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.isPlusType_comp_polarPerp_iff hQ
      (by rw [hdim]) hr hWnd (hU i) hWm).mpr hQminus
  obtain ⟨W, hW, hWs⟩ := hplusComp
  exact ⟨W, hW, fun v hv => by
    simpa [QuadraticMap.restrict_apply, QuadraticMap.comp_apply] using hWs v hv⟩

theorem exists_map_ne_zero_of_polar_ne_zero {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {W : Submodule (ZMod 2) V}
    (hW : PolarNondegOn Q W) {T : Submodule (ZMod 2) W} (hT : finrank (ZMod 2) T = 3)
    (hTs : ∀ x ∈ T, Q (x : V) = 0) : ∃ v : W, Q (v : V) ≠ 0 := by
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hT
    omega
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
  obtain ⟨v, hvW, hvt⟩ := hW.exists_polar_ne_zero (t : W).2 (fun h => ht0 (Subtype.ext h))
  by_cases hv : Q v = 0
  · refine ⟨⟨(t : V) + v, W.add_mem t.2 hvW⟩, ?_⟩
    have h1 : Q ((t : V) + v) = polar Q (t : V) v := by
      rw [QuadraticMap.map_add Q (t : V) v, hTs t htT, hv, zero_add, zero_add]
    exact h1.trans_ne hvt
  · exact ⟨⟨v, hvW⟩, hv⟩

theorem exists_nineJ_restrict_plus {G : Type} [Group G] [Finite G]
    {K E : Subgroup G} {B : Basis3 G (5 + 1)} {φ : ↥K ≃* ↥(orthDerived Q5)}
    {F : SevOm.Frame Q5 3 (Subgroup.map ((orthDerived Q5).subtype.comp φ.toMonoidHom)
      ((E ⊓ K).subgroupOf K)) 5} {j : Fin 5 → Fin 5}
    (hAO : Subgroup.map ((orthDerived Q5).subtype.comp φ.toMonoidHom)
      ((E ⊓ K).subgroupOf K) ≤ TauCeti.QuadraticMap.orthogonalGroup Q5)
    (hU : ∀ i, finrank (ZMod 2) (F.U i) = 2)
    (haK : B.b 2 ∈ K)
    (hx3 : ((φ ⟨B.b 2, haK⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) ^ 3 = 1)
    (hxU : ∀ u ∈ F.U (j 1),
      ((φ ⟨B.b 2, haK⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) u ∈ F.U (j 1))
    (hxfix : ∀ v, ((φ ⟨B.b 2, haK⟩ : ↥(orthDerived Q5)) :
      V5 ≃ₗ[ZMod 2] V5) v = v ↔ v ∈ perpOf Q5 (F.U (j 1))) :
    ∃ (U : Submodule (ZMod 2) V5)
      (_Ψ : ↥(nineJ K (B.b 2)) ≃* ↥(orthDerived (Q5.restrict (perpOf Q5 U)))),
      finrank (ZMod 2) U = 2 ∧
      (polarBilin (Q5.restrict (perpOf Q5 U))).Nondegenerate ∧
      finrank (ZMod 2) (perpOf Q5 U) = 8 ∧
      CFSG.GroupTheory.WeirSylow.IsPlusType (Q5.restrict (perpOf Q5 U)) ∧
      (∃ T : Submodule (ZMod 2) (perpOf Q5 U), finrank (ZMod 2) T = 3 ∧
        ∀ v ∈ T, (Q5.restrict (perpOf Q5 U)) v = 0) := by
  classical
  let U : Submodule (ZMod 2) V5 := F.U (j 1)
  have hU' : PolarNondegOn Q5 U := fun u hu huv => F.nondeg (j 1) u hu fun v hv => by
    rw [polar_comm]; exact huv v hv
  have hU2 : finrank (ZMod 2) U = 2 := hU (j 1)
  have hUc : IsCompl U (perpOf Q5 U) := isCompl_perp hU'
  have hdimV : finrank (ZMod 2) V5 = 10 := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  have hdimW : finrank (ZMod 2) (perpOf Q5 U) = 8 := by
    have := Submodule.finrank_add_eq_of_isCompl hUc
    rw [hU2, hdimV] at this
    omega
  have hP : (polarBilin (Q5.restrict (perpOf Q5 U))).Nondegenerate :=
    perp_polarBilin_nondegenerate nondegenerate_Q5 hU'
  have hT : ∃ T : Submodule (ZMod 2) (perpOf Q5 U), finrank (ZMod 2) T = 3 ∧
      ∀ v ∈ T, (Q5.restrict (perpOf Q5 U)) v = 0 :=
    perp_exists_ts_three nondegenerate_Q5 hU' (by rw [hdimW])
  have h6 : 6 ≤ finrank (ZMod 2) (perpOf Q5 U) := by omega
  have hJleK : nineJ K (B.b 2) ≤ K := (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨Ψ, -⟩ := nineJ_equiv_restrict φ haK hJleK hU' hU2 hT h6 hx3 hxU hxfix
  have hQminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q5 :=
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 5) (by norm_num)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
  have hWplus := isPlusType_restrict_perpOf_framePlane (Q := Q5) nondegenerate_Q5 F hAO
    (by rw [hdimV]) hU (j 1) (by norm_num) hQminus
  exact ⟨U, Ψ, hU2, hP, hdimW, hWplus, hT⟩

end CFSG.StandardType.FrameRoute.FS81

end
