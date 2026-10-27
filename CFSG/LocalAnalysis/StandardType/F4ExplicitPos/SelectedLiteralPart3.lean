module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2SelectedPair
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.SelectedLiteral
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.SeitzReduction.F4Pilot
open CFSG.StandardType.LieCore
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.F4ExplicitPos.LiteralSetup
open CFSG.StandardType.F4ExplicitPos.ActualSetup
open CFSG.StandardType.F4ExplicitPos.ComponentAttach
open CFSG.StandardType.F4ExplicitPos.BaseChange
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType.F4ExplicitPos.A2Actual
open CFSG.StandardType.F4ExplicitPos.SelectedPair
open CFSG.StandardType.F4ExplicitPos.OddKernelActual
open CFSG.StandardType.F4ExplicitPos.RationalC3
open scoped Matrix MatrixGroups

theorem f4_literal_selected_pair
    {X : Type} [Group X] [Finite X]
    {n f p : ℕ} {ψ : (ggU .F4 n f).K →* X}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) :
    let FD := F4PosData.ofHyp hH
    ∃ (w : WeylGroup .F4) (g0 : ModGL .F4 (F4Omega f))
      (hg0C : g0 ∈ adjointGroup .F4 (F4Omega f))
      (hg0 : ((frobF4 (K := GaloisField 2 f) (L := F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
        (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) ⟨g0, hg0C⟩ :
        adjointGroup .F4 (F4Omega f)) : ModGL .F4 (F4Omega f)) =
        g0 * canonicalRep (coxeterSystem .F4) (F4Omega f) w),
      let Δ := langDatumF4 (K := GaloisField 2 f) (L :=
          F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
        (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0
      FrobRootMap Δ (MulAction.toPerm w) ∧ Finite Δ.model ∧
      (∀ a ∈ thetaGLimage (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner D FD.hDB,
        g0⁻¹ * a * g0 ∈ Δ.torus) ∧
      (∀ b : B₁, Δ.step (ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0 b) =
        ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0 b) ∧
      (ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
          (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0).ker =
        (Subgroup.centralizer (G₀ : Set X)).subgroupOf B₁ ∧
      ∃ (d : X) (hdD : d ∈ D) (coord : D → Fin Tag.F4.rank → (F4Omega f)ˣ),
        d ≠ 1 ∧ d ∉ Subgroup.centralizer (L : Set X) ∧
        Subgroup.closure ({x, d} : Set X) = D ∧
        (∀ d0 : D, ThetaF4 (L := F4Omega f) ψ G₀ B₁ FD.hG0 FD.hker
            (center_adjointGroup_F4_galoisField f) FD.hBN FD.hinner g0
            (Subgroup.inclusion FD.hDB d0) = rootDiagUnit .F4 (coord d0)) ∧
        (∀ (d0 : D) (i : Fin Tag.F4.rank), (coord d0 i) ^ p = 1) ∧
        coord ⟨d, hdD⟩ ≠ 1 ∧
        CFSG.Assembly.IsComponentOf ((J.subgroupOf G₀).map
            (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
              (center_adjointGroup_F4_galoisField f) g0))
          (Δ.Γ ⊓ Subgroup.centralizer
            ({rootDiagUnit .F4 (coord ⟨x, FD.h17⟩), rootDiagUnit .F4 (coord ⟨d, hdD⟩)} :
              Set (ModGL .F4 (F4Omega f)))) ∧
        ∃ i : KernelComponent (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)),
          ((J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
              (center_adjointGroup_F4_galoisField f) g0)) ≤
            rootSpan .F4 (F4Omega f)
              (componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) i) ∧
          CFSG.StandardType.F4ExplicitPos.SelectedPair.SelectedPairOutput
            (k := GaloisField 2 f) Δ
            (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩))
            ((J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
              (center_adjointGroup_F4_galoisField f) g0)) i := by
  set FD := F4PosData.ofHyp hH with hFD
  obtain ⟨w, g0, hg0C, hg0, hFrob, hFin, htor, hstep, hTheker, d, hdD, coord,
    hd1, hdCL, hgen, hcoord, hexp, hcd, hattach, hsel⟩ := f4_literal_setup hH
  have h28 : IsEmpty (↥J ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
    exact h28
  let : Algebra (ZMod 2) (F4Omega f) := ZMod.algebra (F4Omega f) 2
  let : Algebra.IsAlgebraic (ZMod 2) (F4Omega f) :=
    CFSG.LieType.Chevalley.algebraicClosure_isAlgebraic_zmod 2 (GaloisField 2 f)
  set Δ : LangDatum Tag.F4 (F4Omega f) :=
    langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
      (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0 with hΔ
  set Jbar : Subgroup (ModGL Tag.F4 (F4Omega f)) :=
    (J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
      (center_adjointGroup_F4_galoisField f) g0) with hJbar
  set Ccent : Subgroup (ModGL Tag.F4 (F4Omega f)) :=
    Subgroup.centralizer
      ({rootDiagUnit .F4 (coord ⟨x, FD.h17⟩), rootDiagUnit .F4 (coord ⟨d, hdD⟩)} :
        Set (ModGL .F4 (F4Omega f))) with hCcent
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := card_galoisField_two f FD.hf
  have hq : Δ.q = 2 ^ f := by
    have h := langDatumF4_q (K := GaloisField 2 f) (L := F4Omega f)
      (iterateFrobenius (F4Omega f) 2 f)
      (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0
    exact h.trans hk
  have hFr_inj : Function.Injective (iterateFrobenius (F4Omega f) 2 f) :=
    fun a b hab => iterateFrobenius_inj (F4Omega f) 2 f hab
  have hstep_inj : Function.Injective Δ.step :=
    langDatumF4_step_injective (K := GaloisField 2 f) (L := F4Omega f)
      (iterateFrobenius (F4Omega f) 2 f)
      (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) hFr_inj w hg0C hg0
  have hTorX : rootDiagUnit .F4 (coord ⟨x, FD.h17⟩) ∈ Δ.torus := by
    apply rootDiagUnit_mem_torus_of_step_fixed Δ
    rw [← hcoord ⟨x, FD.h17⟩]
    exact hstep (Subgroup.inclusion FD.hDB ⟨x, FD.h17⟩)
  have hTorD : rootDiagUnit .F4 (coord ⟨d, hdD⟩) ∈ Δ.torus := by
    apply rootDiagUnit_mem_torus_of_step_fixed Δ
    rw [← hcoord ⟨d, hdD⟩]
    exact hstep (Subgroup.inclusion FD.hDB ⟨d, hdD⟩)
  have hpOdd : Odd p := FD.hp.odd_of_ne_two FD.hp2
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp hpOdd
  have hpa : ∀ i, coord ⟨x, FD.h17⟩ i ^ p = 1 := fun i => hexp ⟨x, FD.h17⟩ i
  have hpd : ∀ i, coord ⟨d, hdD⟩ i ^ p = 1 := fun i => hexp ⟨d, hdD⟩ i
  have hne : rootDiagUnit .F4 (coord ⟨x, FD.h17⟩) ≠ 1 ∨
      rootDiagUnit .F4 (coord ⟨d, hdD⟩) ≠ 1 := by
    right
    intro h1
    exact hcd (CFSG.LieType.Chevalley.rootDiagUnit_injective
      (h1.trans rootDiagUnit_one.symm))
  have hker : ∀ α ∈ kernelRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)),
      (MulAction.toPerm w) α ∈
        kernelRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) :=
    joint_kernel_root_stable Δ (MulAction.toPerm w) hFrob
      (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩) hTorX hTorD
  have hP : CFSG.Assembly.IsComponentOf Jbar (Δ.Γ ⊓ Ccent) := by
    rw [hJbar, hCcent, hΔ]
    exact hattach
  have hout : ∃ i : KernelComponent (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)),
      Jbar ≤ rootSpan .F4 (F4Omega f)
        (componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) i) ∧
      SelectedPairOutput (k := GaloisField 2 f) Δ
        (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) Jbar i := by
    obtain ⟨iJ, hleOrbit⟩ := hsel
    have hCcentLe : rootSpan .F4 (F4Omega f)
        (componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ) ≤ Ccent := by
      rw [hCcent]
      exact rootSpan_componentRoots_le_centralizer_pair
        (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩))
        (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)
        (CFSG.StandardType.F4ExplicitPos.JointShapes.kernelRoots_jointChar
          (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ
    have hstable : ((MulAction.toPerm w) : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ =
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ :=
      joint_componentRoots_image_eq_of_coord Δ (MulAction.toPerm w) hFrob
        (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩) hTorX hTorD hpOdd hpa hpd iJ
    have hle : Jbar ≤ rootSpan .F4 (F4Omega f)
        (componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ) := by
      have h := hleOrbit
      rw [f4_joint_ratOrbit_eq_of_coord (D := Δ) (ρ := MulAction.toPerm w) hFrob
        (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩) hTorX hTorD hpOdd hpa hpd iJ] at h
      rw [hJbar] at h
      exact h
    have hA1 : ∀ (v : WeylGroup Tag.F4) (j : Fin Tag.F4.rank),
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ =
          (fun α => v • α) '' ({Pi.single j 1, -Pi.single j 1} :
            Set (Fin Tag.F4.rank → ℤ)) →
        SelectedPairOutput (k := GaloisField 2 f) Δ
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) Jbar iJ := by
      intro v j hΨ
      exact a1_selected_pair_output_of_shape (Ω := F4Omega f) (k := GaloisField 2 f)
        (f := f) FD.hf Δ hq hk iJ Jbar (MulAction.toPerm w) hFrob hker hstable v j hΨ
        hCcentLe hP hle
    have hLongA2 : ∀ v : WeylGroup Tag.F4,
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ =
          (fun α => v • α) '' parabolicRoots Tag.F4 f4LongSupport →
        SelectedPairOutput (k := GaloisField 2 f) Δ
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) Jbar iJ := by
      intro v hΨ
      exact a2_long_selected_pair_output_of_shape (Ω := F4Omega f) (k := GaloisField 2 f)
        (f := f) FD.hf hk Δ hq hstep_inj iJ Jbar (MulAction.toPerm w) hFrob hker hstable
        v hΨ hCcentLe hP hle
    have hShortA2 : ∀ v : WeylGroup Tag.F4,
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ =
          (fun α => v • α) '' parabolicRoots Tag.F4 f4ShortSupport →
        SelectedPairOutput (k := GaloisField 2 f) Δ
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) Jbar iJ := by
      intro v hΨ
      exact a2_short_selected_pair_output_of_shape (Ω := F4Omega f) (k := GaloisField 2 f)
        (f := f) FD.hf hk Δ hq hstep_inj iJ Jbar (MulAction.toPerm w) hFrob hker hstable
        v hΨ hCcentLe hP hle
    have hB2 : ∀ v : WeylGroup Tag.F4,
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ =
          (fun α => v • α) '' b2LeviRoots →
        SelectedPairOutput (k := GaloisField 2 f) Δ
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) Jbar iJ := by
      intro v hΨ
      have hΓ : Δ.Γ = Δ.model :=
        CFSG.StandardType.F4ExplicitPos.ActualPerfect.f4_langDatum_gamma_eq_model
          (n := n) (f := f) (ψ := ψ) (G0 := G₀) (B1 := B₁)
          FD.hG0 FD.hker FD.hBN FD.hinner
          (iterateFrobenius (F4Omega f) 2 f)
          (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0
      have hη := CFSG.StandardType.F4ExplicitPos.ActualPerfect.f4_actual_etaJ_injective_range
        (n := n) (f := f) (ψ := ψ) (G0 := G₀)
        FD.hG0 FD.hker g0 (FD.h15.1.trans inf_le_left)
      exact CFSG.StandardType.F4ExplicitPos.B2SelectedPair.f4_b2_selected_pair_output
        (Ω := F4Omega f) (k := GaloisField 2 f) (f := f)
        Δ FD.hf hq hk (MulAction.toPerm w) hFrob iJ hker hstable v hΨ
        hP hle hCcentLe hΓ
        ((etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
            (center_adjointGroup_F4_galoisField f) g0).comp
          (Subgroup.inclusion (FD.h15.1.trans inf_le_left)))
        hη.1 hη.2 h28
    have hB3 : ∀ v : WeylGroup Tag.F4,
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ =
          (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB3 →
        SelectedPairOutput (k := GaloisField 2 f) Δ
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) Jbar iJ := by
      intro v hΨ
      exact b3_selected_pair_output_of_shape (Ω := F4Omega f) (k := GaloisField 2 f)
        (f := f) FD.hf Δ hq hk iJ Jbar (MulAction.toPerm w) hFrob hker hstable v hΨ
        hCcentLe hP hle
    have hC3 : ∀ v : WeylGroup Tag.F4,
        componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ =
          (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviC3 →
        SelectedPairOutput (k := GaloisField 2 f) Δ
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) Jbar iJ := by
      intro v hΨ
      have h3 : compRank (componentRoots
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ) = 3 := by
        rw [hΨ, compRank_image, compRank_parabolicRoots_f4LeviC3]
      have h18 : (componentRoots
          (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ).ncard = 18 := by
        rw [hΨ, ncard_image_smul, ncard_parabolicRoots_f4LeviC3]
      exact c3_selected_pair_output_of_shape (Ω := F4Omega f) (k := GaloisField 2 f)
        (f := f) FD.hf Δ hq hk iJ Jbar (MulAction.toPerm w) hFrob hker hstable h3 h18
        v hΨ hCcentLe hP hle
    refine ⟨iJ, hle, ?_⟩
    exact selected_pair_of_six_handlers (Ω := F4Omega f) (k := GaloisField 2 f)
      (M := (F4Omega f)ˣ × (F4Omega f)ˣ) Δ
      (p := p) FD.hp.pos hpodd (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩) hpa hpd hne
      Jbar iJ hA1 hLongA2 hShortA2 hB2 hB3 hC3
  exact ⟨w, g0, hg0C, hg0, hFrob, hFin, htor, hstep, hTheker, d, hdD, coord,
    hd1, hdCL, hgen, hcoord, hexp, hcd, hattach, hout⟩

end CFSG.StandardType.F4ExplicitPos.SelectedLiteral

end

end
