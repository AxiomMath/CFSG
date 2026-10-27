module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairRootSpan
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinE78
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgE7
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacEAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
import CFSG.LocalAnalysis.StandardType.GGLieOddCoverSplit
import CFSG.LocalAnalysis.StandardType.GGExcKGSFFinite
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ClassicalInvolution.WeakCT
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.StandardType.LieOddCover
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag)
open scoped MatrixGroups


theorem rckPairE8_shape
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hTp : rootDiagUnit τ a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 8)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 240) :
    τ = .E8 ∧ ∃ (β : Option (Fin τ.rank) → Fin τ.rank → ℤ)
      (l : Fin 8 → Option (Fin τ.rank)), (∀ b, IsRoot τ (β b)) ∧
      componentRoots (rootCharHom a) i = rootsOfFam β (Set.range l) ∧
      (∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
        iform (β (l i)) (β (l j)) = 0) ∧
      ∀ {F : Type} [Field F] (i j : Fin 8), edgeE 8 i j → ∃ θ : SL(3, F) →* ModGL τ F,
        θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l i)) ∧
          θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l j)) := by
  classical
  have hpL : (p : GGL) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff GGL 2 p).1 h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hle : 8 ≤ τ.rank := hrank ▸ compRank_le_rank _
  have hτ : τ = .E8 := by
    cases τ <;> simp [Tag.rank] at hle ⊢
  refine ⟨hτ, ?_⟩
  subst hτ
  have h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  have hn' : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [hcard, hrank]
    rfl
  obtain ⟨v, n, l, -, -, hrk, hroots, hnon, hE⟩ :=
    l154_exists_tree_of_class_rank kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card edgeE 6
      eRootCount e8_ecount e8_etrees (fun n => n = 6 ∨ n = 7 ∨ n = 8) e8_elen S hp hpL hTp i h6 hn'
  have hn8 : n = 8 := by rw [← hrk, hrank]
  subst hn8
  refine ⟨fun x => v • kacE8.extRoot x, l,
    fun b => IsRoot.smul (kacE8.isRoot_extRoot b) v, ?_, ?_, ?_⟩
  · rw [hroots, l154_smul_image_rootsOf_eq]
  · intro c d hcd h1 h2
    show iform (v • kacE8.extRoot (l c)) (v • kacE8.extRoot (l d)) = 0
    rw [iform_smul]
    exact hnon c d hcd h1 h2
  · intro F _ c d hcd
    exact treeFrames kacE8 (fun {F} _ x y h => e8_frames x y h) v l (edgeE 8) hE
      (F := F) c d hcd

theorem rckPairE8_holds :
    RCKPairE8 := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hshape hQS
  obtain ⟨hkind, hrank, hcard⟩ := hshape
  obtain ⟨hτ, β, l, hroot, hroots, hgram, hframe⟩ :=
    rckPairE8_shape S hp hp2 hTp i hrank hcard
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hs
  have hs0 : 0 < s := by
    rw [hs]
    exact (outer_componentOrbitLength_spec S hT i).1
  have hpos : 0 < h := by
    have hq2 : 2 ≤ S.D.q := by
      obtain ⟨r, e, hr, he, hqe⟩ := (isPrimePow_nat_iff S.D.q).1 S.hqpow.1
      rw [← hqe]
      exact le_trans hr.two_le (Nat.le_self_pow (by omega) r)
    rcases Nat.eq_zero_or_pos h with h0 | hh
    · rw [h0] at hq
      simp at hq
      omega
    · exact hh
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) :=
    twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  have hadm : CFSG.Open.StatedLieAdmissible .E8 0 2 (h * s) :=
    ⟨Nat.prime_two, Nat.succ_le_of_lt (Nat.mul_pos hpos hs0), rfl⟩
  have hfin : Finite (ggU .E8 0 (h * s)).K :=
    ggU_finite_exc (t := .E8) (by unfold GGExcFive; simp)
      ⟨hadm, by rw [show (ggU .E8 0 (h * s)).D.rank = 8 from rfl]; norm_num⟩
  have hperf : Group.IsPerfect (ggU .E8 0 (h * s)).K :=
    CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 (GaloisField 2 (h * s))
  have hsplit : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .E8 0 (h * s)).K :=
    oddCentralSplit_ggU_pos (by unfold GGPosTag; simp) hadm
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rw [hτ]
    exact Or.inr (Or.inr (Or.inr rfl))
  refine rckFrameCoverPair_of_rootSpanCover S a hT i h hq hinner
    (ggU .E8 0 (h * s)) rfl (Or.inl ⟨.E8, 0, by simp, hadm, rfl⟩) hfin hperf hsplit ?_
  intro σ _ hKcard
  haveI : CharP ↥(fixSubfield σ) 2 := Subfield.charP _ 2
  obtain ⟨Ψ0, hsurj0, hker0, hpair0⟩ :=
    exists_cover_rootSpan_e8 hτ' (g := h * s) (Nat.mul_pos hpos hs0) hKcard β hroot l hgram
      hframe
  have hcomp : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
      rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l)) := by
    show rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [show componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = s from hs.symm]
  rw [hcomp]
  rw [hroots]
  refine ⟨Ψ0, hsurj0, hker0, ?_⟩
  intro _ δ hδ _
  exact hpair0 δ hδ

end CFSG.StandardType.RCKRP
