module

public import CFSG.LocalAnalysis.StandardType.GGLangE8RecogBase
import CFSG.LocalAnalysis.StandardType.GGK0LQRecA
import CFSG.LocalAnalysis.StandardType.GGK0LQRecD
import CFSG.LocalAnalysis.StandardType.GGK0LQRecE
import CFSG.LocalAnalysis.StandardType.GGK0LQRecTwE6
import CFSG.LocalAnalysis.StandardType.GGK0LQRecTriD4
import CFSG.LocalAnalysis.StandardType.GGK0LQRecTwoD
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDispatch

public section

namespace CFSG.StandardType

section Recognition

open CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma recogd_labelIso_eq {labJ lab' : LargeEvenLabel}
    (hiso : GGLabelIso labJ lab') (hrank : labJ.rank = 8)
    (htag : labJ.tag = .A ∨ labJ.tag = .twA) : lab' = labJ := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h.symm
  · obtain ⟨ht, -⟩ := h
    rcases htag with ht' | ht' <;> rw [ht'] at ht <;> exact absurd ht (by decide)
  · obtain ⟨h1, -⟩ := h
    have htg : labJ.tag = .D := congrArg LargeEvenLabel.tag h1
    rw [htg] at htag
    rcases htag with ht | ht <;> exact absurd ht (by decide)
  · obtain ⟨h1, -⟩ := h
    have hrk : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    rw [hrk] at hrank
    exact absurd hrank (by decide)
  · obtain ⟨h1, -⟩ := h
    have htg : labJ.tag = .twD := congrArg LargeEvenLabel.tag h1
    rw [htg] at htag
    rcases htag with ht | ht <;> exact absurd ht (by decide)
  · obtain ⟨h1, -⟩ := h
    have hrk : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    rw [hrk] at hrank
    exact absurd hrank (by decide)
  · obtain ⟨h1, -⟩ := h
    have htg : labJ.tag = .twD := congrArg LargeEvenLabel.tag h1
    rw [htg] at htag
    rcases htag with ht | ht <;> exact absurd ht (by decide)
  · obtain ⟨-, h2⟩ := h
    have hrk : labJ.rank = 1 := congrArg LargeEvenLabel.rank h2
    rw [hrk] at hrank
    exact absurd hrank (by decide)

private lemma recogd_mul_succ_injective : Function.Injective (fun n : ℕ => n * (n + 1)) := by
  have hmono : StrictMono (fun n : ℕ => n * (n + 1)) := by
    intro a b hab
    calc a * (a + 1) < (a + 1) * (a + 1) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self a) (Nat.succ_pos a)
      _ ≤ b * (b + 1) := Nat.mul_le_mul (by omega) (by omega)
  exact hmono.injective

private lemma recogd_frame_dim {ν r : ℕ} (hν : 3 ≤ ν) (h : ν * (ν - 1) = r * (r + 1)) :
    ν = r + 1 := by
  have h1 : (ν - 1) * ((ν - 1) + 1) = r * (r + 1) := by
    have h2 : (ν - 1) * ((ν - 1) + 1) = ν * (ν - 1) := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ ν), Nat.mul_comm]
    rw [h2, h]
  have h3 : ν - 1 = r := recogd_mul_succ_injective h1
  omega

private theorem recogd_suN_two_one_false
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .suN)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hr2 : compRank (componentRoots (rootCharHom a) i) = 2)
    (hNq : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2) :
    False := by
  classical
  obtain ⟨h2, hn⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hk
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_frame_of_typeA_tag_T_of_prime
      CFSG.HardMathSupport.Timmesfeld.CrossChar.g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.ssexc_suN_perm S hT i hk hν hψ hκ hnorm hΨ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2' : r = 2 := by
    have h1 : r = ringChar L := CharP.eq L hchar (ringChar.charP L)
    have h2 : ringChar L = 2 := by
      clear hchar
      exact ringChar.eq L 2
    exact h1.trans h2
  have hq2 : S.D.q = 2 ^ e := by rw [hq, hr2']
  have heq : (2 : ℕ) ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) = 2 := by
    calc (2 : ℕ) ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        = (2 ^ e) ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := pow_mul 2 e _
      _ = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by rw [← hq2]
      _ = 2 := hNq
  have hν3 : ν = 3 := by
    have hcard : ν * (ν - 1) = 2 * (2 + 1) := by
      rw [← CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm, ← hΨ, hn, hr2]
    exact recogd_frame_dim (r := 2) hν hcard
  have hnot := CFSG.LocalAnalysis.GLTheoremA.RationalModel.not_unitaryFrame_three_two
    S hT i hν hψ hΨ π hπ hr hchar he hq hqs
  exact hnot (by rw [hν3, hr2', heq])

private theorem recogd_main
    {τ : Tag} (hτ : τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hlab : GGHasLabel labJ (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)))
    (htag : labJ.tag = .A ∨ labJ.tag = .twA) (hrank : labJ.rank = 8)
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N)
    (hn : labJ.n = N) :
    compRank (componentRoots (rootCharHom a) i) = 8 ∧
      (componentRoots (rootCharHom a) i).ncard = 72 ∧
      ((labJ.tag = .A ∧ twistKind S.ρ (rootCharHom a) i = .inner) ∨
        (labJ.tag = .twA ∧ twistKind S.ρ (rootCharHom a) i = .suN)) := by
  subst hτ
  classical
  have hN1 : 1 ≤ N := by rw [← hn]; exact hΛJ.1
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrankc, hncardc⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_cand_of_class
          CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE8
          CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_E8
          CFSG.HardMathSupport.Timmesfeld.CrossChar.e8_tree
          CFSG.HardMathSupport.Timmesfeld.CrossChar.e8_adj
          CFSG.HardMathSupport.Timmesfeld.CrossChar.e8_check
          CFSG.HardMathSupport.Timmesfeld.CrossChar.e8_lt
          CFSG.HardMathSupport.Timmesfeld.CrossChar.e8_card S hp hpL hTp i
      have hshape := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.e8_shape c hc hlen
      rw [← hncardc, ← hrankc] at hshape
      have hrle : compRank (componentRoots (rootCharHom a) i) ≤ 8 := by
        have h := CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank_le_rank
          (componentRoots (rootCharHom a) i)
        rwa [show Tag.E8.rank = 8 from rfl] at h
      have hinner := CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner_of_twistKind_eq_innerT
        S CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk
      rcases hshape with hA | hD | hE
      · obtain ⟨hr1le, hnA⟩ := hA
        by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
        · have hn1 : (componentRoots (rootCharHom a) i).ncard = 2 := by
            rw [hr1] at hnA
            norm_num at hnA
            exact hnA
          obtain ⟨K, -, -, f, -, hKcard, hfeq, -, hK4, -, -, -⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.RationalModel.exists_slCover_rationalComponent_rankOne
              S hT i hr1 hn1 hqs
          have hchar : ringChar L = 2 := ringChar.eq L 2
          have hfN : N = f := by
            apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
            change 2 ^ N = 2 ^ f
            rw [hchar] at hfeq
            rw [← hN, ← hfeq]
          subst hfN
          rw [hchar] at hKcard
          have hN2 : 2 ≤ N := by
            have h4 : 4 ≤ 2 ^ N := by rw [← hKcard]; exact hK4
            by_contra h
            have hle : N ≤ 1 := by omega
            interval_cases N <;> norm_num at h4
          have hlab' : GGHasLabel ⟨.A, 1, N⟩
              (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
                Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
            GGK0LQ.lq_rec_A1 S hT i hr1 hn1 hN hN2
          have hΛ' : LargeEvenInLambda2 (⟨.A, 1, N⟩ : LargeEvenLabel) := by
            refine ⟨hN1, ?_, ?_⟩
            · change 1 ≤ (1 : ℕ)
              decide
            · intro _
              exact hN2
          have hiso : GGLabelIso labJ (⟨.A, 1, N⟩ : LargeEvenLabel) :=
            ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
          have heq : (⟨.A, 1, N⟩ : LargeEvenLabel) = labJ :=
            recogd_labelIso_eq hiso hrank htag
          exfalso
          have hrk := congrArg LargeEvenLabel.rank heq
          simp at hrk
          omega
        · have hr2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
          have hlab' : GGHasLabel ⟨.A, compRank (componentRoots (rootCharHom a) i), N⟩
              (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
                Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
            GGK0LQ.lq_rec_A S hp hpL hT hTp i hk hr2 hnA hN
          have hΛ' : LargeEvenInLambda2
              (⟨.A, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) := by
            refine ⟨hN1, ?_, ?_⟩
            · change 1 ≤ compRank (componentRoots (rootCharHom a) i)
              omega
            · intro h
              exfalso
              change compRank (componentRoots (rootCharHom a) i) = 1 at h
              omega
          have hiso : GGLabelIso labJ
              (⟨.A, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) :=
            ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
          have heq : (⟨.A, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) =
              labJ := recogd_labelIso_eq hiso hrank htag
          have hr8 : compRank (componentRoots (rootCharHom a) i) = 8 := by
            have h := congrArg LargeEvenLabel.rank heq
            simp at h
            omega
          refine ⟨hr8, ?_, Or.inl ⟨?_, by simp only [hk]⟩⟩
          · rw [hr8] at hnA
            norm_num at hnA
            exact hnA
          · have h := congrArg LargeEvenLabel.tag heq
            simp at h
            exact h.symm
      · obtain ⟨hr4, hnD⟩ := hD
        have hlab' : GGHasLabel ⟨.D, compRank (componentRoots (rootCharHom a) i), N⟩
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
          GGK0LQ.lq_rec_D (Or.inr (Or.inr rfl)) S hp hpL hT hTp i hr4 hnD hinner hN
        have hΛ' : LargeEvenInLambda2
            (⟨.D, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) := by
          refine ⟨hN1, ?_⟩
          change 3 ≤ compRank (componentRoots (rootCharHom a) i)
          omega
        have hiso : GGLabelIso labJ
            (⟨.D, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) :=
          ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
        have heq : (⟨.D, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) =
            labJ := recogd_labelIso_eq hiso hrank htag
        exfalso
        have htg := congrArg LargeEvenLabel.tag heq
        simp at htg
        rcases htag with ht | ht <;> rw [ht] at htg <;> exact absurd htg (by decide)
      · obtain ⟨hr6, hnE⟩ := hE
        have hr678 : compRank (componentRoots (rootCharHom a) i) = 6 ∨
            compRank (componentRoots (rootCharHom a) i) = 7 ∨
            compRank (componentRoots (rootCharHom a) i) = 8 := by omega
        rcases hr678 with h6 | h7 | h8
        · have hn6 : (componentRoots (rootCharHom a) i).ncard = 72 := by
            rw [h6] at hnE
            have : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eRootCount 6 = 72 := by decide
            rwa [this] at hnE
          have hlab' : GGHasLabel ⟨.E6, 0, N⟩
              (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
                Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
            GGK0LQ.lq_rec_E6 (Or.inr rfl) S hp hpL hT hTp i h6 hn6 hinner hN
          have hΛ' : LargeEvenInLambda2 (⟨.E6, 0, N⟩ : LargeEvenLabel) := ⟨hN1, rfl⟩
          have hiso : GGLabelIso labJ (⟨.E6, 0, N⟩ : LargeEvenLabel) :=
            ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
          have heq : (⟨.E6, 0, N⟩ : LargeEvenLabel) = labJ :=
            recogd_labelIso_eq hiso hrank htag
          exfalso
          have htg := congrArg LargeEvenLabel.tag heq
          simp at htg
          rcases htag with ht | ht <;> rw [ht] at htg <;> exact absurd htg (by decide)
        · have hn7 : (componentRoots (rootCharHom a) i).ncard = 126 := by
            rw [h7] at hnE
            have : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eRootCount 7 = 126 := by decide
            rwa [this] at hnE
          have hlab' : GGHasLabel ⟨.E7, 0, N⟩
              (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
                Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
            GGK0LQ.lq_rec_E7 S hp hpL hT hTp i h7 hn7 hinner hN
          have hΛ' : LargeEvenInLambda2 (⟨.E7, 0, N⟩ : LargeEvenLabel) := ⟨hN1, rfl⟩
          have hiso : GGLabelIso labJ (⟨.E7, 0, N⟩ : LargeEvenLabel) :=
            ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
          have heq : (⟨.E7, 0, N⟩ : LargeEvenLabel) = labJ :=
            recogd_labelIso_eq hiso hrank htag
          exfalso
          have htg := congrArg LargeEvenLabel.tag heq
          simp at htg
          rcases htag with ht | ht <;> rw [ht] at htg <;> exact absurd htg (by decide)
        · exfalso
          have hn8 : (componentRoots (rootCharHom a) i).ncard = 240 := by
            rw [h8] at hnE
            have : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eRootCount 8 = 240 := by decide
            rwa [this] at hnE
          have h240 : Tag.E8.rootCount ≤ (componentRoots (rootCharHom a) i).ncard := by
            rw [hn8]
            decide
          exact h1 (CFSG.HardMathSupport.Timmesfeld.LangTorus.rootDiagUnit_eq_one_of_ncard i h240)
  | suN =>
      obtain ⟨hr2, hnA⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hk
      by_cases h21 : compRank (componentRoots (rootCharHom a) i) = 2 ∧ N = 1
      · exfalso
        obtain ⟨hr2eq, hN1eq⟩ := h21
        have hNq : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 := by
          rw [hN, hN1eq]
          norm_num
        exact recogd_suN_two_one_false S hp hpL hT hTp i hk hqs hr2eq hNq
      · have hlab' : GGHasLabel ⟨.twA, compRank (componentRoots (rootCharHom a) i), N⟩
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
          GGK0LQ.lq_rec_SU S hp hpL hT hTp i hk hN h21
        have hΛ' : LargeEvenInLambda2
            (⟨.twA, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) := by
          refine ⟨hN1, hr2, ?_⟩
          intro h2r
          change 2 ≤ N
          by_contra hN2
          exact h21 ⟨h2r, by omega⟩
        have hiso : GGLabelIso labJ
            (⟨.twA, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) :=
          ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
        have heq : (⟨.twA, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) =
            labJ := recogd_labelIso_eq hiso hrank htag
        have hr8 : compRank (componentRoots (rootCharHom a) i) = 8 := by
          have h := congrArg LargeEvenLabel.rank heq
          simp at h
          omega
        refine ⟨hr8, ?_, Or.inr ⟨?_, by simp only [hk]⟩⟩
        · rw [hr8] at hnA
          norm_num at hnA
          exact hnA
        · have h := congrArg LargeEvenLabel.tag heq
          simp at h
          exact h.symm
  | twoD =>
      obtain ⟨-, hr4, hnD⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.twoD_kind_unpack hk
      have hlab' : GGHasLabel ⟨.twD, compRank (componentRoots (rootCharHom a) i), N⟩
          (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
        GGK0LQ.lq_rec_twoD S hp hpL hT hTp h1 i hk hN
      have hΛ' : LargeEvenInLambda2
          (⟨.twD, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) := by
        refine ⟨hN1, ?_⟩
        change 2 ≤ compRank (componentRoots (rootCharHom a) i)
        omega
      have hiso : GGLabelIso labJ
          (⟨.twD, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
      have heq : (⟨.twD, compRank (componentRoots (rootCharHom a) i), N⟩ : LargeEvenLabel) =
          labJ := recogd_labelIso_eq hiso hrank htag
      exfalso
      have htg := congrArg LargeEvenLabel.tag heq
      simp at htg
      rcases htag with ht | ht <;> rw [ht] at htg <;> exact absurd htg (by decide)
  | exc =>
      obtain ⟨-, hcases⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exc_kind hk
      rcases hcases with ⟨h6, -⟩ | ⟨h4, -, -⟩
      · have hlab' : GGHasLabel ⟨.twE6, 0, N⟩
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
          GGK0LQ.lq_rec_twE6 S hp hpL hT hTp h1 i hk h6 hN
        have hΛ' : LargeEvenInLambda2 (⟨.twE6, 0, N⟩ : LargeEvenLabel) := ⟨hN1, rfl⟩
        have hiso : GGLabelIso labJ (⟨.twE6, 0, N⟩ : LargeEvenLabel) :=
          ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
        have heq : (⟨.twE6, 0, N⟩ : LargeEvenLabel) = labJ :=
          recogd_labelIso_eq hiso hrank htag
        exfalso
        have htg := congrArg LargeEvenLabel.tag heq
        simp at htg
        rcases htag with ht | ht <;> rw [ht] at htg <;> exact absurd htg (by decide)
      · have hlab' : GGHasLabel ⟨.triD4, 0, N⟩
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
          GGK0LQ.lq_rec_triD4 S hp hpL hT hTp h1 i hk h4 hN
        have hΛ' : LargeEvenInLambda2 (⟨.triD4, 0, N⟩ : LargeEvenLabel) := ⟨hN1, rfl⟩
        have hiso : GGLabelIso labJ (⟨.triD4, 0, N⟩ : LargeEvenLabel) :=
          ggLabelRigidInput_holds labJ _ _ hΛJ hΛ' hlab hlab'
        have heq : (⟨.triD4, 0, N⟩ : LargeEvenLabel) = labJ :=
          recogd_labelIso_eq hiso hrank htag
        exfalso
        have htg := congrArg LargeEvenLabel.tag heq
        simp at htg
        rcases htag with ht | ht <;> rw [ht] at htg <;> exact absurd htg (by decide)

theorem recoga_kind_dispatch
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord) (hτ : B.τ = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    {b : Bs} (hb : b ≠ 1) (i : KernelComponent (rootCharHom (B.a b)))
    (hqs : CFSG.IsQuasisimple ↥(recogaR B b i))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hlab : GGHasLabel labJ (↥(recogaR B b i) ⧸ Subgroup.center ↥(recogaR B b i)))
    (htag : labJ.tag = .A ∨ labJ.tag = .twA) (hrank : labJ.rank = 8) (hn : labJ.n = f) :
    compRank (componentRoots (rootCharHom (B.a b)) i) = 8 ∧
      (componentRoots (rootCharHom (B.a b)) i).ncard = 72 ∧
      ((labJ.tag = .A ∧ twistKind B.setup.ρ (rootCharHom (B.a b)) i = .inner) ∨
        (labJ.tag = .twA ∧ twistKind B.setup.ρ (rootCharHom (B.a b)) i = .suN)) := by
  have hf : 1 ≤ f := by rw [← hn]; exact hΛJ.1
  haveI : CharP L 2 := recoga_charP B hf
  have hN : B.setup.D.q ^ componentOrbitLength B.setup.ρ
      (componentRoots (rootCharHom (B.a b)) i) = 2 ^ f := by
    rw [recoga_orbitLength_eq_one B hτ b i, pow_one, B.q_eq]
  exact recogd_main hτ B.setup hp (recoga_natCast_ne_zero B hf hp hp2) (B.a_torus b)
    (recoga_rootDiagUnit_pow B b) (recoga_rootDiagUnit_ne_one B hp hb) i hqs hΛJ hlab htag
    hrank hN hn

end Recognition

end CFSG.StandardType

end
