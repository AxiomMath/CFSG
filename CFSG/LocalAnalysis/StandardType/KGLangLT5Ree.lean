module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestLabels
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGReeLangPositionF4
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcModel
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcGlue
import CFSG.LocalAnalysis.StandardType.KGLangReeTorusInput
import CFSG.LocalAnalysis.StandardType.KGLangReeBridge
import CFSG.LocalAnalysis.StandardType.GGL45NtRecExTw
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.TCX.Ree
  CFSG.StandardType.LieCore

private theorem kgLangReeAsmAux_exists_ne_comm_of_isPerfect {X : Type*} [Group X] [Nontrivial X]
    (hX : Group.IsPerfect X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hc : commutator X = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  rw [hX.commutator_eq_top] at hc
  exact top_ne_bot hc

private lemma kgLangReeAsmAux_pow_apply (Γ : Type*) [Group Γ] (e : MulAut Γ) (n : ℕ) :
    ∀ x : Γ, ((e ^ n : MulAut Γ) : Γ → Γ) x = e^[n] x := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

private lemma kgLangReeAsmAux_endPow_toMonoidHom (Γ : Type*) [Group Γ] (e : MulAut Γ) (n : ℕ) :
    endPow e.toMonoidHom n = ((e ^ n).toMonoidHom : Γ →* Γ) := by
  ext x
  rw [endPow_apply]
  simpa using (kgLangReeAsmAux_pow_apply Γ e n x).symm

private theorem kgLangReeAsmAux_datumCont
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (ha : 1 ≤ a)
    (hRLP : GGReeLangPositionF4) (hM1 : GGLieToralPosition)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) (C : ReeClosure L)
    (hrec : GGL45NtRec p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)))
    (hcyc : GGRawPCyclic p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)))
    (hconj : GGRawFieldConj p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))) :
    KGLangTorusDatumCont p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  haveI : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma (K := K) (a := a) ha hK
  haveI hsRee : IsSimpleGroup ↥(ReeTag.F4.reeGamma K a) := gff_isSimpleGroup_reeGamma ha hK
  haveI : Nontrivial ↥(ReeTag.F4.reeGamma K a) := hsRee.toNontrivial
  have hs : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := eR.isSimpleGroup
  have hperf : Group.IsPerfect ↥(ReeTag.F4.reeGamma K a) :=
    ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) ha hK⟩
  have hna : ∃ x y : LargeEvenCenterQuot (LargeEvenTwF4H a K), x * y ≠ y * x :=
    nonabelian_of_mulEquiv eR.symm (kgLangReeAsmAux_exists_ne_comm_of_isPerfect hperf)
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have hp2le : 2 ≤ p := hp.two_le
    omega
  obtain ⟨J, S, hJI, hJS, hN, hcycS, hpS⟩ := hcyc hs hna
  have hM : KGLangTorusMPart p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
    by_cases hF : ∃ f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K),
        orderOf f = p
    · obtain ⟨b, hbr, hfin'⟩ :=
        kgLangRee_absBridge (K := K) (L := L) ha hp hp2 hK hL C hF
      have hstab : ∀ g ∈ (((C.Φ * C.Fr ^ b) ^ p).toMonoidHom.eqLocus
          (MonoidHom.id (adjointGroup ReeTag.F4.tag L))),
          (C.Φ * C.Fr ^ b).toMonoidHom g ∈ (((C.Φ * C.Fr ^ b) ^ p).toMonoidHom.eqLocus
            (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := by
        rw [← kgLangReeAsmAux_endPow_toMonoidHom (adjointGroup ReeTag.F4.tag L)
          (C.Φ * C.Fr ^ b) p]
        exact eqLocus_endPow_stab ((C.Φ * C.Fr ^ b).toMonoidHom) p
      have hfix : ∀ g ∈ (((C.Φ * C.Fr ^ b) ^ p).toMonoidHom.eqLocus
          (MonoidHom.id (adjointGroup ReeTag.F4.tag L))),
          endPow ((C.Φ * C.Fr ^ b).toMonoidHom) p g = g := by
        intro g hg
        rw [kgLangReeAsmAux_endPow_toMonoidHom (adjointGroup ReeTag.F4.tag L)
          (C.Φ * C.Fr ^ b) p]
        simpa using hg
      haveI := hfin'
      exact kgLangTorusMPart_of_absBridge hp hs hna hconj hrec hstab hfix hbr
        (kgLangReeTorusInput hRLP hM1 hL C hp hp5)
    · push Not at hF
      exact kgLangTorusMPart_of_forall_orderOf_ne hconj hs hna hF
  intro hfin θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  haveI := hfin
  have hα₀J : kgInducedAut θ α₀ ∉ J := by
    intro h
    exact hα₀I (hJI ▸ h)
  have hAS : ∀ α ∈ A, kgInducedAut θ α ∈ S := by
    intro α hα
    exact hpS (kgInducedAut θ α) ⟨1, by rw [pow_one, ← map_pow, hA.2 α hα, map_one]⟩
  refine ⟨?_, hM θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I⟩
  intro α hα
  obtain ⟨k, hk⟩ := kgLangLT1_decomp hp θ hJS hN hcycS hA hAS hα₀ hα₀J α hα
  exact ⟨k, hJI ▸ hk⟩

theorem kgLangTorusDatumReeInput_holds
    (hRLP : GGReeLangPositionF4) (hM1 : GGLieToralPosition) :
    KGLangTorusDatumOn fun p lab =>
      GGNbrLangRegExcLabel p lab ∧ GGNbrLangRest12Label p lab ∧ lab.tag = .twF4 := by
  intro p lab hp hp2 hlab hS
  obtain ⟨hreg, h12, htw⟩ := hS
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at htw
  subst htw
  dsimp only [LargeEvenInLambda2] at hlab
  have hn3 : 3 ≤ n := hlab.2.2.2
  have ha : 1 ≤ (n - 1) / 2 := by omega
  have hp3 : p ≠ 3 := by
    rcases hreg with h | ⟨h, hp3⟩ | ⟨h, hp3⟩ | ⟨h, hp3, hp5⟩
    · exact absurd h (by simp)
    · exact hp3
    · exact hp3
    · exact hp3
  have hkg : GGL45KGLabel p (⟨.twF4, rank, n⟩ : LargeEvenLabel) := by
    simp [GGL45KGLabel, hp3]
  have hfam : GGL45NtFamExTw p (⟨.twF4, rank, n⟩ : LargeEvenLabel) := by
    refine ⟨⟨?_, ?_, ?_⟩, Or.inr rfl⟩
    · simpa [GGL45FamNonTorsion] using hp3
    · simp [GGL45NtVacLabel]
    · simp [GGL45NtExcLabel]
  have hrecAll : LargeEvenLabelAll (⟨.twF4, rank, n⟩ : LargeEvenLabel) (GGL45NtRec p) :=
    ggL45NtRecOn_exTw p hp hp2 (⟨.twF4, rank, n⟩ : LargeEvenLabel) hlab hkg hfam
  have hcycAll : LargeEvenLabelAll (⟨.twF4, rank, n⟩ : LargeEvenLabel) (GGRawPCyclic p) :=
    ggRawPCyclicOn_excCyclic p hp hp2 (⟨.twF4, rank, n⟩ : LargeEvenLabel) hlab
      (Or.inr (Or.inr rfl))
  have hconjAll : LargeEvenLabelAll (⟨.twF4, rank, n⟩ : LargeEvenLabel) (GGRawFieldConj p) :=
    ggRawFieldConjOn_twF4 p hp hp2 (⟨.twF4, rank, n⟩ : LargeEvenLabel) hlab rfl
  intro Q hQ
  have h1 : LargeEvenRawDatum (⟨.twF4, rank, n⟩ : LargeEvenLabel)
      (fun R _ I F => Q R I F ∧ (GGL45NtRec p R I F ∧ GGRawPCyclic p R I F ∧
        GGRawFieldConj p R I F)) :=
    largeEvenLabelAll_and hrecAll (largeEvenLabelAll_and hcycAll hconjAll) Q hQ
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at h1 ⊢
  obtain ⟨K, hf, hfin, hK, hQ', hrec, hcyc, hconj⟩ := h1
  refine ⟨K, hf, hfin, hK, hQ', ?_⟩
  obtain ⟨C⟩ := exists_reeClosure (K := ZMod 2) (L := AlgebraicClosure (ZMod 2))
  exact kgLangReeAsmAux_datumCont (L := AlgebraicClosure (ZMod 2)) hp hp2 hp3 ha hRLP hM1 hK
    algClosure_zmod_isAlgebraic C hrec hcyc hconj

end CFSG.StandardType
