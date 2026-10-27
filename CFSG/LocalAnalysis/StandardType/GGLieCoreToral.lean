module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTrialityPlane
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn CFSG.LocalAnalysis.GLTheoremA

theorem isToralSubgroup_of_card_le_sq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L)
    (hfin : Finite A) (hel : IsElemAbelian p A) (hcard : Nat.card A ≤ p ^ 2)
    (hE6 : τ = .E6 → p = 3 → Nat.card A ≤ p) : IsToralSubgroup τ L A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite A := hfin
  have hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    cases τ <;> simp
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ hp hp2
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hisP : IsPGroup p A := by
    intro y
    have hy : y ^ p = 1 := Subtype.ext (by simpa using hel.2 y y.2)
    have h1 : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact ⟨0, by rw [pow_zero, pow_one]; exact orderOf_eq_one_iff.mp h⟩
    · exact ⟨1, by rw [pow_one]; exact hy⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card A = p ^ k := IsPGroup.iff_card.1 hisP
  have hk2 : k ≤ 2 := by
    have h := hcard
    rw [hk] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl | rfl
  ·
    have hbot : A = ⊥ := by
      apply Subgroup.card_eq_one.mp
      simpa using hk
    refine ⟨1, Subgroup.one_mem _, fun x hx => ?_⟩
    have hx1 : x = 1 := by
      have : x ∈ (⊥ : Subgroup (ModGL τ L)) := hbot ▸ hx
      exact Subgroup.mem_bot.mp this
    simp [hx1]
  ·
    have hcardp : Nat.card A = p := by simpa using hk
    have hAne : A ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcardp
      exact hp.ne_one hcardp.symm
    obtain ⟨⟨x, hxA⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have hx : x ∈ adjointGroup τ L := hA hxA
    have hxp : x ^ p = 1 := hel.2 x hxA
    have hgen : Subgroup.zpowers x = A := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxA) ?_
      simp [hcardp, Nat.card_zpowers, orderOf_eq_prime hxp (fun h => hx1 (Subtype.ext h))]
    obtain ⟨g, hg, hgx⟩ :=
      exists_conj_torusGroup_of_pow_eq_one (τ := τ) (L := L) hp hmon (ℓ := 2)
        (Ne.symm hp2) halg hx hxp
    refine ⟨g, hg, fun y hy => ?_⟩
    have hle : Subgroup.zpowers x ≤ (torusGroup τ L).comap (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.zpowers_le.2 (by simpa [MulAut.conj_apply] using hgx)
    rw [hgen] at hle
    exact hle hy
  ·
    have hcard2 : Nat.card A = p ^ 2 := hk
    have hE6ne : τ = .E6 → p ≠ 3 := by
      intro hτE h3
      have hle := hE6 hτE h3
      rw [hcard2, h3] at hle
      norm_num at hle
    have hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) →
        rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := fun a ha =>
      T171Sh.rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd
        (K := L) hp hp2 hτ hE6ne ha
    obtain ⟨C, hC, hCA⟩ :=
      exists_conj_le_torusGroup_of_plane (τ := τ) (L := L) hmon (ℓ := 2) (Ne.symm hp2) halg
        hstab hA hcomm hel.2 hcard2
    exact ⟨C⁻¹, inv_mem hC, fun x hx => by simpa using hCA x hx⟩

end CFSG.StandardType.LieCore
