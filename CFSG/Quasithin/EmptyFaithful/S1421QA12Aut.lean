module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeGL
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.Quasithin.H13.A5S136r
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

namespace QA12

theorem exists_equiv_projectiveSL {X : Type} [Group X] (hX : IsPSL 3 2 2 X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (X ≃* LinearFlag.projectiveSL 3 F) := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hX
  exact ⟨F, hF, hFin, by simpa using hcard,
    ⟨e.trans (QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).symm⟩⟩

theorem two_le_pRank_psl34 {X : Type} [Group X] [Finite X] (hX : IsPSL 3 2 2 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := exists_equiv_projectiveSL hX
  have h1 := RankThree.PartTwo.KFacts.L34.pRank_three_projectiveSL (k := F) hcard
  have h2 := RankThree.PartOne.KLC.pRank_congr_mulEquiv e (p := 3) (by norm_num)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, h2, h1]

theorem perfect_subgroup_le_inn {X : Type} [Group X] [Finite X] (hX : IsPSL 3 2 2 X)
    {P : Subgroup (MulAut X)} (hP : ⁅P, P⁆ = P) :
    P ≤ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := exists_equiv_projectiveSL hX
  have hA : Nat.card (MulAut X) = 241920 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact RankThree.PartTwo.KFacts.L34.card_mulAut hcard
  have hZ := H13.A5.center_eq_bot_of_isPSL34 hX
  have hX20 := H13.A5.card_of_isPSL34 hX
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun a : MulAut X => a g) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * z = (z * g * z⁻¹) * z := by rw [h1]
        _ = z * g := by group
    rw [hZ] at hzc
    exact Subgroup.mem_bot.mp hzc
  set I : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hI
  have hIcard : Nat.card I = 20160 := by
    rw [← hX20]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hnormal : I.Normal := by
    refine ⟨fun n hn α => ?_⟩
    obtain ⟨x, rfl⟩ := hn
    refine ⟨α x, ?_⟩
    ext y
    simp [MulAut.conj_apply]
  have hindex : I.index = 12 := by
    have h := Subgroup.index_mul_card I
    rw [hIcard, hA] at h
    omega
  have hsolv : Group.IsSolvable (MulAut X ⧸ I) := by
    refine RankThree.PartTwo.Sec4.Census.isSolvable_of_card_dvd_two_pow_mul_three_pow
      (a := 2) (b := 1) ?_
    show I.index ∣ 2 ^ 2 * 3 ^ 1
    rw [hindex]
    norm_num
  have hS : P.map (QuotientGroup.mk' I) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(P.map (QuotientGroup.mk' I)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ↥(P.map (QuotientGroup.mk' I)) :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hP])
    exact Group.IsPerfect.not_isSolvable ↥(P.map (QuotientGroup.mk' I)) inferInstance
  intro a ha
  have h1 : (QuotientGroup.mk' I) a ∈ P.map (QuotientGroup.mk' I) := Subgroup.mem_map_of_mem _ ha
  rw [hS, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff a).mp h1

end QA12

end CFSG.Quasithin
