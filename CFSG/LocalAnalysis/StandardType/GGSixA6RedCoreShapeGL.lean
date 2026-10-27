module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresLinear
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores

private theorem hasCoreLie_of_isSolvable {G : Type} [Group G] {U : Subgroup G}
    (hU : Group.IsSolvable U) : HasCoreLie U := by
  obtain ⟨k, hk⟩ := exists_ggDer_eq_bot hU
  refine ⟨⊥, bot_le, fun u _ s hs => ?_, ⟨k, hk.le⟩, Or.inl rfl⟩
  rw [Subgroup.mem_bot.mp hs, mul_one, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem gga6CharTwoLie_SL_toGL_range {E : Type} [Field E] [Finite E] [CharP E 2] (m : ℕ)
    (hg : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset E, s.card = 4)) :
    GGA6CharTwoLie ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) E →* GL (Fin m) E).range := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨n, _hnprime, hncard⟩ := FiniteField.card E 2
  have hgood : 3 ≤ m ∨ 4 ≤ 2 ^ (n : ℕ) := by
    rcases hg.2 with h3 | ⟨s, hs⟩
    · exact Or.inl h3
    · right
      have hle : s.card ≤ Fintype.card E := Finset.card_le_univ s
      rw [hs, hncard] at hle
      exact hle
  refine ⟨.PSL, m, (n : ℕ), ?_⟩
  refine Or.inl ⟨by decide, ?_⟩
  unfold CFSG.Open.StatedClassicalModel
  refine ⟨?_, E, inferInstance, inferInstance, ?_, ?_⟩
  · unfold CFSG.Open.StatedLieAdmissible
    refine ⟨Nat.prime_two, n.pos, hg.1, ?_, ?_⟩
    · rintro h
      injection h with hm h2n
      rcases hgood with h3 | h4
      · omega
      · rw [h2n] at h4; omega
    · rintro h
      injection h with hm h2n
      rcases hgood with h3 | h4
      · omega
      · rw [h2n] at h4; omega
  · rw [Nat.card_eq_fintype_card, hncard]
  · exact CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl m
      (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem gga6CharTwoLie_SL {E : Type} [Field E] [Finite E] [CharP E 2] (m : ℕ)
    (hg : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset E, s.card = 4)) :
    GGA6CharTwoLie (Matrix.SpecialLinearGroup (Fin m) E) :=
  GGA6CharTwoLie.of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm
    (gga6CharTwoLie_SL_toGL_range m hg)

theorem hasCoreLie_top_GL {E : Type} [Field E] [Finite E] [CharP E 2] (m : ℕ) :
    HasCoreLie (⊤ : Subgroup (GL (Fin m) E)) := by
  classical
  by_cases hg : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset E, s.card = 4)
  · refine ⟨(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* GL (Fin m) E).range,
      le_top, fun u _ s hs => ?_, ⟨1, ?_⟩, Or.inr ⟨?_, fun z _ hzc hz2 =>
        eq_one_of_mem_range_toGL hzc hz2, gga6CharTwoLie_SL_toGL_range m hg⟩⟩
    · rw [SpecialLinearGroup.range_toGL_eq_ker_det] at hs ⊢
      exact (MonoidHom.normal_ker _).conj_mem s hs u
    · rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero, SpecialLinearGroup.range_toGL_eq_ker_det]
      exact Abelianization.commutator_subset_ker _
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective)
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hg.1 hg.2)
  · have : Group.IsSolvable (GL (Fin m) E) :=
      LayerFacts.isSolvable_of_not_goodBlock (E := fun _ : Unit => E) (m := fun _ => m)
        (b := ()) hg
    exact hasCoreLie_of_isSolvable inferInstance

end CFSG.StandardType.A6Red.CoreShape
