module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofLift
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartOne.RF4.FinalKFacts
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nontrivial_of_isoSUThree {X : Type} [Group X] {n : ℕ} (hn : Odd n)
    (h : IsoSUThree X (2 ^ (3 * n))) : Nontrivial X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * n) K :=
    ⟨Nat.prime_two, by have := hn.pos; omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨z, -, hz1, -⟩ := exists_mem_center_statedSU_ne_one hU
    (three_dvd_two_pow_three_mul_add_one hn)
  exact ⟨e.symm z, 1, fun h1 => hz1 (e.symm.injective (h1.trans (map_one _).symm))⟩


theorem exists_data83_of_ree_model (hKF : KF83ReeF4) {A : Subgroup G} {c a : G}
    (h : Hyp81 G A c L a) {n : ℕ} (hn : Odd n) {m : ℕ} (hm1 : 1 ≤ m) (hmn : 2 * m + 1 = 3 * n)
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* ReeTag.F4.reeGamma K m) :
    ∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n := by
  have hZ : Subgroup.center (ReeTag.F4.reeGamma K m) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial m K hK
  have ha := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout := h.inducesOuterTheta
  have hα3 : inducedAutHom L e ⟨a, ha⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L e ha ha3
  have hnot : ¬ IsInnerAut (inducedAutHom L e ⟨a, ha⟩) :=
    (not_isInnerAut_inducedAutHom_iff L e ha).mpr hout
  obtain ⟨β, hβ3, hβin⟩ := largeRee_order_three_inFieldCoset hm1 hK hα3 hnot
  obtain ⟨x, hαx⟩ := RankThree.PartOne.RF4.largeReeOrderThreeFieldConj m K hK β hβ3 _ hα3 hβin
  obtain ⟨e', he'⟩ : ∃ e' : L ⧸ aschbacherSolvableCore 3 L ≃* ReeTag.F4.reeGamma K m,
      e' = e.trans (MulAut.conj x)⁻¹ := ⟨_, rfl⟩
  have hα' : inducedAutHom L e' ⟨a, ha⟩ = ReeTag.F4.reeGammaFieldAut K m β := by
    rw [he', inducedAutHom_trans, hαx]
    group
  obtain ⟨hFix, y₁, y₂, hy₁f, hy₂f, hy₁3, hy₂3, hy, hy₁1, hy₂₁, hSU⟩ :=
    hKF m K n hm1 hmn hK β hβ3
  have hne : inSubgroup perfectResidual (Subgroup.centralizer
      ({y₁} : Set (ReeTag.F4.reeGamma K m))) ≠ ⊥ := by
    have := nontrivial_of_isoSUThree hn hSU
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  have hinner : ∀ d : G, d ∈ L → InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
    intro d hdL
    have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
    exact Or.inl (InducesStdKind.largeRee m hm1 K hK ⟨e', hdN, _,
      (inducedAutHom_eq_conj_of_mem e' hdL hdN).symm⟩)
  have hLbar : IsoReeF4 (L ⧸ aschbacherSolvableCore 3 L) (3 * n) :=
    ⟨m, K, inferInstance, inferInstance, inferInstance, hmn, by rw [hK, hmn], ⟨e⟩⟩
  have hC : IsoReeF4 (barCentralizer (Subgroup.zpowers a) L) n := by
    obtain ⟨k, K', hK'f, hK'fin, hK'c, hk, hK', ⟨φ⟩⟩ := hFix
    refine ⟨k, K', hK'f, hK'fin, hK'c, hk, hK', ⟨?_⟩⟩
    rw [barCentralizer_zpowers_eq_autFix ha]
    refine (autFixCongrEquiv e' _).symm.trans ?_
    rw [show MulAut.congr e' (thetaQuotMulAut L (compAction L ⟨a, ha⟩)) =
      inducedAutHom L e' ⟨a, ha⟩ from rfl, hα']
    exact φ
  refine exists_data83_of_model h e' hZ (by rw [hα']; exact hy₁f) (by rw [hα']; exact hy₂f)
    hy₁3 hy₂3 hy hy₁1 hy₂₁ hne hn hinner ?_
  rintro A₀ d - - - ⟨κ⟩
  obtain ⟨K₀, hK₀f, hK₀fin, hK₀c, ⟨φ⟩⟩ := hSU
  exact Or.inr (Or.inl ⟨hLbar, hC, K₀, hK₀f, hK₀fin, hK₀c, ⟨κ.trans φ⟩⟩)

theorem exists_data83_of_ree
    (hKF : KF83ReeF4) {A : Subgroup G} {c a : G} (h : Hyp81 G A c L a) {n : ℕ} (hn : Odd n)
    (hL : ∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid), 2 * m + 1 = 3 * n ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group)) :
    ∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n := by
  obtain ⟨m, hm, hmn, ⟨e₀⟩⟩ := hL
  have hRT : ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 (2 * m + 1) :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 m hm)
  obtain ⟨-, m', hm'1, hmm', K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma hRT
  obtain rfl : m' = m := by omega
  exact exists_data83_of_ree_model hKF h hn hm'1 hmn hK e

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
