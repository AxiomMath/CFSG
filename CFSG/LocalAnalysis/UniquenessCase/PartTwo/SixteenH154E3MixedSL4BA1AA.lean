module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_sl4_natNorm_lin_dvd {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    (hD : IsElemAbelian q D) :
    D ≤ linSub (ι := Fin 2) (K := K) ∧ Nat.card D ∣ 180 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hΓ : HasScalarCommutant (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    hasScalarCommutant_statedSL (K := K) (by norm_num)
  have hAut : Nat.card (K ≃+* K) = 2 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := 2) Nat.prime_two K (by rw [hK]; norm_num)).1
    simpa using h
  let φ : ↥D →* (K ≃+* K) := (fieldHom hΓ).comp (Subgroup.inclusion hDN)
  have hφ1 : φ = 1 := by
    refine MonoidHom.ext fun d => ?_
    have hdq : d ^ q = 1 := Subtype.ext (hD.2 d d.2)
    have hq_dvd : orderOf (φ d) ∣ q :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hdq, map_one])
    have h2_eq : (φ d) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := φ d)
      rwa [hAut] at this
    have h2_dvd : orderOf (φ d) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2_eq
    rcases (Nat.dvd_prime hq).mp hq_dvd with h1 | hq_eq
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [hq_eq] at h2_dvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2_dvd)
  have hDlin : D ≤ linSub (ι := Fin 2) (K := K) := by
    intro d hd
    have hφd : (fieldHom hΓ) ((Subgroup.inclusion hDN) ⟨d, hd⟩) = 1 := by
      have h := congrFun (congrArg DFunLike.coe hφ1) ⟨d, hd⟩
      exact h
    have hφd' : (fieldHom hΓ) (⟨d, hDN hd⟩ :
        ↥(natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))) = 1 := by
      rwa [show (Subgroup.inclusion hDN) ⟨d, hd⟩ = ⟨d, hDN hd⟩ from rfl] at hφd
    exact (fieldHom_eq_one_iff hΓ ⟨d, hDN hd⟩).mp hφd'
  have hdiv : Nat.card D ∣ 180 := by
    have h1 : Nat.card D ∣ Nat.card (linSub (ι := Fin 2) (K := K)) :=
      Subgroup.card_dvd_of_le hDlin
    have hlin : Nat.card (linSub (ι := Fin 2) (K := K)) = 180 := by
      have hrange : (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K)).range =
          linSub (ι := Fin 2) (K := K) := by
        ext g
        constructor
        · rintro ⟨A, rfl⟩
          exact isSemilinear_matAut A
        · intro hg
          obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hg
          exact ⟨A, rfl⟩
      rw [← hrange]
      rw [← Nat.card_congr (MonoidHom.ofInjective
        (f := (matHom : GL (Fin 2) K →* MulAut (StdMod (Fin 2) K))) matHom_injective).toEquiv]
      rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hK]
      norm_num
    rwa [hlin] at h1
  exact ⟨hDlin, hdiv⟩

theorem s16h_sl4_natNorm_elemAbelian_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {D : Subgroup (MulAut (StdMod (Fin 2) K))}
    (hDN : D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    (hD : IsElemAbelian q D) :
    Nat.card D ≤ q := by
  obtain ⟨-, hdiv⟩ := s16h_sl4_natNorm_lin_dvd hK hq hq2 hDN hD
  haveI : Fact q.Prime := ⟨hq⟩
  have hpg : IsPGroup q D := CFSG.Open.IsElemAbelian.isPGroup hD
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  rw [hk] at hdiv ⊢
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero]
    exact hq.one_le
  · have hdvd : q ∣ 180 := dvd_trans (dvd_pow_self q hkpos.ne') hdiv
    have hq5 : q = 5 := by
      have h180 : (180 : ℕ) = 2 ^ 2 * (3 ^ 2 * 5) := by norm_num
      rw [h180] at hdvd
      rcases hq.dvd_mul.mp hdvd with h2 | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
          (hq.dvd_of_dvd_pow h2)) hq2
      · rcases hq.dvd_mul.mp h' with h3 | h5
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
            (hq.dvd_of_dvd_pow h3)) hq3
        · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5
    have hk1 : k = 1 := by
      by_contra hk1
      have hk2 : 2 ≤ k := by omega
      have h25 : 25 ∣ 180 := by
        rw [hq5] at hdiv
        exact dvd_trans (pow_dvd_pow 5 hk2) hdiv
      norm_num at h25
    rw [hq5, hk1, pow_one]

private theorem s16h_sl4_stab_commSub {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) :
    g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

theorem s16h_sl4_row_block_bound_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    s16h_BlockBound A L q 1 := by
  intro E hE hEab
  obtain ⟨K, hKf, hKfin, hKcard, D, hDN, hDab, hcard⟩ :=
    s16h_H5_row_SL2_four_bridge hc hrow hq hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hDle : Nat.card D ≤ q :=
    s16h_sl4_natNorm_elemAbelian_one hKcard hq hq2 hq3 hDN hDab
  rw [hcard] at hDle
  have hEU : E ≤ stabSub (commSub ⊤ L) := fun e he =>
    s16h_sl4_stab_commSub (Subgroup.mem_inf.mp (hE he)).2
  rw [← card_autSub_mul (A := E) (U := commSub ⊤ L) hEU]
  exact Nat.mul_le_mul_right _ (by simpa using hDle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
