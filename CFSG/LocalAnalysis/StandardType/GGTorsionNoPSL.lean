module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetExc
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

section TorsionNoPSL

private theorem tn_ordA_one {a : ℕ} (ha : 1 ≤ a) :
    CFSG.Open.ordA 1 (2 ^ a) = 2 ^ a * (2 ^ (2 * a) - 1) := by
  have hodd : Odd (2 ^ a - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have hgcd : Nat.gcd 2 (2 ^ a - 1) = 1 := hodd.coprime_two_left
  rw [CFSG.Open.ordA, show (1 + 1 : ℕ) = 2 from rfl, hgcd, Nat.div_one,
    Finset.Icc_self, Finset.prod_singleton,
    show 1 * 2 / 2 = 1 by norm_num, pow_one]
  rw [show (2 ^ a) ^ 2 = 2 ^ (2 * a) by rw [← pow_mul, Nat.mul_comm]]

private theorem tn_ordE8_le (n : ℕ) : CFSG.Open.ordE8 (2 ^ n) ≤ 2 ^ (248 * n) := by
  set q := 2 ^ n with hq
  calc CFSG.Open.ordE8 q
      = q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
          (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) := by
        rw [CFSG.Open.ordE8]
    _ ≤ q ^ 120 * q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
        gcongr
        all_goals exact Nat.sub_le _ _
    _ = q ^ 248 := by ring
    _ = 2 ^ (248 * n) := by rw [hq, ← pow_mul, Nat.mul_comm]

private theorem tn_ordF4_le (n : ℕ) : CFSG.Open.ordF4 (2 ^ n) ≤ 2 ^ (52 * n) := by
  set q := 2 ^ n with hq
  calc CFSG.Open.ordF4 q
      = q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
        rw [CFSG.Open.ordF4]
    _ ≤ q ^ 24 * q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr
        all_goals exact Nat.sub_le _ _
    _ = q ^ 52 := by ring
    _ = 2 ^ (52 * n) := by rw [hq, ← pow_mul, Nat.mul_comm]

private theorem tn_ordTwistedF4_le (n : ℕ) (hn : 1 ≤ n) :
    CFSG.Open.ordTwistedF4 (2 ^ n) ≤ 2 ^ (28 * n) := by
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := by rw [hq]; simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
  have h61 : q ^ 6 + 1 ≤ q ^ 7 := by
    calc q ^ 6 + 1 ≤ q ^ 6 + q ^ 6 := Nat.add_le_add_left (Nat.one_le_pow 6 q (by omega)) _
      _ = 2 * q ^ 6 := by ring
      _ ≤ q * q ^ 6 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 7 := by ring
  have h31 : q ^ 3 + 1 ≤ q ^ 4 := by
    calc q ^ 3 + 1 ≤ q ^ 3 + q ^ 3 := Nat.add_le_add_left (Nat.one_le_pow 3 q (by omega)) _
      _ = 2 * q ^ 3 := by ring
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 4 := by ring
  calc CFSG.Open.ordTwistedF4 q
      = q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := by
        rw [CFSG.Open.ordTwistedF4]
    _ ≤ q ^ 12 * q ^ 7 * q ^ 4 * q ^ 4 * q := by
        gcongr
        all_goals first | exact h61 | exact h31 | exact Nat.sub_le _ _
    _ = q ^ 28 := by ring
    _ = 2 ^ (28 * n) := by rw [hq, ← pow_mul, Nat.mul_comm]

private theorem tn_ordTits_lt : CFSG.Open.ordTits < 2 ^ 25 := by
  rw [CFSG.Open.ordTits]; norm_num

private theorem tn_two_pow_lt_ordA_one {E a : ℕ} (ha1 : 1 ≤ a) (haE : a ≤ E)
    (hE : E + 1 < 3 * a) : 2 ^ E < CFSG.Open.ordA 1 (2 ^ a) := by
  rw [tn_ordA_one ha1]
  have hmul : 2 ^ a * (2 ^ (2 * a) - 1) = 2 ^ (3 * a) - 2 ^ a := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add,
      show a + 2 * a = 3 * a by ring]
  rw [hmul]
  refine (Nat.lt_sub_iff_add_lt).mpr ?_
  have hle : 2 ^ a ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) haE
  have hsum : 2 ^ E + 2 ^ a ≤ 2 ^ E + 2 ^ E := Nat.add_le_add_left hle _
  have hdouble : 2 ^ E + 2 ^ E = 2 ^ (E + 1) := by rw [← two_mul, pow_succ']
  have hlt : 2 ^ (E + 1) < 2 ^ (3 * a) := Nat.pow_lt_pow_right (by norm_num) hE
  exact lt_of_le_of_lt (hsum.trans_eq hdouble) hlt

private theorem tn_E8_ordA_one_ne {n a : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a)
    (h : CFSG.Open.ordE8 (2 ^ n) = CFSG.Open.ordA 1 (2 ^ a)) : False := by
  have hX := CFSG.Timmesfeld.Orders.profile_ordE8 hn
  have hA := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := a) (by omega) ha
  rw [h] at hX
  have hNa : n * 120 = a := by simpa using (hX.transfer hA).1
  have hlt : 2 ^ (248 * n) < CFSG.Open.ordA 1 (2 ^ a) :=
    tn_two_pow_lt_ordA_one ha (by omega) (by omega)
  have hbad : CFSG.Open.ordE8 (2 ^ n) < CFSG.Open.ordA 1 (2 ^ a) :=
    lt_of_le_of_lt (tn_ordE8_le n) hlt
  rw [h] at hbad
  exact (lt_irrefl _) hbad

private theorem tn_F4_ordA_one_ne {n a : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a)
    (h : CFSG.Open.ordF4 (2 ^ n) = CFSG.Open.ordA 1 (2 ^ a)) : False := by
  have hX := CFSG.Timmesfeld.Orders.profile_ordF4 hn
  have hA := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := a) (by omega) ha
  rw [h] at hX
  have hNa : n * 24 = a := by simpa using (hX.transfer hA).1
  have hlt : 2 ^ (52 * n) < CFSG.Open.ordA 1 (2 ^ a) :=
    tn_two_pow_lt_ordA_one ha (by omega) (by omega)
  have hbad : CFSG.Open.ordF4 (2 ^ n) < CFSG.Open.ordA 1 (2 ^ a) :=
    lt_of_le_of_lt (tn_ordF4_le n) hlt
  rw [h] at hbad
  exact (lt_irrefl _) hbad

private theorem tn_twF4_ordA_one_ne {n a : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a)
    (h : CFSG.Open.ordTwistedF4 (2 ^ n) = CFSG.Open.ordA 1 (2 ^ a)) : False := by
  have hX := CFSG.Timmesfeld.Orders.profile_ordTwistedF4 hn
  have hA := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := a) (by omega) ha
  rw [h] at hX
  have hNa : n * 12 = a := by simpa using (hX.transfer hA).1
  have hlt : 2 ^ (28 * n) < CFSG.Open.ordA 1 (2 ^ a) :=
    tn_two_pow_lt_ordA_one ha (by omega) (by omega)
  have hbad : CFSG.Open.ordTwistedF4 (2 ^ n) < CFSG.Open.ordA 1 (2 ^ a) :=
    lt_of_le_of_lt (tn_ordTwistedF4_le n hn) hlt
  rw [h] at hbad
  exact (lt_irrefl _) hbad

private theorem tn_Tits_ordA_one_ne {a : ℕ} (ha : 1 ≤ a)
    (h : CFSG.Open.ordTits = CFSG.Open.ordA 1 (2 ^ a)) : False := by
  have hodd : Odd 8775 := by decide
  obtain ⟨r, hr, hAr⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := a) (by omega) ha).two
  have hAr' : CFSG.Open.ordA 1 (2 ^ a) = 2 ^ a * r := by simpa using hAr
  have heq : 2 ^ 11 * 8775 = 2 ^ a * r := by
    rw [← CFSG.Timmesfeld.Orders.ordTits_eq, h, hAr']
  have h11 : 11 = a := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd hr heq
  subst h11
  have hlt : CFSG.Open.ordTits < CFSG.Open.ordA 1 (2 ^ 11) :=
    lt_of_lt_of_le tn_ordTits_lt
      (le_of_lt (tn_two_pow_lt_ordA_one (a := 11) (E := 25) (by norm_num) (by norm_num)
        (by norm_num)))
  rw [h] at hlt
  exact (lt_irrefl _) hlt

theorem ggTorsion_not_marking_psl
    {J : Type} [Group J] {d : ℕ} (hd : 2 ≤ d) {D : Type} [Field D] [Finite D] [CharP D 2]
    (e : J ⧸ Subgroup.center J ≃*
      Matrix.SpecialLinearGroup (Fin d) D ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) :
    ¬ LargeEvenMarking J fun lab _ _ _ _ _ => GGL45TorsionTag lab := by
  intro h
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, hP, hM⟩ :=
    largeEvenMarking_exists_markedModel h
  obtain ⟨t, l, n⟩ := lab
  have hP' : t = .E8 ∨ t = .F4 ∨ t = .twF4 ∨ t = .twF4der := by
    simpa only [GGL45TorsionTag] using hP
  have hRJ : Nat.card R = Nat.card (J ⧸ Subgroup.center J) := (Nat.card_congr θ.toEquiv).symm
  have hJSL : Nat.card (J ⧸ Subgroup.center J) =
      Nat.card (Matrix.SpecialLinearGroup (Fin d) D ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) := Nat.card_congr e.toEquiv
  obtain ⟨a, ha, hDa⟩ : ∃ a : ℕ, 1 ≤ a ∧ Nat.card D = 2 ^ a := by
    haveI : Fintype D := Fintype.ofFinite D
    obtain ⟨k, -, hk⟩ := FiniteField.card D 2
    have h2 : 2 ≤ Fintype.card D := by
      haveI : Nontrivial D := inferInstance
      exact Fintype.one_lt_card
    refine ⟨k, ?_, ?_⟩
    · exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [← hk]; simpa using h2)
    · rw [Nat.card_eq_fintype_card]; exact hk
  have hPSL : Nat.card (Matrix.SpecialLinearGroup (Fin d) D ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) =
      Nat.card D ^ (d * (d - 1) / 2) *
        (∏ j ∈ Finset.Icc 2 d, (Nat.card D ^ j - 1)) / Nat.gcd d (Nat.card D - 1) :=
    (Nat.card_congr
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d D).toEquiv).trans
      (CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega))
  have hordA : Nat.card (Matrix.SpecialLinearGroup (Fin d) D ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) = CFSG.Open.ordA (d - 1) (2 ^ a) := by
    rw [hPSL, hDa, CFSG.Open.ordA, show (d - 1) + 1 = d by omega,
      Nat.mul_comm d (d - 1)]
  have hmain : Nat.card R = CFSG.Open.ordA (d - 1) (2 ^ a) := hRJ.trans (hJSL.trans hordA)
  rcases hP' with rfl | rfl | rfl | rfl
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordE8 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · have hd2 : d - 1 = 1 := by omega
      rw [hd2] at hmain
      exact tn_E8_ordA_one_ne hn ha (hR.symm.trans hmain)
    · have hr : 2 ≤ d - 1 := by omega
      exact CFSG.SeitzReduction.LinearPilot.ordE8_ne_ordA hn hr ha (hR.symm.trans hmain)
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordF4 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · have hd2 : d - 1 = 1 := by omega
      rw [hd2] at hmain
      exact tn_F4_ordA_one_ne hn ha (hR.symm.trans hmain)
    · have hr : 2 ≤ d - 1 := by omega
      exact CFSG.SeitzReduction.LinearPilot.ordF4_ne_ordA hn hr ha (hR.symm.trans hmain)
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordTwistedF4 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · have hd2 : d - 1 = 1 := by omega
      rw [hd2] at hmain
      exact tn_twF4_ordA_one_ne hn ha (hR.symm.trans hmain)
    · have hr : 2 ≤ d - 1 := by omega
      exact CFSG.SeitzReduction.LinearPilot.ordTwistedF4_ne_ordA hn hr ha (hR.symm.trans hmain)
  ·
    dsimp only [LargeEvenInLambda2] at hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordTits :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · have hd2 : d - 1 = 1 := by omega
      rw [hd2] at hmain
      exact tn_Tits_ordA_one_ne ha (hR.symm.trans hmain)
    · have hr : 2 ≤ d - 1 := by omega
      exact CFSG.SeitzReduction.LinearPilot.ordTits_ne_ordA hr ha (hR.symm.trans hmain)

end TorsionNoPSL

end CFSG.StandardType
