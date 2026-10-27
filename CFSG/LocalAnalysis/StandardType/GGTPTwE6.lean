module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_card_twA {n : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twA, 5, n⟩ R) : Nat.card R = CFSG.Open.ordTwistedA 5 (2 ^ n) := by
  have hraw : CFSG.StandardType.LargeEvenRawDatum ⟨.twA, 5, n⟩
      (fun R' _ _ _ => Nonempty (R ≃* R')) := h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, _, _, hK, hQ⟩ := hraw
  obtain ⟨e⟩ := hQ
  have hn : 1 ≤ n := by
    by_contra h
    push Not at h
    have hn0 : n = 0 := by omega
    have h2 : 2 ≤ Nat.card K := by
      haveI : Nontrivial K := inferInstance
      have := Finite.one_lt_card (α := K)
      omega
    rw [hn0] at hK
    norm_num at hK
    omega
  have hadm : StatedLieAdmissible .PSU (5 + 1) 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, by simp⟩
  have hSC : StatedClassicalModel
      (LargeEvenProj (LargeEvenSUGroup (Fin (5 + 1)) K (2 ^ n))) .PSU (5 + 1) 2 n :=
    statedClassicalModel_unitary (5 + 1) n hK hadm
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hSC).2.1 rfl
  rw [Nat.card_congr e.toEquiv]
  simpa using hcard

private theorem ggTP_card_twE6
    {n : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twE6, 0, n⟩ R) : Nat.card R = CFSG.Open.ordTwistedE6 (2 ^ n) := by
  have hraw : CFSG.StandardType.LargeEvenRawDatum ⟨.twE6, 0, n⟩
      (fun R' _ _ _ => Nonempty (R ≃* R')) := h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeTwisted] at hraw
  obtain ⟨K, _, _, hK, hQ⟩ := hraw
  obtain ⟨e⟩ := hQ
  have hn : 1 ≤ n := by
    by_contra h
    push Not at h
    have hn0 : n = 0 := by omega
    have h2 : 2 ≤ Nat.card K := by
      haveI : Nontrivial K := inferInstance
      have := Finite.one_lt_card (α := K)
      omega
    rw [hn0] at hK
    norm_num at hK
    omega
  have hTM : TwistedChevalleyModel
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))
      .E6 (2 ^ n) := twistedChevalleyModel_largeEven .E6 hK
  have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_E6_two hn hTM
  rw [Nat.card_congr e.toEquiv]
  exact hcard

private theorem ggTP_card_centerQuot_le {G : Type} [Group G] [Finite G] {J K' : Subgroup G}
    (hJK : J ≤ K') :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
  let ZK : Subgroup ↥K' := Subgroup.center ↥K'
  let A : Subgroup ↥J := ZK.comap (Subgroup.inclusion hJK)
  haveI hAn : A.Normal := Subgroup.Normal.comap (inferInstance : ZK.Normal) (Subgroup.inclusion hJK)
  have hAZ : A ≤ Subgroup.center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx' : Subgroup.inclusion hJK x ∈ ZK := hx
    rw [Subgroup.mem_center_iff] at hx'
    simpa only [Subgroup.coe_mul, Subgroup.coe_inclusion] using
      congrArg (Subtype.val : ↥K' → G) (hx' (Subgroup.inclusion hJK y))
  haveI : Finite (↥J ⧸ A) :=
    Finite.of_surjective (QuotientGroup.mk : ↥J → ↥J ⧸ A) QuotientGroup.mk_surjective
  have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card (↥J ⧸ A) := by
    refine Nat.card_le_card_of_surjective
      (QuotientGroup.map A (Subgroup.center ↥J) (MonoidHom.id ↥J) (by simpa using hAZ)) ?_
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, by simp [QuotientGroup.map_mk]⟩
  let φ : ↥J →* (↥K' ⧸ ZK) := (QuotientGroup.mk' ZK).comp (Subgroup.inclusion hJK)
  have hφker : φ.ker = A := by
    rw [show φ = (QuotientGroup.mk' ZK).comp (Subgroup.inclusion hJK) from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  haveI : Finite (↥K' ⧸ ZK) :=
    Finite.of_surjective (QuotientGroup.mk : ↥K' → ↥K' ⧸ ZK) QuotientGroup.mk_surjective
  have h2 : Nat.card (↥J ⧸ A) ≤ Nat.card (↥K' ⧸ ZK) := by
    rw [← hφker]
    calc Nat.card (↥J ⧸ φ.ker) = Nat.card φ.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
      _ ≤ Nat.card (↥K' ⧸ ZK) :=
          Nat.card_le_card_of_injective (Subgroup.subtype φ.range) (Subgroup.subtype_injective _)
  exact h1.trans h2

private theorem ggTP_toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have h : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [this]; ring
  rw [h, Int.toNat_natCast]

private theorem ggTP_toNat_odd {q i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  have h : ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private theorem ggTP_ordTwistedA_five_mul {Q : ℕ} (hQ : 1 ≤ Q) :
    CFSG.Open.ordTwistedA 5 Q * Nat.gcd 6 (Q + 1) =
      Q ^ 15 * ((Q ^ (2 * 1) - 1) * ((Q ^ 3 + 1) *
        ((Q ^ (2 * 2) - 1) * ((Q ^ 5 + 1) * (Q ^ (2 * 3) - 1))))) := by
  have h3 : Q + 1 ∣ Q ^ 3 + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow Q 1 (by decide : Odd 3)
  rw [CFSG.Open.ordTwistedA, show Finset.Icc 2 (5 + 1) = ({2, 3, 4, 5, 6} : Finset ℕ) from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num), ggTP_toNat_even hQ (by decide), ggTP_toNat_odd (by decide),
    ggTP_toNat_even hQ (by decide), ggTP_toNat_odd (by decide), ggTP_toNat_even hQ (by decide),
    show 5 * (5 + 1) / 2 = 15 from rfl, show (5 : ℕ) + 1 = 6 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _) _))

private theorem ggTP_numTwistedE6_lt {q : ℕ} (hq : 2 ≤ q) :
    CFSG.SeitzReduction.E6Pilot.numTwistedE6 q < q ^ 80 := by
  have h12 : q ^ 12 - 1 < q ^ 12 := Nat.sub_lt (pow_pos (by omega) 12) (by norm_num)
  have h9 : q ^ 9 + 1 < 2 * q ^ 9 := by
    have : 1 < q ^ 9 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h8 : q ^ 8 - 1 < q ^ 8 := Nat.sub_lt (pow_pos (by omega) 8) (by norm_num)
  have h6 : q ^ 6 - 1 < q ^ 6 := Nat.sub_lt (pow_pos (by omega) 6) (by norm_num)
  have h5 : q ^ 5 + 1 < 2 * q ^ 5 := by
    have : 1 < q ^ 5 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h2 : q ^ 2 - 1 < q ^ 2 := Nat.sub_lt (pow_pos (by omega) 2) (by norm_num)
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hpow : 4 * q ^ 78 ≤ q ^ 80 := by
    calc 4 * q ^ 78 ≤ q ^ 2 * q ^ 78 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 80 := by ring
  rw [CFSG.SeitzReduction.E6Pilot.numTwistedE6]
  calc q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
      < q ^ 36 * q ^ 12 * (2 * q ^ 9) * q ^ 8 * q ^ 6 * (2 * q ^ 5) * q ^ 2 := by gcongr
    _ = 4 * q ^ 78 := by ring
    _ ≤ q ^ 80 := hpow

private theorem ggTP_pow_succ_sub_one_ge {Q m : ℕ} (hQ : 2 ≤ Q) :
    Q ^ m ≤ Q ^ (m + 1) - 1 := by
  have hm1 : 1 ≤ Q ^ m := Nat.one_le_pow _ _ (by omega)
  have h2 : Q ^ m + 1 ≤ 2 * Q ^ m := by omega
  have h3 : 2 * Q ^ m ≤ Q ^ (m + 1) := by
    calc 2 * Q ^ m ≤ Q * Q ^ m := Nat.mul_le_mul_right _ hQ
      _ = Q ^ (m + 1) := by rw [pow_succ]; ring
  have : Q ^ m + 1 ≤ Q ^ (m + 1) := le_trans h2 h3
  omega

private theorem ggTP_numA5_ge {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 32 ≤ Q ^ 15 * ((Q ^ (2 * 1) - 1) * ((Q ^ 3 + 1) * ((Q ^ (2 * 2) - 1) *
      ((Q ^ 5 + 1) * (Q ^ (2 * 3) - 1))))) := by
  have h1 : Q ≤ Q ^ (2 * 1) - 1 := by simpa using ggTP_pow_succ_sub_one_ge (m := 1) hQ
  have h2 : Q ^ 3 ≤ Q ^ 3 + 1 := by omega
  have h3 : Q ^ 3 ≤ Q ^ (2 * 2) - 1 := by
    simpa using ggTP_pow_succ_sub_one_ge (m := 3) hQ
  have h4 : Q ^ 5 ≤ Q ^ 5 + 1 := by omega
  have h5 : Q ^ 5 ≤ Q ^ (2 * 3) - 1 := by
    simpa using ggTP_pow_succ_sub_one_ge (m := 5) hQ
  have hprod : Q * (Q ^ 3 * (Q ^ 3 * (Q ^ 5 * Q ^ 5))) ≤
      (Q ^ (2 * 1) - 1) * ((Q ^ 3 + 1) * ((Q ^ (2 * 2) - 1) *
        ((Q ^ 5 + 1) * (Q ^ (2 * 3) - 1)))) := by
    gcongr
  calc Q ^ 32 = Q ^ 15 * (Q * (Q ^ 3 * (Q ^ 3 * (Q ^ 5 * Q ^ 5)))) := by ring
    _ ≤ Q ^ 15 * ((Q ^ (2 * 1) - 1) * ((Q ^ 3 + 1) * ((Q ^ (2 * 2) - 1) *
        ((Q ^ 5 + 1) * (Q ^ (2 * 3) - 1))))) := Nat.mul_le_mul_left _ hprod

private theorem ggTP_ordTwistedA_five_gt {q : ℕ} (hq : 2 ≤ q) :
    q ^ 80 < CFSG.Open.ordTwistedA 5 (q ^ 3) := by
  have hQ1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hmul := ggTP_ordTwistedA_five_mul (Q := q ^ 3) hQ1
  have hQ2 : 2 ≤ q ^ 3 := le_trans hq (Nat.le_self_pow (by norm_num : 3 ≠ 0) q)
  have hnumA5 := ggTP_numA5_ge (Q := q ^ 3) hQ2
  have hNge : q ^ 96 ≤ (q ^ 3) ^ 15 * (((q ^ 3) ^ (2 * 1) - 1) * (((q ^ 3) ^ 3 + 1) *
      (((q ^ 3) ^ (2 * 2) - 1) * (((q ^ 3) ^ 5 + 1) * ((q ^ 3) ^ (2 * 3) - 1))))) := by
    calc q ^ 96 = (q ^ 3) ^ 32 := by rw [← pow_mul]
      _ ≤ (q ^ 3) ^ 15 * (((q ^ 3) ^ (2 * 1) - 1) * (((q ^ 3) ^ 3 + 1) *
          (((q ^ 3) ^ (2 * 2) - 1) * (((q ^ 3) ^ 5 + 1) *
            ((q ^ 3) ^ (2 * 3) - 1))))) := hnumA5
  have hq96 : 6 * q ^ 80 < q ^ 96 := by
    have h16 : 6 < q ^ 16 := by
      have h2 : 2 ^ 16 ≤ q ^ 16 := Nat.pow_le_pow_left hq 16
      norm_num at h2
      omega
    have h : 6 * q ^ 80 < q ^ 16 * q ^ 80 :=
      (Nat.mul_lt_mul_right (by positivity : 0 < q ^ 80)).mpr h16
    calc 6 * q ^ 80 < q ^ 16 * q ^ 80 := h
      _ = q ^ 96 := by rw [← pow_add]
  have hg : Nat.gcd 6 (q ^ 3 + 1) ≤ 6 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 6 _)
  have hgoal : q ^ 80 * Nat.gcd 6 (q ^ 3 + 1) <
      CFSG.Open.ordTwistedA 5 (q ^ 3) * Nat.gcd 6 (q ^ 3 + 1) := by
    calc q ^ 80 * Nat.gcd 6 (q ^ 3 + 1) ≤ q ^ 80 * 6 := Nat.mul_le_mul_left _ hg
      _ = 6 * q ^ 80 := by ring
      _ < q ^ 96 := hq96
      _ ≤ (q ^ 3) ^ 15 * (((q ^ 3) ^ (2 * 1) - 1) * (((q ^ 3) ^ 3 + 1) *
          (((q ^ 3) ^ (2 * 2) - 1) * (((q ^ 3) ^ 5 + 1) *
            ((q ^ 3) ^ (2 * 3) - 1))))) := hNge
      _ = CFSG.Open.ordTwistedA 5 (q ^ 3) * Nat.gcd 6 (q ^ 3 + 1) := hmul.symm
  exact Nat.lt_of_mul_lt_mul_right hgoal

private theorem ggTP_ordTwistedE6_lt_ordTwistedA_five {n' : ℕ} (hn' : 1 ≤ n') :
    CFSG.Open.ordTwistedE6 (2 ^ n') < CFSG.Open.ordTwistedA 5 (2 ^ (3 * n')) := by
  have hq : 2 ≤ 2 ^ n' := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn'
  have hnum := ggTP_numTwistedE6_lt hq
  have hmul := CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd (2 ^ n')
  have hg1 : 1 ≤ Nat.gcd 3 (2 ^ n' + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.gcd_pos_of_pos_right _ (by omega)).ne'
  have hE : CFSG.Open.ordTwistedE6 (2 ^ n') < (2 ^ n') ^ 80 :=
    calc CFSG.Open.ordTwistedE6 (2 ^ n') = CFSG.Open.ordTwistedE6 (2 ^ n') * 1 := by rw [mul_one]
      _ ≤ CFSG.Open.ordTwistedE6 (2 ^ n') * Nat.gcd 3 (2 ^ n' + 1) :=
          Nat.mul_le_mul_left _ hg1
      _ = CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ n') := hmul
      _ < (2 ^ n') ^ 80 := hnum
  have hpow : (2 : ℕ) ^ (3 * n') = (2 ^ n') ^ 3 := by rw [mul_comm 3 n', pow_mul]
  rw [hpow]
  exact hE.trans (ggTP_ordTwistedA_five_gt hq)

theorem ggTPTwE6_excl
    {G : Type} [Group G] [Finite G] {J K' : Subgroup G} (hJK : J ≤ K') {n n' : ℕ}
    (hn : n = 3 * n') (hn1 : 1 ≤ n')
    (hJ : GGHasLabel ⟨.twA, 5, n⟩ (↥J ⧸ Subgroup.center ↥J))
    (hK : GGHasLabel ⟨.twE6, 0, n'⟩ (↥K' ⧸ Subgroup.center ↥K')) : False := by
  subst n
  have hJc := ggTP_card_twA hJ
  have hKc := ggTP_card_twE6 hK
  have hle := ggTP_card_centerQuot_le hJK
  rw [hJc, hKc] at hle
  exact absurd (ggTP_ordTwistedE6_lt_ordTwistedA_five hn1) (not_lt.mpr hle)

end CFSG.StandardType

end

