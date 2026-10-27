module

public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSG.Timmesfeld.Orders.ClassicalLinearThree
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.Ch1Four

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

section NS

variable {X : Type} [Group X] [Finite X]

theorem ns_le_three_of_central (hperf : Group.IsPerfect X) (Z0 : Subgroup X) [Z0.Normal]
    (hZ : Z0 ≤ Subgroup.center X) (hZ3 : Nat.card Z0 ≤ 3) (hs : IsSimpleGroup (X ⧸ Z0)) :
    ∀ n, NSof X n → n ≤ 3 := by
  rintro n ⟨N, hN, hne, rfl⟩
  have hmap : (N.map (QuotientGroup.mk' Z0)).Normal := hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z0)) with h | h
  · have hle : N ≤ Z0 := by
      intro x hx
      have : QuotientGroup.mk' Z0 x ∈ N.map (QuotientGroup.mk' Z0) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    exact (Subgroup.card_le_of_le hle).trans hZ3
  · exfalso
    apply hne
    have hdec : ∀ x : X, ∃ n ∈ N, ∃ z ∈ Z0, x = n * z := by
      intro x
      have : QuotientGroup.mk' Z0 x ∈ N.map (QuotientGroup.mk' Z0) := by rw [h]; trivial
      obtain ⟨n, hn, hnx⟩ := this
      refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnx
      exact hnx
    have hmk : ∀ a b : X, (QuotientGroup.mk' N a) * QuotientGroup.mk' N b =
        QuotientGroup.mk' N b * QuotientGroup.mk' N a := by
      intro a b
      obtain ⟨n1, hn1, z1, hz1, rfl⟩ := hdec a
      obtain ⟨n2, hn2, z2, hz2, rfl⟩ := hdec b
      have e1 : QuotientGroup.mk' N n1 = 1 := (QuotientGroup.eq_one_iff n1).mpr hn1
      have e2 : QuotientGroup.mk' N n2 = 1 := (QuotientGroup.eq_one_iff n2).mpr hn2
      have hc : z1 * z2 = z2 * z1 := (Subgroup.mem_center_iff.mp (hZ hz1) z2).symm
      simp only [map_mul, e1, e2, one_mul]
      rw [← map_mul, ← map_mul, hc]
    have hcomm : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hmk a b
    have htop : ⁅(⊤ : Subgroup X), ⊤⁆ = ⊤ := hperf.commutator_eq_top
    exact eq_top_iff.mpr (htop ▸ hcomm)

omit [Finite X] in
theorem ns_le_three_of_simple (hs : IsSimpleGroup X) : ∀ n, NSof X n → n ≤ 3 := by
  rintro n ⟨N, hN, hne, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.card_bot]
    norm_num
  · exact absurd h hne

theorem ns_le_three_of_quasisimple (hq : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) ≤ 3) : ∀ n, NSof X n → n ≤ 3 :=
  ns_le_three_of_central hq.1 (Subgroup.center X) le_rfl h3 hq.2.1

theorem false_of_perfect_card_two_three (hperf : Group.IsPerfect X) [Nontrivial X] {a b : ℕ}
    (hc : Nat.card X = 2 ^ a * 3 ^ b) : False := by
  have := Fintype.ofFinite X
  have hs : Group.IsSolvable X :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hc])
  exact Group.IsPerfect.not_isSolvable X hs

end NS

section Orders

theorem gcd_three_eq (x : ℕ) : Nat.gcd 3 x = 1 ∨ (Nat.gcd 3 x = 3 ∧ 3 ∣ x) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 x) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, h ▸ Nat.gcd_dvd_right 3 x⟩

theorem card_psl3_mul {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
  CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd

theorem toNat_sq_sub_neg_one {q : ℕ} (hq : 1 ≤ q) :
    (((q : ℤ) ^ 2 - (-1) ^ 2).toNat) = q ^ 2 - 1 := by
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  rw [show ((-1 : ℤ)) ^ 2 = 1 by norm_num, show ((q : ℤ) ^ 2 - 1) = ((q ^ 2 - 1 : ℕ) : ℤ) by
    push_cast [this]; ring, Int.toNat_natCast]

theorem toNat_cube_sub_neg_one (q : ℕ) : (((q : ℤ) ^ 3 - (-1) ^ 3).toNat) = q ^ 3 + 1 := by
  rw [show ((-1 : ℤ)) ^ 3 = -1 by norm_num, show ((q : ℤ) ^ 3 - -1) = ((q ^ 3 + 1 : ℕ) : ℤ) by
    push_cast; ring, Int.toNat_natCast]

theorem card_psu3_mul {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
  CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hf hK

theorem card_sl3 {K : Type} [Field K] [Finite K] :
    Nat.card (StatedSL 3 K) = Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three K

theorem card_su3 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedSU 3 (p ^ f) K) = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (K := K) (p := p) (f := f) hK
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hK, mul_assoc]

theorem isPSL_three_two_of_isSL3 {X : Type} [Group X] (h : IsSL3 2 X) : IsPSL 3 2 1 X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hu : ∀ c : Kˣ, c = 1 := by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun c => Subsingleton.elim c 1
  have hbot : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
    obtain ⟨c, hc⟩ := hg
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [← hc, hu c, map_one]
    rfl
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, K, inferInstance,
    inferInstance, by rw [hK, pow_one],
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm⟩⟩

end Orders

section List

variable {X : Type} [Group X]

theorem listNum_of_card_fix {m : ℕ} (h : Nat.card X = m) (hm : FixShape m) :
    ListNum (Nat.card X) (NSof X) := by
  rw [h]
  exact Or.inr (Or.inl hm)

theorem listNum_of_c2Shape (h : C2Shape (Nat.card X)) : ListNum (Nat.card X) (NSof X) :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem listNum_hat7 [Finite X] (h : IsHat X (alternatingGroup (Fin 7))) :
    ListNum (Nat.card X) (NSof X) := by
  have hc : Nat.card X = 7560 := by rw [card_of_isHat' h, card_alt7 ⟨MulEquiv.refl _⟩]
  have hNS := ns_le_three_of_quasisimple h.1 h.2.1.le
  rw [hc]
  exact Or.inl ⟨fixShapeC_hatA7, hNS⟩

theorem listNum_l2sq {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (h : IsPSL 2 r 2 X) :
    ListNum (Nat.card X) (NSof X) := by
  have hodd := hr.odd_of_ne_two (by omega)
  have hev : 2 ∣ r ^ 2 - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)
  have hc : 2 * Nat.card X = r ^ 2 * (r ^ 4 - 1) := by
    rw [card_of_isPSL' (by norm_num) h, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one,
      Finset.Icc_self, Finset.prod_singleton, ← pow_mul, Nat.gcd_eq_left hev]
    have h4 : 2 ∣ r ^ 4 - 1 := by
      rw [show r ^ 4 - 1 = (r ^ 2 - 1) * (r ^ 2 + 1) from four_sub_one_eq' r hr.one_lt.le]
      exact hev.mul_right _
    exact Nat.mul_div_cancel' (h4.mul_left _)
  exact Or.inr (Or.inr (Or.inl ⟨⟨r, hr, five_le_of_prime hr hr3, hc⟩,
    ns_le_three_of_simple (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 r 2 h).2⟩))

theorem listNum_psl3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 3 p 1 X) :
    ListNum (Nat.card X) (NSof X) := by
  have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 p 1 h).2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hc := card_psl3_mul (K := K)
  rw [hK, pow_one, ← Nat.card_congr e.toEquiv] at hc
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p, _, _, hp, h3, hc, Or.inl ⟨rfl, gcd_three_eq _⟩⟩,
    ns_le_three_of_simple hs⟩)))

theorem listNum_psu3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSU 3 p 1 X) :
    ListNum (Nat.card X) (NSof X) := by
  have hs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 p 1 h).2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hc := card_psu3_mul hp le_rfl hK
  rw [← Nat.card_congr e.toEquiv, pow_one] at hc
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p, _, _, hp, h3, hc, Or.inr ⟨rfl, gcd_three_eq _⟩⟩,
    ns_le_three_of_simple hs⟩)))

theorem ns_le_three_of_isSL3 {q : ℕ} (h : IsSL3 q X) : ∀ n, NSof X n → n ≤ 3 := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
  have hq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl
  have h3 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ 3 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center K 3 (by norm_num)]
    exact Nat.gcd_le_left _ (by norm_num)
  intro n hn
  exact ns_le_three_of_quasisimple hq h3 n
    (hn.of_mulEquiv (e.trans (specialLinearGroupEquivStatedSL 3 K).symm))

theorem listNum_sl3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSL3 p X) :
    ListNum (Nat.card X) (NSof X) := by
  have hNS := ns_le_three_of_isSL3 h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hc : Nat.card X * 1 = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rw [mul_one, Nat.card_congr e.toEquiv, card_sl3, hK]
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p, 1, _, hp, h3, hc, Or.inl ⟨rfl, Or.inl rfl⟩⟩,
    hNS⟩)))

theorem listNum_su3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSU3 p X) :
    ListNum (Nat.card X) (NSof X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have h1 := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := 1) (n := 3) hK1 le_rfl (fun h => hp2 (by simpa using congrArg Prod.snd h))
  have h2 := (CFSG.LinearGroups.unitary_scalar_kernel hp hK1 (n := 3) (by norm_num)).2.2
  rw [← h1.2] at h2
  have hc := card_su3 hp hK1
  rw [pow_one] at h1 h2 hc
  have hZ : Nat.card (Subgroup.center (StatedSU 3 p K)) ≤ 3 := by
    rw [h2]
    exact Nat.gcd_le_left _ (by norm_num)
  have hNS : ∀ n, NSof X n → n ≤ 3 := fun n hn =>
    ns_le_three_of_quasisimple h1.1 hZ n (hn.of_mulEquiv e)
  have hc' : Nat.card X * 1 = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
    rw [mul_one, Nat.card_congr e.toEquiv, hc]
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p, 1, _, hp, h3, hc', Or.inr ⟨rfl, Or.inl rfl⟩⟩,
    hNS⟩)))

theorem listNum_l52 (h : IsPSL 5 2 1 X) : ListNum (Nat.card X) (NSof X) :=
  listNum_of_card_fix (by rw [card_of_isPSL' (by norm_num) h]; decide) fixShape_l52

theorem listNum_u3_two [Finite X] (hperf : Group.IsPerfect X) {n : ℕ}
    (h : IsPSU 3 2 n X ∨ IsSU3 (2 ^ n) X) : ListNum (Nat.card X) (NSof X) := by
  rcases h with h | ⟨K, _, _, hK, ⟨e⟩⟩
  · obtain ⟨⟨-, hn1, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
    have hn2 : 2 ≤ n := by
      by_contra hlt
      exact hne (by rw [show n = 1 by omega, pow_one])
    have hm := card_psu3_mul Nat.prime_two hn1 hK
    rw [← Nat.card_congr e.toEquiv] at hm
    exact listNum_of_c2Shape (c2Shape_U hn2 (gcd_three_eq _) hm)
  · have hn1 : 1 ≤ n := by
      by_contra h0
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, show n = 0 by omega] at h1
      norm_num at h1
    have hc := card_su3 Nat.prime_two hK
    rw [← Nat.card_congr e.toEquiv] at hc
    rcases Nat.lt_or_ge n 2 with hn | hn2
    · have hc' : Nat.card X = 2 ^ 3 * 3 ^ 3 := by
        rw [hc, show n = 1 by omega]
        norm_num
      have : Nontrivial X := by
        rw [← Finite.one_lt_card_iff_nontrivial, hc']
        norm_num
      exact (false_of_perfect_card_two_three hperf hc').elim
    · exact listNum_of_c2Shape (c2Shape_U hn2 (Or.inl rfl) (by rw [mul_one, hc]))

theorem listNum_rank2
    (h : IsRank2LieChar2 X) (h1 : ¬ IsPSL 3 2 1 X) (h2 : ¬ IsPSL 3 2 2 X) :
    ListNum (Nat.card X) (NSof X) := by
  rcases h with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨-, hf, h⟩⟩ | h
  ·
    have hf3 : 3 ≤ f := by
      by_contra hlt
      interval_cases f
      · exact h1 h
      · exact h2 h
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hm := card_psl3_mul (K := K)
    rw [hK, ← Nat.card_congr e.toEquiv] at hm
    refine listNum_of_c2Shape (c2Shape_L (by omega) ?_ hm)
    rcases gcd_three_eq (2 ^ f - 1) with hd | ⟨hd, h3⟩
    · exact Or.inl hd
    · exact Or.inr ⟨hd, hf3, h3⟩
  ·
    rcases Nat.lt_or_ge f 2 with hlt | hf2
    · rw [show f = 1 by omega, pow_one] at h
      exact (h1 (isPSL_three_two_of_isSL3 h)).elim
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
      refine listNum_of_c2Shape (c2Shape_L hf2 (Or.inl rfl) ?_)
      rw [mul_one, Nat.card_congr e.toEquiv, card_sl3, hK]
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := K) 2
    rw [hK, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num),
      ← Nat.card_congr e.toEquiv] at hc
    simp only [Nat.reducePow, Nat.reduceMul] at hc
    exact listNum_of_c2Shape (c2Shape_Sp hf hc)
  ·
    have hc := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 h.2
    refine listNum_of_c2Shape (c2Shape_G2 hf ?_)
    rw [hc, CFSG.Open.ordG2, mul_assoc]
  ·
    have hc := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hf h.2
    refine listNum_of_c2Shape (c2Shape_D4 hf ?_)
    rw [hc, CFSG.Open.ordTrialityD4]
    simp only [mul_assoc]
  ·
    have hc := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h
    refine listNum_of_c2Shape (c2Shape_F4 hf ?_)
    rw [hc, CFSG.Open.ordTwistedF4]
    simp only [mul_assoc]
  ·
    have hc := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits h
    exact listNum_of_card_fix (hc.trans (by decide)) fixShape_tits

theorem listNum_spor {s : TauCeti.SporadicName} {m : ℕ} (h : IsSporadic s X)
    (hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) = m) (hm : FixShape m) :
    ListNum (Nat.card X) (NSof X) := by
  obtain ⟨e⟩ := h
  exact listNum_of_card_fix ((Nat.card_congr e.toEquiv).trans hc) hm

theorem listNum_j1 (h : IsSporadic .J1 X) :
    ListNum (Nat.card X) (NSof X) := by
  obtain ⟨e⟩ := h
  have hc : Nat.card X = 175560 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
    CFSG.Sporadic.J1.isSimpleGroup_J1
  have hs : IsSimpleGroup X := e.isSimpleGroup
  rw [hc]
  exact Or.inl ⟨fixShapeC_j1, ns_le_three_of_simple hs⟩

theorem listNum_of_a128FourList
    [Finite X] (hperf : Group.IsPerfect X) (h : A128FourList X) :
    ListNum (Nat.card X) (NSof X) := by
  rcases h with h | ⟨r, hr, hr3, h⟩ | ⟨s, p, hp, hp2, h⟩ | h | h | h | h | h | h | h | h | h | h |
    ⟨n, h⟩ | ⟨h, h1, h2⟩
  · exact listNum_hat7 h
  · exact listNum_l2sq hr hr3 h
  · cases s
    · rcases h with h | h
      · exact listNum_psu3 hp hp2 h
      · exact listNum_su3 hp hp2 h
    · rcases h with h | h
      · exact listNum_psl3 hp hp2 h
      · exact listNum_sl3 hp hp2 h
  · exact listNum_spor h CFSG.Sporadic.Mathieu.card_M11 fixShape_m11
  · exact listNum_spor h CFSG.Sporadic.Mathieu.card_M12 fixShape_m12
  · exact listNum_spor h CFSG.Sporadic.Schreier.m23_card fixShape_m23
  · exact listNum_j1 h
  · exact listNum_spor h CFSG.Sporadic.J2.card_J2 fixShape_j2
  · exact listNum_spor h CFSG.Sporadic.J4.card_J4 fixShape_j4
  · exact listNum_spor h CFSG.Sporadic.HS.card_HS fixShape_hs
  · exact listNum_spor h CFSG.Sporadic.He.card_He fixShape_he
  · exact listNum_spor h CFSG.Sporadic.Ru.card_Ru fixShape_ru
  · exact listNum_l52 h
  · exact listNum_u3_two hperf h
  · exact listNum_rank2 h h1 h2

end List

end CFSG.Quasithin.Ch1Four
