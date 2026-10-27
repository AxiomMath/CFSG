module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.H13.A7Nat1238QTabA314

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def NQOrder (N : ℕ) : Prop :=
  (∃ p : ℕ, p.Prime ∧ 3 < p ∧ N = p ^ 3 * (p ^ 2 - 1)) ∨
    ∃ m : ℕ, Odd m ∧ (∀ q : ℕ, q.Prime → q ∣ m → q % 5 = 0 ∨ q % 5 = 1 ∨ q % 5 = 4) ∧
      N = 120 * m

theorem card_eq_of_isElemAbelianOfRank {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin n →
    ZMod p) ≃ (Fin n → ZMod p)), Nat.card_pi]
  simp [Nat.card_zmod]

theorem nqOrder_card {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : A36Strong L)
    (hnq : ¬ CFSG.IsQuasisimple ↥L) : NQOrder (Nat.card ↥L) := by
  obtain ⟨hconcl, hcommon, -⟩ := h
  have hF : CFSG.fittingSubgroup ↥L = CFSG.oddCore ↥L := hcommon.1
  rcases hconcl with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact absurd hc.1 hnq
  · exact absurd hc.1 hnq
  · left
    obtain ⟨p, hp, hp3, -, hE, e, ψ, hψs, hψk, -⟩ := h3
    refine ⟨p, hp, hp3, ?_⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have h2 : Nat.card (↥L ⧸ ψ.ker) = p * (p ^ 2 - 1) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv]
      exact A313.card_sl2 hp
    rw [h1, h2, hψk, card_eq_of_isElemAbelianOfRank hE]
    ring
  · right
    obtain ⟨-, -, h5, hpr⟩ := h4
    refine ⟨Nat.card (CFSG.fittingSubgroup ↥L), ?_, fun q hq hqd => ?_, ?_⟩
    · rw [hF]
      exact A312.odd_card_oddCore _
    · rcases (hpr q hq hqd).1 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (by rw [h])
    · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.fittingSubgroup ↥L),
        A313.IsSL2.card_eq Nat.prime_five h5]
      norm_num

theorem oddCore_facts {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : A36Strong L)
    (hnq : ¬ CFSG.IsQuasisimple ↥L) :
    Group.IsNilpotent ↥(CFSG.oddCore ↥L) ∧ Odd (Nat.card ↥(CFSG.oddCore ↥L)) ∧
      ¬ 3 ∣ Nat.card ↥(CFSG.oddCore ↥L) ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L) := by
  obtain ⟨hconcl, hcommon, -⟩ := h
  have hF : CFSG.fittingSubgroup ↥L = CFSG.oddCore ↥L := hcommon.1
  have hn : Group.IsNilpotent ↥(CFSG.oddCore ↥L) := by
    rw [← hF]
    infer_instance
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hF)
      hcommon.2.1
  refine ⟨hn, A312.odd_card_oddCore _, ?_, hq⟩
  rw [← hF]
  rcases hconcl with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact absurd hc.1 hnq
  · exact absurd hc.1 hnq
  · obtain ⟨p, hp, hp3, -, hE, -⟩ := h3
    rw [card_eq_of_isElemAbelianOfRank hE]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  · obtain ⟨-, -, -, hpr⟩ := h4
    intro h3
    rcases (hpr 3 Nat.prime_three h3).1 with h | h | h <;> omega

theorem nqf_mono {a b : ℕ} (h : a ≤ b) : a ^ 3 * (a ^ 2 - 1) ≤ b ^ 3 * (b ^ 2 - 1) :=
  Nat.mul_le_mul (Nat.pow_le_pow_left h 3) (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem false_of_nqOrder {N : ℕ} (h : NQOrder N) {a b : ℕ} (hlo : a ^ 3 * (a ^ 2 - 1) < N)
    (hhi : N < b ^ 3 * (b ^ 2 - 1)) (hmid : ∀ p, a < p → p < b → ¬ p.Prime)
    (h4 : N % 16 ≠ 8 ∨ ∃ q, q.Prime ∧ q ∣ N ∧ ¬ q ∣ 120 ∧ (q % 5 = 2 ∨ q % 5 = 3)) : False := by
  rcases h with ⟨p, hp, -, rfl⟩ | ⟨m, hm, hq, rfl⟩
  · have hap : a < p := by
      by_contra hle
      exact absurd (nqf_mono (not_lt.mp hle)) (not_le.mpr hlo)
    have hpb : p < b := by
      by_contra hle
      exact absurd (nqf_mono (not_lt.mp hle)) (not_le.mpr hhi)
    exact hmid p hap hpb hp
  · rcases h4 with h4 | ⟨q, hqp, hqd, hq120, hq5⟩
    · obtain ⟨j, rfl⟩ := hm
      apply h4
      omega
    · have hcop : Nat.Coprime q 120 := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hq120
      have hqm : q ∣ m := hcop.dvd_of_dvd_mul_left hqd
      rcases hq q hqp hqm with h | h | h <;> omega

theorem false_of_nqOrder_mod8 {N : ℕ} (h : NQOrder N) (hN : N % 8 = 4) : False := by
  rcases h with ⟨p, hp, hp3, rfl⟩ | ⟨m, -, -, rfl⟩
  · have hodd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨j, rfl⟩ := hodd
    have h8 : 8 ∣ (2 * j + 1) ^ 2 - 1 := by
      have e : (2 * j + 1) ^ 2 - 1 = 4 * (j * (j + 1)) := by
        rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
        ring
      rw [e]
      obtain ⟨k, hk⟩ := Nat.even_mul_succ_self j
      rw [hk]
      exact ⟨k, by ring⟩
    have : 8 ∣ (2 * j + 1) ^ 3 * ((2 * j + 1) ^ 2 - 1) := Dvd.dvd.mul_left h8 _
    omega
  · omega

theorem false_of_nqOrder_card {N c : ℕ} (h : NQOrder N) (hc : N = c) (a : ℕ)
    (hlo : a ^ 3 * (a ^ 2 - 1) < c) (hhi : c < (a + 1) ^ 3 * ((a + 1) ^ 2 - 1))
    (h16 : c % 16 ≠ 8) : False := by
  subst hc
  exact false_of_nqOrder h hlo hhi (fun p h1 h2 => absurd h2 (by omega)) (Or.inl h16)

theorem false_of_nqOrder_su35 {d : ℕ} (h : NQOrder (126000 * d)) (hd : d ∣ 24) : False := by
  have hd24 : d ≤ 24 := Nat.le_of_dvd (by norm_num) hd
  rcases h with ⟨p, hp, hp3, he⟩ | ⟨m, hm, -, he⟩
  · have hp20 : p ≤ 20 := by
      by_contra hlt
      have h1 := nqf_mono (show 21 ≤ p by omega)
      norm_num at h1
      omega
    interval_cases p
    all_goals first
      | (norm_num at he; omega)
      | norm_num at hp
  · obtain ⟨j, rfl⟩ := hm
    omega

section Cases

variable {Q : Type} [Group Q] {L : Subgroup Q}

theorem false_of_nq_one
    (hN : NQOrder (Nat.card ↥L))
    (hL : IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L) : False := by
  rcases hL with hL | hL | hL | hL | hL
  · have hcL : Nat.card ↥L = 20160 := by
      obtain ⟨-, F, _, _, hF, ⟨e3⟩⟩ := hL
      rw [Nat.card_congr e3.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3) (by norm_num), hF]
      decide
    exact false_of_nqOrder_card hN hcL 7 (by norm_num) (by norm_num) (by norm_num)
  · have hcL : Nat.card ↥L = 60480 := by
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hF]
      norm_num
    exact false_of_nqOrder_card hN hcL 9 (by norm_num) (by norm_num) (by norm_num)
  · have hcL : Nat.card ↥L = 979200 := by
      rw [(Timmesfeld.card_statedClassicalModel_two hL).2.2.1 rfl]
      decide
    exact false_of_nqOrder_card hN hcL 15 (by norm_num) (by norm_num) (by norm_num)
  · have hcL : Nat.card ↥L = 251596800 := by
      have h := Timmesfeld.card_chevalleyExceptionalModel_two hL
      simp only at h
      rw [h]
      decide
    exact false_of_nqOrder_card hN hcL 47 (by norm_num) (by norm_num) (by norm_num)
  · have hcL : Nat.card ↥L = 2 ^ 24 * 4041335025 := by
      have h := Timmesfeld.card_chevalleyExceptionalModel_two hL
      simp only at h
      rw [h]
      decide
    exact false_of_nqOrder_card hN hcL 2324 (by norm_num) (by norm_num) (by norm_num)

theorem false_of_nq_two (hN : NQOrder (Nat.card ↥L))
    (hL : IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) : False := by
  rcases hL with hA | ⟨-, hZ3, ⟨eZ⟩⟩
  · obtain ⟨e⟩ := hA
    have hcL : Nat.card ↥L = 2520 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
      decide
    rw [hcL] at hN
    exact false_of_nqOrder hN (a := 4) (b := 5) (by norm_num) (by norm_num)
      (fun p h1 h2 => absurd h2 (by omega)) (Or.inr ⟨7, by norm_num, by norm_num, by norm_num,
        by norm_num⟩)
  · have hcL : Nat.card ↥L = 7560 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      rw [Nat.card_congr eZ.toEquiv, card_alternatingGroup1527d 7 (by norm_num), hZ3] at h
      rw [h]
      decide
    rw [hcL] at hN
    refine false_of_nqOrder hN (a := 5) (b := 7) (by norm_num) (by norm_num) ?_
      (Or.inr ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    intro p h1 h2
    obtain rfl : p = 6 := by omega
    decide

theorem false_of_nq_three [Finite Q] (h314 : A314Facts) (hN : NQOrder (Nat.card ↥L))
    (hL : IsPSL 2 5 2 ↥L ∨ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      IsPSL 2 p 1 ↥L) : False := by
  rcases hL with hL | ⟨p, hp, hp5, hp8, hL⟩
  · have hcL : Nat.card ↥L = 7800 := by
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2) (by norm_num), hF]
      decide
    rw [hcL] at hN
    exact false_of_nqOrder hN (a := 6) (b := 7) (by norm_num) (by norm_num)
      (fun p h1 h2 => absurd h2 (by omega)) (Or.inr ⟨13, by norm_num, by norm_num, by norm_num,
        by norm_num⟩)
  · have hp11 := A7.eleven_le_of_sq_mod_five hp hp5
    obtain ⟨-, -, hcL⟩ := h314.model.2.2 p hp (by omega) ↥L hL
    rw [hcL] at hN
    refine false_of_nqOrder_mod8 hN ?_
    obtain ⟨j, hj⟩ : ∃ j, p = 8 * j + p % 8 := ⟨p / 8, (Nat.div_add_mod p 8).symm⟩
    rcases hp8 with h | h <;> rw [h] at hj <;> subst hj
    · have e : (8 * j + 3) * ((8 * j + 3) ^ 2 - 1) / 2 =
          4 * ((8 * j + 3) * (8 * j ^ 2 + 6 * j + 1)) := by
        have e1 : (8 * j + 3) ^ 2 - 1 = 8 * (8 * j ^ 2 + 6 * j + 1) := by
          rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
          ring
        rw [e1, show (8 * j + 3) * (8 * (8 * j ^ 2 + 6 * j + 1)) =
          2 * (4 * ((8 * j + 3) * (8 * j ^ 2 + 6 * j + 1))) by ring]
        exact Nat.mul_div_cancel_left _ two_pos
      rw [e]
      have : (8 * j + 3) * (8 * j ^ 2 + 6 * j + 1) % 2 = 1 := by
        rw [Nat.mul_mod]
        have h1 : (8 * j + 3) % 2 = 1 := by omega
        have h2 : (8 * j ^ 2 + 6 * j + 1) % 2 = 1 := by omega
        rw [h1, h2]
      omega
    · have e : (8 * j + 5) * ((8 * j + 5) ^ 2 - 1) / 2 =
          4 * ((8 * j + 5) * (8 * j ^ 2 + 10 * j + 3)) := by
        have e1 : (8 * j + 5) ^ 2 - 1 = 8 * (8 * j ^ 2 + 10 * j + 3) := by
          rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
          ring
        rw [e1, show (8 * j + 5) * (8 * (8 * j ^ 2 + 10 * j + 3)) =
          2 * (4 * ((8 * j + 5) * (8 * j ^ 2 + 10 * j + 3))) by ring]
        exact Nat.mul_div_cancel_left _ two_pos
      rw [e]
      have : (8 * j + 5) * (8 * j ^ 2 + 10 * j + 3) % 2 = 1 := by
        rw [Nat.mul_mod]
        have h1 : (8 * j + 5) % 2 = 1 := by omega
        have h2 : (8 * j ^ 2 + 10 * j + 3) % 2 = 1 := by omega
        rw [h1, h2]
      omega

theorem false_of_nq_five (hN : NQOrder (Nat.card ↥L))
    (hL : (IsPSL 3 5 1 ↥L ∨ IsSL3 5 ↥L) ∨ IsPSU 3 5 1 ↥L ∨ IsSU3 5 ↥L) : False := by
  rcases hL with (hL | hL) | hL | hL
  · have hcL : Nat.card ↥L = 372000 := by
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3) (by norm_num), hF]
      decide
    exact false_of_nqOrder_card hN hcL 13 (by norm_num) (by norm_num) (by norm_num)
  · have hcL : Nat.card ↥L = 372000 := by
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
      decide
    exact false_of_nqOrder_card hN hcL 13 (by norm_num) (by norm_num) (by norm_num)
  · have hcL : Nat.card ↥L = 126000 := by
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) Nat.prime_five le_rfl hF
          (by norm_num)]
      decide
    exact false_of_nqOrder_card hN hcL 10 (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
    set S := CFSG.Assembly.LowTwoRank.StatedSU 3 5 F with hSdef
    set N := (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf S with hN'
    have hP : Nat.card (S ⧸ N) = 126000 := by
      have h := Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) (p := 5) (f := 1)
        Nat.prime_five le_rfl (by rw [hF]; norm_num) (by norm_num : 2 ≤ 3)
      simp only [pow_one] at h
      rw [show Nat.card (S ⧸ N) = Nat.card (CFSG.Assembly.LowTwoRank.StatedProj S) from rfl,
        h]
      decide
    have hS : Nat.card ↥S = 126000 * Nat.card N := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hP]
    have hN24 : Nat.card N ∣ 24 := by
      have h1 : Nat.card N ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F) := by
        rw [← Subgroup.card_map_of_injective S.subtype_injective, hN',
          Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F) ∣ 24 := by
        have h3 := Subgroup.card_range_dvd (Matrix.GeneralLinearGroup.scalar (Fin 3) (R := F))
        rw [Nat.card_units, hF] at h3
        exact h3
      exact h1.trans h2
    rw [Nat.card_congr e.toEquiv, hS] at hN
    exact false_of_nqOrder_su35 hN hN24

theorem false_of_nq_sporadic
    (hN : NQOrder (Nat.card ↥L))
    (hL : (IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) ∨
      IsSporadic .M23 ↥L ∨ IsSporadic .J1 ↥L ∨ IsSporadic .J2 ↥L ∨ IsSporadic .J4 ↥L ∨
      IsSporadic .HS ↥L ∨ IsSporadic .Ru ↥L) : False := by
  rcases hL with (hM | ⟨-, hZ3, ⟨e⟩⟩) | hM | hM | hM | hM | hM | hM
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 443520 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M22
    exact false_of_nqOrder_card hN hcL 13 (by norm_num) (by norm_num) (by norm_num)
  · have hcL : Nat.card ↥L = 1330560 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      have h2 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
        CFSG.Sporadic.Mathieu.card_M22
      rw [Nat.card_congr e.toEquiv, h2, hZ3] at h1
      rw [h1]
    exact false_of_nqOrder_card hN hcL 16 (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 10200960 := by
      rw [Nat.card_congr e.toEquiv]
      show Nat.card CFSG.Blueprint.NativeSporadic.M23 = _
      rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
      exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
        CFSG.M23.M23Group.card_M23
    exact false_of_nqOrder_card hN hcL 25 (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    rw [hcL] at hN
    exact false_of_nqOrder hN (a := 11) (b := 12) (by norm_num) (by norm_num)
      (fun p h1 h2 => absurd h2 (by omega)) (Or.inr ⟨7, by norm_num, by norm_num, by norm_num,
        by norm_num⟩)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 604800 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    exact false_of_nqOrder_card hN hcL 14 (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 21 * 41377816699065 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J4.card_J4
    exact false_of_nqOrder_card hN hcL 9720 (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 44352000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    exact false_of_nqOrder_card hN hcL 33 (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 145926144000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ru.card_Ru
    exact false_of_nqOrder_card hN hcL 170 (by norm_num) (by norm_num) (by norm_num)

end Cases

theorem a314_nonquasi
    (h314 : A314Facts) {G : Type} [Group G] [Finite G] {T B L : Subgroup G} (h36 : A36Strong L)
    (hnq : ¬ CFSG.IsQuasisimple ↥L) (h : A314Statement T B L) :
    (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)) := by
  have hN := nqOrder_card h36 hnq
  unfold A314Statement at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  · obtain ⟨-, -, hL, -⟩ := h1
    exact (false_of_nq_one hN hL).elim
  · obtain ⟨-, hL, -⟩ := h2
    exact (false_of_nq_two hN hL).elim
  · obtain ⟨-, hL⟩ := h3
    exact (false_of_nq_three h314 hN hL).elim
  · obtain ⟨-, ⟨s, hL⟩, -⟩ := h4
    cases s
    · exact (false_of_nq_five hN (Or.inr hL)).elim
    · exact (false_of_nq_five hN (Or.inl hL)).elim
  · obtain ⟨-, hL, -⟩ := h5
    exact (false_of_nq_five hN (Or.inl hL)).elim
  · obtain ⟨-, -, -, hL⟩ := h6
    exact (false_of_nq_sporadic hN (Or.inl hL)).elim
  · obtain ⟨-, -, -, hL⟩ := h7
    exact (false_of_nq_sporadic hN (Or.inr (Or.inl hL))).elim
  · obtain ⟨-, hL, -⟩ := h8
    exact (false_of_nq_sporadic hN (Or.inr (Or.inr (Or.inl hL)))).elim
  · obtain ⟨-, hL, -⟩ := h9
    exact (false_of_nq_sporadic hN (Or.inr (Or.inr (Or.inr (Or.inl hL))))).elim
  · obtain ⟨-, -, hL⟩ := h10
    exact (false_of_nq_sporadic hN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))).elim
  · obtain ⟨-, hL, -⟩ := h11
    exact (false_of_nq_sporadic hN
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))))).elim
  · obtain ⟨-, -, hL, -⟩ := h12
    exact (false_of_nq_sporadic hN
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL))))))).elim
  · exact Or.inl h13
  · exact Or.inr h14

end CFSG.Quasithin.H13.Ch9.KGFF
