module

public import CFSG.Sporadic.FischerOddCore.Fi22FiveExact
public import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public import CFSG.Sporadic.FischerOddCore.ClosureSpec

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native

theorem fi22CentSylows_eq :
    ((List.range 11).map fun s => (fi22CentSylowField s 0, fi22CentSylowField s 1,
      fi22CentSylowField s 2)) =
    [(0, 3, 27), (1, 3, 81), (1, 5, 5), (2, 3, 81), (2, 5, 5), (3, 3, 729), (3, 5, 25), (3, 7, 7),
      (4, 3, 81), (4, 5, 5), (4, 7, 7)] := by
  rfl

theorem fi22SylSeeds_size (s : ℕ) : (fi22SylSeeds s).size = fi22CentSylowField s 4 := by
  simp [fi22SylSeeds]

theorem fi22SylGens_size (s : ℕ) : (fi22SylGens s).size = 2 * fi22CentSylowField s 4 := by
  simp [fi22SylGens, fi22SylSeeds_size]
  omega

theorem fi22SylSeeds_get {s i : ℕ} (hi : i < fi22CentSylowField s 4) :
    (fi22SylSeeds s)[i]! = fi22CentArr (fi22CentSylowField s 3 + i) := by
  rw [getElem!_pos _ i (by rw [fi22SylSeeds_size]; exact hi)]
  simp [fi22SylSeeds]

@[expose] def fi22SylGen (s i : ℕ) : Equiv.Perm (Fin 3510) :=
  if i < fi22CentSylowField s 4 then fi22CentPerm (fi22CentSylowField s 3 + i)
  else (fi22CentPerm (fi22CentSylowField s 3 + (i - fi22CentSylowField s 4)))⁻¹

theorem fi22CentSylowField_lines {s : ℕ} (hs : s < 11) :
    fi22CentSylowField s 3 + fi22CentSylowField s 4 ≤ 108 ∧
      80 ≤ fi22CentSylowField s 3 := by
  interval_cases s <;> decide

theorem fi22CentWitField_lines {w : ℕ} (hw : w < 66) :
    fi22CentWitField w 0 < 306 ∧ fi22CentWitField w 1 < 306 := by
  interval_cases w <;> decide

theorem fi22CentSylowField_wits {s : ℕ} (hs : s < 11) :
    fi22CentSylowField s 6 + fi22CentSylowField s 7 ≤ 66 := by
  interval_cases s <;> decide

theorem rep_fi22SylGens
    {s : ℕ} (hs : s < 11) {i : ℕ} (hi : i < (fi22SylGens s).size) :
    Rep 3510 (fi22SylGens s)[i]! (fi22SylGen s i) := by
  have hl := fi22CentSylowField_lines hs
  rw [fi22SylGens_size] at hi
  by_cases h : i < fi22CentSylowField s 4
  · rw [fi22SylGens, getElem!_pos _ i (by simp [fi22SylSeeds_size]; omega),
      Array.getElem_append_left (by simpa [fi22SylSeeds_size] using h),
      ← getElem!_pos _ i (by simpa [fi22SylSeeds_size] using h), fi22SylSeeds_get h, fi22SylGen,
      ite_eq_left h]
    exact rep_fi22CentPerm (by omega)
  · rw [fi22SylGens, getElem!_pos _ i (by simp [fi22SylSeeds_size]; omega),
      Array.getElem_append_right (by simp [fi22SylSeeds_size]; omega)]
    simp only [Array.getElem_map, fi22SylSeeds_size]
    rw [← getElem!_pos _ _ (by simp [fi22SylSeeds_size]; omega),
      fi22SylSeeds_get (by omega), fi22SylGen, ite_eq_right h]
    exact rep_fi22CentPerm_inv (by omega)

theorem gensClosure_fi22SylGens {s : ℕ} (_hs : s < 11) :
    gensClosure (fi22SylGens s) (fi22SylGen s) = fi22CentSylowSub s := by
  apply le_antisymm
  · rw [gensClosure, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [fi22SylGens_size] at hi
    by_cases h : i < fi22CentSylowField s 4
    · rw [fi22SylGen, ite_eq_left h]
      exact Subgroup.subset_closure ⟨i, h, rfl⟩
    · rw [fi22SylGen, ite_eq_right h]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i - fi22CentSylowField s 4, by omega, rfl⟩)
  · rw [fi22CentSylowSub, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    refine Subgroup.subset_closure ⟨i, by rw [fi22SylGens_size]; omega, ?_⟩
    rw [fi22SylGen, ite_eq_left hi]

theorem fi22SylWits_get {s w : ℕ} (hw : w < fi22CentSylowField s 7) :
    (fi22SylWits s)[w]! = fi22CentArr (fi22CentWitField (fi22CentSylowField s 6 + w) 0) := by
  rw [getElem!_pos _ w (by simpa [fi22SylWits] using hw)]
  simp [fi22SylWits]

theorem fi22SylWits_size (s : ℕ) : (fi22SylWits s).size = fi22CentSylowField s 7 := by
  simp [fi22SylWits]

theorem rep_fi22SylWits
    {s w : ℕ} (hs : s < 11) (hw : w < fi22CentSylowField s 7) :
    Rep 3510 (fi22SylWits s)[w]! (fi22SylX s w) := by
  have hwl := fi22CentSylowField_wits hs
  rw [fi22SylWits_get hw]
  exact rep_fi22CentPerm (fi22CentWitField_lines (by omega)).1

theorem factorization_eq_of_mul {N p a m : ℕ} (hp : p.Prime) (hN : N = p ^ a * m) (hm : ¬ p ∣ m) :
    N.factorization p = a := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [hN, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem fi22Syl_sylow
    {s : ℕ} (hs : s < 11) {a m : ℕ}
    (hN : Nat.card (fi22H (fi22CentSylowField s 0)) = fi22CentSylowField s 1 ^ a * m)
    (hm : ¬ fi22CentSylowField s 1 ∣ m) (ha : fi22CentSylowField s 2 = fi22CentSylowField s 1 ^ a)
    (hp : (fi22CentSylowField s 1).Prime) :
    ∃ Q : Sylow (fi22CentSylowField s 1) (fi22H (fi22CentSylowField s 0)),
      (Q : Subgroup _) = (fi22CentSylowSub s).subgroupOf (fi22H (fi22CentSylowField s 0)) := by
  have : Fact (fi22CentSylowField s 1).Prime := ⟨hp⟩
  obtain ⟨hle, hcard, -⟩ := fi22Syl_facts hs
  have hc5 : fi22CentSylowField s 0 < 5 := by interval_cases s <;> decide
  have : Finite (fi22H (fi22CentSylowField s 0)) := Nat.finite_of_card_ne_zero (by
    rw [card_fi22H hc5]; interval_cases s <;> decide)
  have hcard' : Nat.card ((fi22CentSylowSub s).subgroupOf (fi22H (fi22CentSylowField s 0))) =
      fi22CentSylowField s 1 ^ (Nat.card (fi22H (fi22CentSylowField s 0))).factorization
        (fi22CentSylowField s 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard, ha,
      factorization_eq_of_mul hp hN hm]
  exact ⟨Sylow.ofCard ((fi22CentSylowSub s).subgroupOf (fi22H (fi22CentSylowField s 0))) hcard',
    rfl⟩

theorem fi22Syl_witness
    {s : ℕ} (hs : s < 11) (hp : (fi22CentSylowField s 1).Prime) :
    ∀ y : fi22H (fi22CentSylowField s 0),
      (y : Equiv.Perm (Fin 3510)) ∈ fi22CentSylowSub s → orderOf y = fi22CentSylowField s 1 →
      ∃ x t : fi22H (fi22CentSylowField s 0), ∃ j : ℕ, 0 < j ∧ j < fi22CentSylowField s 1 ∧
        orderOf x = fi22CentSylowField s 1 ∧ y = t * x ^ j * t⁻¹ ∧
        ∃ g : fi22H (fi22CentSylowField s 0), ∃ k : ℕ, (x * g * x * g⁻¹) ^ k ≠ 1 ∧
          ((x * g * x * g⁻¹) ^ k) ^ 2 = 1 := by
  have : Fact (fi22CentSylowField s 1).Prime := ⟨hp⟩
  obtain ⟨hle, -, hcov, hwit⟩ := fi22Syl_facts hs
  intro y hy hyo
  have hy1 : (y : Equiv.Perm (Fin 3510)) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  have hyp : (y : Equiv.Perm (Fin 3510)) ^ fi22CentSylowField s 1 = 1 := by
    rw [← Subgroup.coe_pow, ← hyo, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨w, hw, t, ht, j, hj0, hjp, heq⟩ := hcov _ hy hy1 hyp
  obtain ⟨hx1, hxp, hxH, hhH, k, hk1, hk2⟩ := hwit w hw
  refine ⟨⟨_, hxH⟩, ⟨t, hle ht⟩, j, hj0, hjp, ?_, Subtype.ext heq, ⟨_, hhH⟩, k, fun h => ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hxp hx1
  · exact hk1 (congrArg Subtype.val h)
  · exact Subtype.ext hk2

theorem prime_mem_of_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ l : List (ℕ × ℕ), (∀ q ∈ l, q.1.Prime) → p ∣ (l.map fun q => q.1 ^ q.2).prod →
      ∃ q ∈ l, q.1 = p
  | [], _, h => absurd (Nat.dvd_one.1 h) hp.ne_one
  | q :: l, hq, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact ⟨q, List.mem_cons_self, ((Nat.prime_dvd_prime_iff_eq hp (hq q List.mem_cons_self)).1
        (hp.dvd_of_dvd_pow h1)).symm⟩
    · obtain ⟨q', hq', e⟩ := prime_mem_of_dvd_prod hp l (fun q'' h'' => hq q''
        (List.mem_cons_of_mem _ h'')) h1
      exact ⟨q', List.mem_cons_of_mem _ hq', e⟩

theorem fi22Syl_am {s : ℕ} (hs : s < 11) :
    (fi22CentSylowField s 1).Prime ∧ ∃ a m,
      Nat.card (fi22H (fi22CentSylowField s 0)) = fi22CentSylowField s 1 ^ a * m ∧
      ¬ fi22CentSylowField s 1 ∣ m ∧ fi22CentSylowField s 2 = fi22CentSylowField s 1 ^ a := by
  have hord := fun c (hc : c < 5) => card_fi22H (c := c) hc
  interval_cases s
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 3, 65536,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 4, 655360,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 1, 10616832,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 4, 40960,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 1, 663552,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 6, 1433600,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 2, 41803776,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 1, 149299200,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 4, 35840,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 1, 580608,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩
  · exact ⟨by norm_num [fi22CentSylowField, fi22CentSylows], 1, 414720,
      by rw [hord _ (by decide)]; rfl, by decide, rfl⟩

theorem oddCore_fi22H_of
    {c : ℕ} (hc : c < 5) (l : List (ℕ × ℕ)) (hl : ∀ q ∈ l, q.1.Prime)
    (hN : Nat.card (fi22H c) = (l.map fun q => q.1 ^ q.2).prod)
    (hrec : ∀ q ∈ l, q.1 ≠ 2 → ∃ s < 11, fi22CentSylowField s 0 = c ∧
      fi22CentSylowField s 1 = q.1) :
    CFSG.oddCore (fi22H c) = ⊥ := by
  have : Finite (fi22H c) := Nat.finite_of_card_ne_zero (by
    rw [card_fi22H hc]; interval_cases c <;> decide)
  apply oddCore_eq_bot_of_sylow_witnesses
  intro p hp hp2 hpd
  obtain ⟨q, hq, hqp⟩ := prime_mem_of_dvd_prod hp l hl (hN ▸ hpd)
  obtain ⟨s, hs, hs0, hs1⟩ := hrec q hq (hqp ▸ hp2)
  have hsp : fi22CentSylowField s 1 = p := hs1.trans hqp
  subst hs0 hsp
  obtain ⟨hpr, a, m, hNm, hm, ha⟩ := fi22Syl_am hs
  obtain ⟨Q, hQ⟩ := fi22Syl_sylow hs hNm hm ha hpr
  refine ⟨Q, fun y hy hyo => ?_⟩
  rw [hQ, Subgroup.mem_subgroupOf] at hy
  exact fi22Syl_witness hs hpr y hy hyo

theorem oddCore_fi22H
    {c : ℕ} (hc : c < 5) : CFSG.oddCore (fi22H c) = ⊥ := by
  have hord := card_fi22H hc
  interval_cases c
  · exact oddCore_fi22H_of (by decide) [(2, 16), (3, 3)] (by decide) (by rw [hord]; rfl)
      (by decide)
  · exact oddCore_fi22H_of (by decide) [(2, 17), (3, 4), (5, 1)] (by decide) (by rw [hord]; rfl)
      (by decide)
  · exact oddCore_fi22H_of (by decide) [(2, 13), (3, 4), (5, 1)] (by decide) (by rw [hord]; rfl)
      (by decide)
  · exact oddCore_fi22H_of (by decide) [(2, 13), (3, 6), (5, 2), (7, 1)] (by decide)
      (by rw [hord]; rfl) (by decide)
  · exact oddCore_fi22H_of (by decide) [(2, 10), (3, 4), (5, 1), (7, 1)] (by decide)
      (by rw [hord]; rfl) (by decide)

theorem CTUC_Fi22_five_fixed_subgroups_odd_core_trivial :
    (∀ c < 5, CFSG.oddCore (fi22H c) = ⊥) ∧
    CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 0}) = ⊥ ∧
    CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 1}) = ⊥ ∧
    CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 3}) = ⊥ ∧
    CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 4}) = ⊥ ∧
    CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep 5}) = ⊥ ∧
    ((List.range 11).map fun s => (fi22CentSylowField s 0, fi22CentSylowField s 1,
      fi22CentSylowField s 2)) =
      [(0, 3, 27), (1, 3, 81), (1, 5, 5), (2, 3, 81), (2, 5, 5), (3, 3, 729), (3, 5, 25),
        (3, 7, 7), (4, 3, 81), (4, 5, 5), (4, 7, 7)] ∧
    (∀ s < 11, fi22CentSylowSub s ≤ fi22H (fi22CentSylowField s 0) ∧
      Nat.card (fi22CentSylowSub s) = fi22CentSylowField s 2 ∧
      ∃ Q : Sylow (fi22CentSylowField s 1) (fi22H (fi22CentSylowField s 0)),
        (Q : Subgroup _) = (fi22CentSylowSub s).subgroupOf (fi22H (fi22CentSylowField s 0))) := by
  obtain ⟨h0, h1, h3, h4, h5, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  refine ⟨fun c hc => oddCore_fi22H hc, ?_, ?_, ?_, ?_, ?_, fi22CentSylows_eq, fun s hs => ?_⟩
  · rw [h0]; exact oddCore_fi22H (by norm_num)
  · rw [h1]; exact oddCore_fi22H (by norm_num)
  · rw [h3]; exact oddCore_fi22H (by norm_num)
  · rw [h4]; exact oddCore_fi22H (by norm_num)
  · rw [h5]; exact oddCore_fi22H (by norm_num)
  · obtain ⟨hle, hcard, -⟩ := fi22Syl_facts hs
    obtain ⟨hpr, a, m, hNm, hm, ha⟩ := fi22Syl_am hs
    exact ⟨hle, hcard, fi22Syl_sylow hs hNm hm ha hpr⟩

end CFSG.Sporadic.FischerOddCore
