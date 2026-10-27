module

public import CFSG.RankThree.SubgroupLists.LinearTwoFamily
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Equiv
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

theorem zmod_five_sq_cases : ∀ a r : ZMod 5, a = r * r → a = 0 ∨ a = 1 ∨ a = 4 := by decide

theorem zmod_seven_sq_cases : ∀ a r : ZMod 7, a = r * r → a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 := by
  decide

theorem mod_five_of_isSquare_five {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (h : IsSquare (5 : ZMod p)) : p % 5 = 1 ∨ p % 5 = 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrec := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
  have h' : IsSquare ((5 : ℕ) : ZMod p) := by exact_mod_cast h
  obtain ⟨c, hc⟩ := hrec.mpr h'
  have hres := zmod_five_sq_cases
  have hval : ((p : ℕ) : ZMod 5).val = p % 5 := ZMod.val_natCast 5 p
  rcases hres _ c hc with h0 | h1 | h4
  · exfalso
    rw [h0, ZMod.val_zero] at hval
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) (Fact.out)).mp
      (Nat.dvd_of_mod_eq_zero hval.symm)
    exact hp5 this.symm
  · left
    rw [h1] at hval
    exact hval.symm.trans rfl
  · right
    rw [h4] at hval
    exact hval.symm.trans rfl

theorem mod_seven_of_isSquare_neg_seven {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (h : IsSquare (-7 : ZMod p)) : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : (7 : ZMod p) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff 7 p).mp (by exact_mod_cast h0)
    exact hp7 ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp this)
  have hsq7 : IsSquare ((p : ℕ) : ZMod 7) := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · have hm1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
      have hs7 : IsSquare ((7 : ℕ) : ZMod p) := by
        have := hm1.mul h
        rw [show (-1 : ZMod p) * -7 = 7 by ring] at this
        exact_mod_cast this
      exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 7) h4
        (by norm_num)).mp hs7
    · have hs7 : ¬ IsSquare ((7 : ℕ) : ZMod p) := by
        intro hs
        have hs' : IsSquare (7 : ZMod p) := by exact_mod_cast hs
        have hm1 : IsSquare (-1 : ZMod p) := by
          have := h.mul hs'.inv
          rwa [show (-7 : ZMod p) * 7⁻¹ = -1 by field_simp] at this
        exact (ZMod.exists_sq_eq_neg_one_iff.mp hm1) h4
      have := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 7) h4
        (by norm_num) hp7).not.mp hs7
      exact not_not.mp this
  obtain ⟨c, hc⟩ := hsq7
  have hres := zmod_seven_sq_cases
  have hval : ((p : ℕ) : ZMod 7).val = p % 7 := ZMod.val_natCast 7 p
  rcases hres _ c hc with h0 | h1 | h2 | h4
  · exfalso
    rw [h0, ZMod.val_zero] at hval
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) (Fact.out)).mp
      (Nat.dvd_of_mod_eq_zero hval.symm)
    exact hp7 this.symm
  · left
    rw [h1] at hval
    exact hval.symm.trans rfl
  · right; left
    rw [h2] at hval
    exact hval.symm.trans rfl
  · right; right
    rw [h4] at hval
    exact hval.symm.trans rfl

variable {p : ℕ} [Fact p.Prime]

theorem exists_lift_isConj_pow {K : Type*} [Field K] {H : Subgroup (GL (Fin 3) K)}
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {n k : ℕ} (hn : Nat.Coprime n 3)
    {s : H ⧸ Subgroup.center H} (hs : s ^ n = 1) (hs1 : s ≠ 1) (hconj : IsConj s (s ^ k)) :
    ∃ X : GL (Fin 3) K, X ∈ H ∧ X ^ n = 1 ∧ X ≠ 1 ∧ IsConj X (X ^ k) := by
  obtain ⟨x, hxs, hxn⟩ := exists_lift_pow_eq_one le_rfl hZ3 hn s hs
  refine ⟨x, x.2, by rw [← Subgroup.coe_pow, hxn, Subgroup.coe_one], fun h => hs1 ?_, ?_⟩
  · rw [← hxs, show x = 1 from Subtype.ext h, QuotientGroup.mk_one]
  · have hH : IsConj x (x ^ k) := isConj_of_isConj_mk le_rfl hZ3 hn hxn
      (by rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow])
      (by rw [QuotientGroup.mk_pow, hxs]; exact hconj)
    rw [← Subgroup.coe_pow]
    exact H.subtype.map_isConj hH

theorem mod_ten_of_linear_two_five (hp2 : p ≠ 2) (hp5 : p ≠ 5) {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 5) (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    p % 10 = 1 ∨ p % 10 = 9 := by
  have : CharP F 5 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (n := 1)
    (by norm_num) (by rw [hF, pow_one])
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have h5F : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
  have h2F : (2 : F) ≠ 0 := by
    intro h
    have : (1 : F) = 0 := by linear_combination 3 * h - h5F
    exact one_ne_zero this
  set s := (toPSL2 e).symm (rootPSL2 F) with hsdef
  have hs5 : s ^ 5 = 1 := by
    rw [hsdef, ← map_pow, rootGroupPSL2_pow rootPSL2_mem_rootGroupPSL2, map_one]
  have hs1 : s ≠ 1 := fun h =>
    rootPSL2_ne_one ((toPSL2 e).symm.injective (by rw [← hsdef, h, map_one]))
  have hconj : IsConj s (s ^ 4) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_rootPSL2_pow (F := F) (k := 4)
      (a := Units.mk0 2 h2F) (by rw [Units.val_mk0]; norm_num))
    exact isConj_iff.mpr ⟨(toPSL2 e).symm c, by
      rw [hsdef, ← map_pow, ← map_inv, ← map_mul, ← map_mul, hc]⟩
  obtain ⟨X, hXH, hX5, hX1, hX4⟩ := exists_lift_isConj_pow hZ3 (by norm_num) hs5 hs1 hconj
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h)
    exact hp5 ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp this)
  have htr := sq_two_mul_trace_sub_one_eq_five (hdet X hXH) hX5 hX1 h5 hX4
  have hsq : IsSquare (5 : ZMod p) := ⟨_, by rw [← htr, sq]⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  rcases mod_five_of_isSquare_five hp2 hp5 hsq with h | h <;> omega

theorem mod_seven_of_linear_two_seven (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 7) (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have : CharP F 7 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (n := 1)
    (by norm_num) (by rw [hF, pow_one])
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have h7F : (7 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 7
  have h3F : (3 : F) ≠ 0 := by
    intro h
    have : (1 : F) = 0 := by linear_combination 5 * h - 2 * h7F
    exact one_ne_zero this
  set s := (toPSL2 e).symm (rootPSL2 F) with hsdef
  have hs7 : s ^ 7 = 1 := by
    rw [hsdef, ← map_pow, rootGroupPSL2_pow rootPSL2_mem_rootGroupPSL2, map_one]
  have hs1 : s ≠ 1 := fun h =>
    rootPSL2_ne_one ((toPSL2 e).symm.injective (by rw [← hsdef, h, map_one]))
  have hconj : IsConj s (s ^ 2) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_rootPSL2_pow (F := F) (k := 2)
      (a := Units.mk0 3 h3F) (by rw [Units.val_mk0]; push_cast; linear_combination -h7F))
    exact isConj_iff.mpr ⟨(toPSL2 e).symm c, by
      rw [hsdef, ← map_pow, ← map_inv, ← map_mul, ← map_mul, hc]⟩
  obtain ⟨X, hXH, hX7, hX1, hX2⟩ := exists_lift_isConj_pow hZ3 (by norm_num) hs7 hs1 hconj
  have h7 : (7 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 7 p).mp (by exact_mod_cast h)
    exact hp7 ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp this)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  have htr := sq_two_mul_trace_add_one_eq_neg_seven (hdet X hXH) hX7 hX1 h2 h7 hX2
  exact mod_seven_of_isSquare_neg_seven hp2 hp7 ⟨_, by rw [← htr, sq]⟩

@[expose] def cycleFiveSix : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def invertFiveSix : alternatingGroup (Fin 6) :=
  ⟨swap 1 4 * swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem cycleFiveSix_pow_five : cycleFiveSix ^ 5 = 1 := Subtype.ext (by decide)

theorem cycleFiveSix_ne_one : cycleFiveSix ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

theorem invertFiveSix_conj : invertFiveSix * cycleFiveSix * invertFiveSix⁻¹ = cycleFiveSix ^ 4 :=
  Subtype.ext (by decide)

theorem mod_thirty_of_linear_two_nine (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hscal : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * x) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) = 3) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 9) (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    p % 30 = 1 ∨ p % 30 = 19 := by
  classical
  have hp : p.Prime := Fact.out
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center (Dvd.intro 1 (by rw [hZ, mul_one])) hz
  have hp31 : p % 3 = 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz1⟩ : ∃ z : Subgroup.center H, z ≠ 1 := by
      by_contra hno
      push Not at hno
      have : Subsingleton (Subgroup.center H) := ⟨fun a b => (hno a).trans (hno b).symm⟩
      rw [Nat.card_unique] at hZ
      omega
    obtain ⟨c, hc⟩ := hscal ((z : H) : GL (Fin 3) (ZMod p)) (fun x hx => by
      have := congrArg (fun g : H => ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)))
        (Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩)
      simpa using this)
    have hz3 : ((z : H) : GL (Fin 3) (ZMod p)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hZ3 _ z.2, Subgroup.coe_one]
    have hc3 : c ^ 3 = 1 := by
      have := congrArg (fun g : GL (Fin 3) (ZMod p) => (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0)
        hz3
      simp only [Units.val_pow_eq_pow_val, hc, Units.val_one, Matrix.one_apply_eq] at this
      rwa [Matrix.scalar_apply, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at this
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hz1
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rw [hc, map_one]
      rfl
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hc3
      exact zero_ne_one hc3
    have hord : orderOf (Units.mk0 c hc0) = 3 :=
      orderOf_eq_prime (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc3,
        Units.val_one])) (fun h => hc1 (by simpa using congrArg Units.val h))
    have hdvd : 3 ∣ p - 1 := by
      rw [← ZMod.card_units p, ← hord]
      exact orderOf_dvd_card
    have := hp.two_le
    omega
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ψ⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
    F (by rw [← Nat.card_eq_fintype_card, hF])
  set θ := (toPSL2 e).trans ψ with hθ
  set s := θ.symm cycleFiveSix with hsdef
  have hs5 : s ^ 5 = 1 := by rw [hsdef, ← map_pow, cycleFiveSix_pow_five, map_one]
  have hs1 : s ≠ 1 := fun h =>
    cycleFiveSix_ne_one (θ.symm.injective (by rw [← hsdef, h, map_one]))
  have hconj : IsConj s (s ^ 4) := by
    refine isConj_iff.mpr ⟨θ.symm invertFiveSix, ?_⟩
    rw [hsdef, ← map_pow, ← map_inv, ← map_mul, ← map_mul, invertFiveSix_conj]
  obtain ⟨X, hXH, hX5, hX1, hX4⟩ := exists_lift_isConj_pow hZ3 (by norm_num) hs5 hs1 hconj
  have hp5 : p ≠ 5 := by
    rintro rfl
    norm_num at hp31
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h)
    exact hp5 ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp this)
  have htr := sq_two_mul_trace_sub_one_eq_five (hdet X hXH) hX5 hX1 h5 hX4
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  rcases mod_five_of_isSquare_five hp2 hp5 ⟨_, by rw [← htr, sq]⟩ with h | h <;> omega

end CFSG.RankThree.SubgroupLists
