module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KFacts2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Ree

public section

open CFSG.Open CFSG.Open.StatedAPI

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.KFacts

theorem w2_entries_sq_one {K : Type} [Field K] (h2 : (2 : K) = 0)
    (a00 a01 a10 a11 b00 b01 b10 b11 : K)
    (E1 : a00 * a00 + a01 * a10 = 1) (E2 : a00 * a01 + a01 * a11 = 0)
    (E3 : a10 * a00 + a11 * a10 = 0) (E4 : a10 * a01 + a11 * a11 = 1)
    (C01 : a00 * b01 + a01 * b11 = b00 * a01 + b01 * a11)
    (C10 : a10 * b00 + a11 * b10 = b10 * a00 + b11 * a10)
    (Db : b00 * b11 - b01 * b10 = 1)
    (hA : ¬ (a00 = 1 ∧ a01 = 0 ∧ a10 = 0 ∧ a11 = 1)) :
    b00 * b00 + b01 * b10 = 1 ∧ b00 * b01 + b01 * b11 = 0 ∧
      b10 * b00 + b11 * b10 = 0 ∧ b10 * b01 + b11 * b11 = 1 := by
  have hnz : a01 ≠ 0 ∨ a10 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h01, h10⟩ := hcon
    have ha00 : a00 = 1 := by
      have h : (a00 - 1) * (a00 - 1) = 0 := by
        linear_combination E1 - a01 * h10 + (1 - a00) * h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
    have ha11 : a11 = 1 := by
      have h : (a11 - 1) * (a11 - 1) = 0 := by
        linear_combination E4 - a10 * h01 + (1 - a11) * h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
    exact hA ⟨ha00, h01, h10, ha11⟩
  have ht : a00 + a11 = 0 := by
    rcases hnz with h | h
    · have h' : a01 * (a00 + a11) = 0 := by linear_combination E2
      exact (mul_eq_zero.mp h').resolve_left h
    · have h' : a10 * (a00 + a11) = 0 := by linear_combination E3
      exact (mul_eq_zero.mp h').resolve_left h
  have hC01 : a01 * (b11 - b00) = 0 := by
    linear_combination C01 - b01 * ht + (b01 * a11) * h2
  have hC10 : a10 * (b00 - b11) = 0 := by
    linear_combination C10 - b10 * ht + (b10 * a00) * h2
  have hb : b00 + b11 = 0 := by
    rcases hnz with h | h
    · have h' := (mul_eq_zero.mp hC01).resolve_left h
      linear_combination h' + b00 * h2
    · have h' := (mul_eq_zero.mp hC10).resolve_left h
      linear_combination h' + b11 * h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -Db + b00 * hb - h2
  · linear_combination b01 * hb
  · linear_combination b10 * hb
  · linear_combination -Db + b11 * hb - h2

theorem w2_sq_eq_one_mat {K : Type} [Field K] [CharP K 2]
    (a b : Matrix (Fin 2) (Fin 2) K) (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b.det = 1)
    (hab : a * b = b * a) : b * b = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have E1 := congrFun (congrFun ha 0) 0
  have E2 := congrFun (congrFun ha 0) 1
  have E3 := congrFun (congrFun ha 1) 0
  have E4 := congrFun (congrFun ha 1) 1
  have C01 := congrFun (congrFun hab 0) 1
  have C10 := congrFun (congrFun hab 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
    Matrix.one_apply_ne', one_ne_zero, ite_false, ite_true] at E1 E2 E3 E4 C01 C10
  rw [Matrix.det_fin_two] at hb
  have hA : ¬ (a 0 0 = 1 ∧ a 0 1 = 0 ∧ a 1 0 = 0 ∧ a 1 1 = 1) := by
    rintro ⟨h00, h01, h10, h11⟩
    apply ha1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  obtain ⟨k1, k2, k3, k4⟩ := w2_entries_sq_one h2 (a 0 0) (a 0 1) (a 1 0) (a 1 1)
    (b 0 0) (b 0 1) (b 1 0) (b 1 1)
    (by linear_combination E1) (by linear_combination E2) (by linear_combination E3)
    (by linear_combination E4) (by linear_combination C01) (by linear_combination C10)
    (by linear_combination hb) hA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
    | linear_combination k1
    | linear_combination k2
    | linear_combination k3
    | linear_combination k4

theorem w2_sq_eq_one {K : Type} [Field K] [CharP K 2]
    (A B : ↥(StatedSL 2 K)) (hA : A * A = 1) (hA1 : A ≠ 1) (hAB : A * B = B * A) :
    B * B = 1 := by
  have hmat : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have := congrArg (fun X : ↥(StatedSL 2 K) => ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hA
    simpa [Units.val_mul] using this
  have hA1m : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro h
    apply hA1
    apply Subtype.ext
    apply Units.ext
    simpa using h
  have hab : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg
      (fun X : ↥(StatedSL 2 K) => ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hAB
    simpa [Units.val_mul] using this
  have hdet : ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    mem_statedSL_iff.1 B.2
  have key := w2_sq_eq_one_mat _ _ hmat hA1m hdet hab
  apply Subtype.ext
  apply Units.ext
  simpa [Units.val_mul] using key

theorem w1_statedScalars_subgroupOf_sl_two {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' := hx
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx'
  obtain ⟨c, hc⟩ := hx'
  have hdetx : Matrix.GeneralLinearGroup.det (x : GL (Fin 2) K) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact mem_statedSL_iff.1 x.2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar] at hdetx
  have hsq : (c : K) ^ 2 = 1 := by
    have := congrArg Units.val hdetx
    simpa using this
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hc1 : (c : K) = 1 := by
    have h0 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
      linear_combination hsq + (1 - (c : K)) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
  have hc' : c = 1 := Units.ext hc1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  simp [← hc, hc']

theorem w1_three_pow_odd_mod_eight (a : ℕ) : 3 ^ (2 * a + 1) % 8 = 3 := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    have h : 3 ^ (2 * (n + 1) + 1) = 9 * 3 ^ (2 * n + 1) := by ring
    rw [h]
    omega

theorem w1_ree_not_sixteen_dvd {q : ℕ} (hq : q % 16 = 3 ∨ q % 16 = 11) :
    ¬ 16 ∣ q ^ 3 * (q - 1) * (q ^ 3 + 1) := by
  intro h
  have hq1 : 1 ≤ q := by omega
  have h' : (q : ZMod 16) ^ 3 * ((q : ZMod 16) - 1) * ((q : ZMod 16) ^ 3 + 1) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast [Nat.cast_sub hq1] at this
    exact this
  have hqz : (q : ZMod 16) = ((q % 16 : ℕ) : ZMod 16) := (ZMod.natCast_mod q 16).symm
  rw [hqz] at h'
  rcases hq with hq | hq <;> rw [hq] at h' <;> revert h' <;> decide

theorem w1_ordA_one_not_sixteen_dvd {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ¬ 16 ∣ CFSG.Open.ordA (2 - 1) q := by
  have hq1 : 1 ≤ q := by omega
  have hgcd : Nat.gcd 2 (q - 1) = 2 := Nat.gcd_eq_left (by omega)
  have hord : CFSG.Open.ordA (2 - 1) q = q * (q ^ 2 - 1) / 2 := by
    unfold CFSG.Open.ordA
    norm_num [Finset.Icc_self, hgcd]
  rw [hord]
  intro h16
  have hX : (q * (q ^ 2 - 1)) % 32 = 0 ∨ (q * (q ^ 2 - 1)) % 32 = 1 := by
    generalize q * (q ^ 2 - 1) = X at h16 ⊢
    omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hcast : ((q * (q ^ 2 - 1) : ℕ) : ZMod 32) =
      (q : ZMod 32) * ((q : ZMod 32) ^ 2 - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one]
  have hZ : ((q * (q ^ 2 - 1) : ℕ) : ZMod 32) = 0 ∨ ((q * (q ^ 2 - 1) : ℕ) : ZMod 32) = 1 := by
    rcases hX with h | h
    · left
      rw [← ZMod.natCast_mod, h]
      simp
    · right
      rw [← ZMod.natCast_mod, h]
      simp
  rw [hcast] at hZ
  have hqz : (q : ZMod 32) = ((q % 32 : ℕ) : ZMod 32) := (ZMod.natCast_mod q 32).symm
  rw [hqz] at hZ
  have hr : q % 32 = 3 ∨ q % 32 = 5 ∨ q % 32 = 11 ∨ q % 32 = 13 ∨
      q % 32 = 19 ∨ q % 32 = 21 ∨ q % 32 = 27 ∨ q % 32 = 29 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr] at hZ <;> revert hZ <;>
    decide

theorem walterListLargeSylow_holds :
    WalterListLargeSylowStatement := by
  intro D _ _ hW P hP i hi hi1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : 16 ≤ Nat.card P.toSubgroup := hP
  have h16 : 16 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have h4 : 4 ≤ n := by
      by_contra hlt
      have h8 : 2 ^ n ≤ 8 := by
        calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      omega
    have h16P : 16 ∣ Nat.card P.toSubgroup := by
      rw [hn]
      have h16eq : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [h16eq]
      exact Nat.pow_dvd_pow 2 h4
    exact h16P.trans (Subgroup.card_subgroup_dvd_card P.toSubgroup)
  rcases hW with ⟨f, hf, h⟩ | ⟨p, f, hp, hp2, hf1, h5, hmod, h⟩ | ⟨f, hodd, h3, hR⟩ | hJ
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hchar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
      w1_statedScalars_subgroupOf_sl_two
    let φ : D ≃* ↥(StatedSL 2 K) :=
      e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
    have key : ∀ g : D, g * i = i * g → g * g = 1 := by
      intro g hg
      have hφi : φ i * φ i = 1 := by rw [← map_mul, hi, map_one]
      have hφi1 : φ i ≠ 1 := by
        intro h1
        apply hi1
        apply φ.injective
        rw [h1, map_one]
      have hcomm : φ i * φ g = φ g * φ i := by
        rw [← map_mul, ← map_mul, hg]
      have hgg := w2_sq_eq_one (φ i) (φ g) hφi hφi1 hcomm
      apply φ.injective
      rw [map_mul, map_one]
      exact hgg
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using key (g : D) (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  ·
    exfalso
    have hcard := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h).1 rfl
    rw [hcard] at h16
    exact w1_ordA_one_not_sixteen_dvd hmod h16
  ·
    exfalso
    obtain ⟨a, -, hfa, -, hcard⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.card_ree_model hR
    have h8 : 3 ^ f % 8 = 3 := by
      obtain ⟨a', rfl⟩ : ∃ a', f = 2 * a' + 1 := ⟨a, hfa⟩
      exact w1_three_pow_odd_mod_eight a'
    rw [hcard] at h16
    exact w1_ree_not_sixteen_dvd (by omega) h16
  ·
    exfalso
    rw [CFSG.GH74.card_of_isSporadic_J1 hJ] at h16
    norm_num at h16

end CFSG.RankThree.GF2n.Smith81.Smith23E1.KFacts
