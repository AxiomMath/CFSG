module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieTools
public import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith
public import CFSG.RankThree.PartTwo.Sec15.Wales154L3Two
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Rank

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem false_of_isoLThreePi_of_isLThreeEpsAt_two {X : Type} [Group X] {p e k : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (he : 1 ≤ e) (hk : 1 ≤ k) (hX : Sec4.IsoLThreePi X p e)
    (h2 : IsLThreeEpsAt X 2 k) : False := by
  have hpp : p.Prime := Fact.out
  have hpi : ¬ Sec4.IsoLThreePi X 2 k := fun h2' => by
    have hdvd : p ∣ 2 ^ k :=
      Sec19.Step1917EqProof.eq_of_isoLThreePi he hk hX h2' ▸ dvd_pow_self p (by omega)
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))
  have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have hne : 2 ^ k % 3 ≠ 0 := fun h0 => by
      have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0)
      norm_num at h32
    omega
  rcases h2 with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩ <;> rcases hmod with h1 | h1
  · exact hpi (Or.inl ⟨h1, ⟨φ⟩⟩)
  · exact Sec4.RonanEps.false_of_isTypeEps_of_isoLThreePi
      ⟨2, k, inferInstance, by norm_num, hk, Or.inl ⟨h1, ⟨φ⟩⟩⟩ he hX
  · exact Sec4.RonanEps.false_of_isTypeEps_of_isoLThreePi
      ⟨2, k, inferInstance, by norm_num, hk, Or.inr ⟨h1, h2q, ⟨φ⟩⟩⟩ he hX
  · exact hpi (Or.inr ⟨h1, ⟨φ⟩⟩)

theorem not_dvd_pow_three_sub_one_three_mul_add_one {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 3 - 1) ∣ 3 * (q ^ 3 + 1) := by
  intro h
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h6 : (q ^ 3 - 1) ∣ 6 := by
    have h1 : (q ^ 3 - 1) ∣ 3 * (q ^ 3 - 1) := dvd_mul_left _ _
    have h2 := Nat.dvd_sub h h1
    rwa [show 3 * (q ^ 3 + 1) - 3 * (q ^ 3 - 1) = 6 by omega] at h2
  have hle := Nat.le_of_dvd (by norm_num : 0 < 6) h6
  omega

theorem not_dvd_pow_three_add_one_three_mul_sub_one {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 3 + 1) ∣ 3 * (q ^ 3 - 1) := by
  intro h
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h6 : (q ^ 3 + 1) ∣ 6 := by
    have h1 : (q ^ 3 + 1) ∣ 3 * (q ^ 3 + 1) := dvd_mul_left _ _
    have h2 := Nat.dvd_sub h1 h
    rwa [show 3 * (q ^ 3 + 1) - 3 * (q ^ 3 - 1) = 6 by omega] at h2
  have hle := Nat.le_of_dvd (by norm_num : 0 < 6) h6
  omega

theorem not_dvd_of_three_mul_eq {x z M a b : ℕ} (hM : 0 < M) (hx : 3 * x = M * a)
    (hz : 3 * z = M * (3 * b)) (hab : ¬ a ∣ 3 * b) : ¬ x ∣ z := fun hd =>
  hab (Nat.dvd_of_mul_dvd_mul_left hM (hx ▸ hz ▸ Nat.mul_dvd_mul_left 3 hd))

theorem eq_one_of_isoLThreePi_of_isLThreeEpsAt_of_dvd {X Z : Type} [Group X] [Group Z]
    {p f e : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (he : 1 ≤ e)
    (hX : Sec4.IsoLThreePi X p (f * e)) (hZ : IsLThreeEpsAt Z p f)
    (hd : Nat.card X ∣ Nat.card Z) : e = 1 := by
  have hfe : 1 ≤ f * e := Nat.mul_pos (by omega) (by omega)
  obtain ⟨π, hqmod, hXc⟩ := Sec14.Ronan148W.card_mul_three_of_isoLThreePi hfe hX
  have hQ3dvd : (p ^ (f * e)) ^ 3 ∣ Nat.card X * 3 :=
    ⟨((p ^ (f * e)) ^ 2 - 1) * cond π ((p ^ (f * e)) ^ 3 - 1) ((p ^ (f * e)) ^ 3 + 1),
      by rw [hXc]; ring⟩
  have hq0 : p ^ (f * e) % 3 ≠ 0 := by
    rcases π with _ | _ <;> simp [Sec4.ModThree] at hqmod <;> omega
  have hQcop : Nat.Coprime ((p ^ (f * e)) ^ 3) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact fun hd3 => hq0 (Nat.mod_eq_zero_of_dvd (Nat.prime_three.dvd_of_dvd_pow hd3))
  have hle : f * e ≤ f * 1 := by
    simpa using Wales154.le_of_pow_three_dvd_of_isLThreeEpsAt hf hZ
      (hQcop.dvd_of_dvd_mul_right hQ3dvd) hd
  exact Nat.le_antisymm (Nat.le_of_mul_le_mul_left hle (by omega)) he

theorem pow_three_mul_sq_sub_one_pos {q : ℕ} (hq : 2 ≤ q) : 0 < q ^ 3 * (q ^ 2 - 1) := by
  have h4 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)

theorem card_eq_of_isoLThreePi_of_projSL_of_dvd {X Z : Type} [Group X] [Group Z]
    {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hX : Sec4.IsoLThreePi X p f)
    (hZ : Nat.card Z * Nat.gcd 3 (p ^ f - 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)))
    (hd : Nat.card X ∣ Nat.card Z) : Nat.card Z = Nat.card X := by
  have hq2 : 2 ≤ p ^ f := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨π, hqmod, hXc⟩ := Sec14.Ronan148W.card_mul_three_of_isoLThreePi hf hX
  cases π
  ·
    have hqmod' : p ^ f % 3 = 2 := by simpa [Sec4.ModThree] using hqmod
    have hg : Nat.gcd 3 (p ^ f - 1) = 1 := by
      rw [Wales154.gcd_three_eq]
      have h : (p ^ f - 1) % 3 ≠ 0 := by omega
      simp [h]
    rw [hg, Nat.mul_one] at hZ
    exact absurd hd (not_dvd_of_three_mul_eq (pow_three_mul_sq_sub_one_pos hq2)
      (by simpa [Nat.mul_comm] using hXc) (by rw [hZ]; ring)
      (not_dvd_pow_three_add_one_three_mul_sub_one hq2))
  ·
    have hqmod' : p ^ f % 3 = 1 := by simpa [Sec4.ModThree] using hqmod
    have hg : Nat.gcd 3 (p ^ f - 1) = 3 := by
      rw [Wales154.gcd_three_eq]
      have h : (p ^ f - 1) % 3 = 0 := by omega
      simp [h]
    rw [hg] at hZ
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3)
      (hZ.trans (by rw [← Nat.mul_assoc]; simpa using hXc.symm))

theorem card_eq_of_isoLThreePi_of_projSU_of_dvd {X Z : Type} [Group X] [Group Z]
    {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hX : Sec4.IsoLThreePi X p f)
    (hZ : Nat.card Z * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)))
    (hd : Nat.card X ∣ Nat.card Z) : Nat.card Z = Nat.card X := by
  have hq2 : 2 ≤ p ^ f := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨π, hqmod, hXc⟩ := Sec14.Ronan148W.card_mul_three_of_isoLThreePi hf hX
  cases π
  ·
    have hqmod' : p ^ f % 3 = 2 := by simpa [Sec4.ModThree] using hqmod
    have hg : Nat.gcd 3 (p ^ f + 1) = 3 := by
      rw [Wales154.gcd_three_eq]
      have h : (p ^ f + 1) % 3 = 0 := by omega
      simp [h]
    rw [hg] at hZ
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3)
      (hZ.trans (by rw [← Nat.mul_assoc]; simpa using hXc.symm))
  ·
    have hqmod' : p ^ f % 3 = 1 := by simpa [Sec4.ModThree] using hqmod
    have hg : Nat.gcd 3 (p ^ f + 1) = 1 := by
      rw [Wales154.gcd_three_eq]
      have h : (p ^ f + 1) % 3 ≠ 0 := by omega
      simp [h]
    rw [hg, Nat.mul_one] at hZ
    exact absurd hd (not_dvd_of_three_mul_eq (pow_three_mul_sq_sub_one_pos hq2)
      (by simpa [Nat.mul_comm] using hXc) (by rw [hZ]; ring)
      (not_dvd_pow_three_sub_one_three_mul_add_one hq2))

theorem card_eq_of_isoLThreePi_of_isLThreeEpsAt_of_dvd {X Z : Type} [Group X] [Group Z]
    {p f e : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (he : 1 ≤ e)
    (hX : Sec4.IsoLThreePi X p (f * e)) (hZ : IsLThreeEpsAt Z p f)
    (hd : Nat.card X ∣ Nat.card Z) : Nat.card Z = Nat.card X := by
  rw [eq_one_of_isoLThreePi_of_isLThreeEpsAt_of_dvd hf he hX hZ hd, Nat.mul_one] at hX
  rcases Wales154.card_eq_of_isLThreeEpsAt hf hZ with hZsl | ⟨-, hZsu⟩
  · exact card_eq_of_isoLThreePi_of_projSL_of_dvd hf hX hZsl hd
  · exact card_eq_of_isoLThreePi_of_projSU_of_dvd hf hX hZsu hd

theorem card_alternatingGroup_seven_le_of_case148Two_ii {X : Type} [Group X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      (∃ _ : Fact (Nat.Prime 5), Nonempty (X ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
      (∃ _ : Fact (Nat.Prime 5), Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1))) :
    Nat.card (alternatingGroup (Fin 7)) ≤ Nat.card X := by
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  rcases h with ⟨⟨φ⟩⟩ | ⟨h5, ⟨φ⟩⟩ | ⟨h5, ⟨φ⟩⟩
  · rw [hA7, Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    norm_num
  · let : Fact (Nat.Prime 5) := h5
    rw [hA7]
    rcases Wales154.card_eq_of_isLThreeEpsAt (p := 5) (f := 2) (by norm_num)
        (Or.inl ⟨φ⟩) with h | ⟨-, h⟩
    · rw [show Nat.gcd 3 (5 ^ 2 - 1) = 3 by
        rw [Wales154.gcd_three_eq]
        norm_num] at h
      norm_num at h
      omega
    · rw [show Nat.gcd 3 (5 ^ 2 + 1) = 1 by
        rw [Wales154.gcd_three_eq]
        norm_num] at h
      norm_num at h
      omega
  · let : Fact (Nat.Prime 5) := h5
    rw [hA7]
    rcases Wales154.card_eq_of_isLThreeEpsAt (p := 5) (f := 1) (by norm_num)
        (Or.inr ⟨by norm_num, ⟨φ⟩⟩) with h | ⟨-, h⟩
    · rw [show Nat.gcd 3 (5 ^ 1 - 1) = 1 by
        rw [Wales154.gcd_three_eq]
        norm_num] at h
      norm_num at h
      omega
    · rw [show Nat.gcd 3 (5 ^ 1 + 1) = 3 by
        rw [Wales154.gcd_three_eq]
        norm_num] at h
      norm_num at h
      omega

end CFSG.RankThree.PartTwo.Sec15.GagenL3
