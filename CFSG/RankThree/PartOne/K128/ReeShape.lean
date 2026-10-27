module

public import CFSG.RankThree.PartOne.K128.ReeSector
public import CFSG.RankThree.PartOne.K128.ReeArith
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.K128.ReeTori

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.LargeReeOrder

section Casts

theorem int_dvd_sub_one' {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q - 1) : (p : ℤ) ∣ (q : ℤ) - 1 := by
  have := Int.natCast_dvd_natCast.2 h
  rwa [Nat.cast_sub hq, Nat.cast_one] at this

theorem int_dvd_sub_add_one' {p q r : ℕ} (hr : r ≤ q) (h : p ∣ q - r + 1) :
    (p : ℤ) ∣ (q : ℤ) - r + 1 := by
  have := Int.natCast_dvd_natCast.2 h
  rwa [Nat.cast_add, Nat.cast_sub hr, Nat.cast_one] at this

theorem tsq' (a : ℕ) : (2 ^ (a + 1)) ^ 2 = 2 * 2 ^ (2 * a + 1) := tsq a

theorem le_two_mul_of_pow_dvd_sq {p v M : ℕ} (hp : p.Prime) (hM : M ≠ 0) (h : p ^ v ∣ M ^ 2) :
    v ≤ 2 * M.factorization p := by
  have h2 := (hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hM)).1 h
  rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h2

theorem natCast_ne_zero_algebraicClosure {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [CharP (AlgebraicClosure K) 2] :
    (p : AlgebraicClosure K) ≠ 0 := fun h0 =>
  hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).1 h0)).symm

end Casts

section Gamma

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem pow_factorization_card_reeGamma_dvd_phi6 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣
      (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1]
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  refine pow_factorization_dvd_of_not_dvd_cofactor ?_ (Nat.succ_ne_zero _)
    (not_dvd_cofactor_six hp hp5 hq1 hpq)
  ring

theorem pow_factorization_card_reeGamma_dvd_phi12p (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ m12p (2 ^ (2 * a + 1)) (2 ^ (a + 1))) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣
      m12p (2 ^ (2 * a + 1)) (2 ^ (a + 1)) := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1]
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  rw [← m12_mul hq1 (tsq a)]
  refine pow_factorization_dvd_of_not_dvd_cofactor (R := q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
    (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * m12m q (2 ^ (a + 1))) ?_ (by simp [m12p])
    (not_dvd_cofactor_12p hp hp5 hq1 (tsq a) hpq)
  ring

theorem pow_factorization_card_reeGamma_dvd_phi12m (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ m12m (2 ^ (2 * a + 1)) (2 ^ (a + 1))) :
    p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ∣
      m12m (2 ^ (2 * a + 1)) (2 ^ (a + 1)) := by
  rw [(large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1]
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  rw [← m12_mul hq1 (tsq a)]
  have hM : m12m q (2 ^ (a + 1)) ≠ 0 := by
    intro h0
    rw [h0] at hpq
    exact absurd (m12_mul hq1 (tsq a)) (by
      rw [h0, mul_zero]
      have : q ^ 4 - q ^ 2 + 1 ≠ 0 := Nat.succ_ne_zero _
      exact fun h => this h.symm)
  refine pow_factorization_dvd_of_not_dvd_cofactor (R := q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
    (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * m12p q (2 ^ (a + 1))) ?_ hM
    (not_dvd_cofactor_12m hp hp5 hq1 (tsq a) hpq)
  ring

end Gamma

section Shapes

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem sylowShape_ree_phi1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) - 1) :
    SylowShape p 2 ((2 ^ (2 * a + 1) - 1).factorization p) (ReeTag.F4.reeGamma K a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd : Odd (p ^ (2 ^ (2 * a + 1) - 1).factorization p) :=
    (hp.odd_of_ne_two (by omega)).pow
  have hmM : ((p ^ (2 ^ (2 * a + 1) - 1).factorization p : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 1 := by
    have := int_dvd_sub_one' hq1 (Nat.ordProj_dvd (2 ^ (2 * a + 1) - 1) p)
    exact_mod_cast this
  obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi1 (L := AlgebraicClosure K) D.isFrob hodd hmM
  obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi1 Φ hΦ hΦF
  refine sylowShape_of_rootsOfUnity_hom hp (natCast_ne_zero_algebraicClosure hp (by omega)) Ψ hΨ ?_
  exact le_two_mul_of_pow_dvd_sq hp (by omega)
    (pow_factorization_card_reeGamma_dvd_phi1 hK hp (by omega) hpq)

theorem sylowShape_ree_phi2 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) + 1) :
    SylowShape p 2 ((2 ^ (2 * a + 1) + 1).factorization p) (ReeTag.F4.reeGamma K a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd : Odd (p ^ (2 ^ (2 * a + 1) + 1).factorization p) :=
    (hp.odd_of_ne_two (by omega)).pow
  have hmM : ((p ^ (2 ^ (2 * a + 1) + 1).factorization p : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 1 := by
    have := Int.natCast_dvd_natCast.2 (Nat.ordProj_dvd (2 ^ (2 * a + 1) + 1) p)
    exact_mod_cast this
  obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi2 (L := AlgebraicClosure K) D.isFrob hodd hmM
  obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi2 Φ hΦ hΦF
  refine sylowShape_of_rootsOfUnity_hom hp (natCast_ne_zero_algebraicClosure hp (by omega)) Ψ hΨ ?_
  exact le_two_mul_of_pow_dvd_sq hp (by omega)
    (pow_factorization_card_reeGamma_dvd_phi2 hK hp (by omega) hpq)

theorem sylowShape_ree_phi4 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1) :
    SylowShape p 2 (((2 ^ (2 * a + 1)) ^ 2 + 1).factorization p) (ReeTag.F4.reeGamma K a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set e := ((2 ^ (2 * a + 1)) ^ 2 + 1).factorization p with he
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two (by omega)).pow
  have hpe : p ^ e ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := Nat.ordProj_dvd _ p
  have hLE : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ 2 * e :=
    le_two_mul_of_pow_dvd_sq hp (by omega)
      (pow_factorization_card_reeGamma_dvd_four hK hp (by omega) hpq)
  have hpL := natCast_ne_zero_algebraicClosure (K := K) hp (by omega : p ≠ 2)
  rcases dvd_phi4_cases hp (by omega) hpq with ⟨hp1, hnd⟩ | ⟨hp1, hnd⟩
  · have hdiv : p ^ e ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
      have h1 : p ^ e ∣ (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) *
          (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by rw [phi4_factor a]; exact hpe
      exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_right
        h1
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
      have := Int.natCast_dvd_natCast.2 hdiv
      exact_mod_cast this
    obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi4p (L := AlgebraicClosure K) D.isFrob hodd hmM
    obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi4p Φ hΦ hΦF
    exact sylowShape_of_rootsOfUnity_hom hp hpL Ψ hΨ hLE
  · have hdiv : p ^ e ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      have h1 : p ^ e ∣ (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) *
          (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by rw [phi4_factor a]; exact hpe
      exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_left
        h1
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      exact int_dvd_sub_add_one' hle hdiv |> fun h => by exact_mod_cast h
    obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi4m (L := AlgebraicClosure K) D.isFrob hodd hmM
    obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi4m Φ hΦ hΦF
    exact sylowShape_of_rootsOfUnity_hom hp hpL Ψ hΨ hLE

theorem sylowShape_ree (hK : Nat.card K = 2 ^ (2 * a + 1)) {d : ℕ}
    (hd : d = 1 ∨ d = 2 ∨ d = 4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ phiF4 d (2 ^ (2 * a + 1))) :
    SylowShape p 2 ((phiF4 d (2 ^ (2 * a + 1))).factorization p) (ReeTag.F4.reeGamma K a) := by
  rcases hd with rfl | rfl | rfl
  · exact sylowShape_ree_phi1 hK hp hp5 hpd
  · exact sylowShape_ree_phi2 hK hp hp5 hpd
  · exact sylowShape_ree_phi4 hK hp hp5 hpd

theorem pRank_le_one_ree_phi6 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) :
    CFSG.pRank p (ReeTag.F4.reeGamma K a) ≤ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hle2 : 2 ^ (2 * a + 1) ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set e := ((2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1).factorization p with he
  have hmM : ((p ^ e : ℕ) : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 := by
    have h1 := Int.natCast_dvd_natCast.2
      (Nat.ordProj_dvd ((2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) p)
    push_cast [Nat.cast_sub hle2] at h1
    exact h1
  obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi6 (L := AlgebraicClosure K) D.isFrob hmM
  obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi6 Φ hΦ hΦF
  have hle : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ e :=
    (hp.pow_dvd_iff_le_factorization (Nat.succ_ne_zero _)).1
      (pow_factorization_card_reeGamma_dvd_phi6 hK hp hp5 hpq)
  exact pRank_le_one_of_cyclic_pSubgroups hp
    (isCyclic_of_rootsOfUnity_hom hp (natCast_ne_zero_algebraicClosure hp (by omega)) Ψ hΨ hle)

theorem pRank_le_one_ree_phi12 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1) :
    CFSG.pRank p (ReeTag.F4.reeGamma K a) ≤ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have htq := t_mul_le (tsq a)
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL := natCast_ne_zero_algebraicClosure (K := K) hp (by omega : p ≠ 2)
  rw [← m12_mul hq1 (tsq a)] at hpq
  rcases (Nat.Prime.dvd_mul hp).1 hpq with h | h
  · set e := (m12p (2 ^ (2 * a + 1)) (2 ^ (a + 1))).factorization p with he
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 +
        2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1) := by
      have h1 := Int.natCast_dvd_natCast.2
        (Nat.ordProj_dvd (m12p (2 ^ (2 * a + 1)) (2 ^ (a + 1))) p)
      push_cast [m12p] at h1
      exact h1
    obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi12p (L := AlgebraicClosure K) D.isFrob hmM
    obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi12p Φ hΦ hΦF
    have hne : m12p (2 ^ (2 * a + 1)) (2 ^ (a + 1)) ≠ 0 := by simp [m12p]
    have hle : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ e :=
      (hp.pow_dvd_iff_le_factorization hne).1
        (pow_factorization_card_reeGamma_dvd_phi12p hK hp hp5 h)
    exact pRank_le_one_of_cyclic_pSubgroups hp (isCyclic_of_rootsOfUnity_hom hp hpL Ψ hΨ hle)
  · set e := (m12m (2 ^ (2 * a + 1)) (2 ^ (a + 1))).factorization p with he
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 -
        2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1) := by
      have h1 := Int.natCast_dvd_natCast.2
        (Nat.ordProj_dvd (m12m (2 ^ (2 * a + 1)) (2 ^ (a + 1))) p)
      push_cast [m12m, Nat.cast_sub htq] at h1
      exact h1
    obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi12m (L := AlgebraicClosure K) D.isFrob hmM
    obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi12m Φ hΦ hΦF
    have hne : m12m (2 ^ (2 * a + 1)) (2 ^ (a + 1)) ≠ 0 := by
      intro h0
      have := m12_mul hq1 (tsq a)
      rw [h0, mul_zero] at this
      exact Nat.succ_ne_zero _ this.symm
    have hle : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ e :=
      (hp.pow_dvd_iff_le_factorization hne).1
        (pow_factorization_card_reeGamma_dvd_phi12m hK hp hp5 h)
    exact pRank_le_one_of_cyclic_pSubgroups hp (isCyclic_of_rootsOfUnity_hom hp hpL Ψ hΨ hle)

end Shapes

end CFSG.RankThree.PartOne.K128
