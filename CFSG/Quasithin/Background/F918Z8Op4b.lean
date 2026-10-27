module

public import CFSG.Quasithin.Background.F918Z8Op4b1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.GorensteinWalter CFSG.BenderSuzuki.External
open scoped MatrixGroups

private theorem opq4b_card_psl2 {K : Type} [Field K] [Finite K] {b : ℕ}
    (hq : (2 * b + 1).Prime) (hKq : Nat.card K = 2 * b + 1) :
    Nat.card (PSL2 K) = (2 * b + 1) * (2 * (b * (b + 1))) := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨2 * b + 1, 1, hq, ⟨b, rfl⟩, le_rfl, by rw [hKq, pow_one]⟩
  have hsq : (2 * b + 1) ^ 2 - 1 = 4 * (b * (b + 1)) := by
    have : (2 * b + 1) ^ 2 = 4 * (b * (b + 1)) + 1 := by ring
    omega
  rw [psl2_card_formula K hodd, hKq, hsq]
  exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)

private theorem opq4b_split_data {K : Type} [Field K] [Finite K] {b : ℕ}
    (hq : (2 * b + 1).Prime) (hb : 0 < b) (hKq : Nat.card K = 2 * b + 1) :
    ∃ (U : Subgroup (PSL2 K)) (w : PSL2 K), w * w = 1 ∧ (∀ t ∈ U, w * t * w⁻¹ = t⁻¹) ∧
      U.index = (2 * b + 1) * (2 * (b + 1)) := by
  have : Fact (2 * b + 1).Prime := ⟨hq⟩
  obtain ⟨U, w, -, hUcard, -, -, hw, hwU, -, -⟩ :=
    huppert_II_8_3_split_torus_reflection_data (F := K) (p := 2 * b + 1) (f := 1)
      (by rw [hKq, pow_one])
  have hgcd : Nat.gcd (2 * b + 1 - 1) 2 = 2 := by
    rw [Nat.add_sub_cancel]
    exact Nat.gcd_eq_right (dvd_mul_right 2 b)
  have hUcard' : Nat.card U = b := by
    rw [hUcard, hKq, hgcd]
    omega
  refine ⟨U, w, hw, hwU, ?_⟩
  have h1 := U.card_mul_index
  rw [hUcard', opq4b_card_psl2 hq hKq] at h1
  refine Nat.eq_of_mul_eq_mul_left hb (h1.trans ?_)
  ring

private theorem opq4b_nonsplit_data {K : Type} [Field K] [Finite K] {b : ℕ}
    (hq : (2 * b + 1).Prime) (hKq : Nat.card K = 2 * b + 1) :
    ∃ (S : Subgroup (PSL2 K)) (w : PSL2 K), w * w = 1 ∧ (∀ t ∈ S, w * t * w⁻¹ = t⁻¹) ∧
      S.index = (2 * b + 1) * (2 * b) := by
  have : Fact (2 * b + 1).Prime := ⟨hq⟩
  obtain ⟨S, w, -, hScard, -, -, hw, hwS, -, -⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data (F := K) (p := 2 * b + 1) (f := 1)
      (by rw [hKq, pow_one])
  have hgcd : Nat.gcd (2 * b + 1 - 1) 2 = 2 := by
    rw [Nat.add_sub_cancel]
    exact Nat.gcd_eq_right (dvd_mul_right 2 b)
  have hScard' : Nat.card S = b + 1 := by
    rw [hScard, hKq, hgcd]
    omega
  refine ⟨S, w, hw, hwS, ?_⟩
  have h1 := S.card_mul_index
  rw [hScard', opq4b_card_psl2 hq hKq] at h1
  refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < b + 1) (h1.trans ?_)
  ring

private theorem opq4b_unipotent_data {K : Type} [Field K] [Finite K] {b : ℕ}
    (hq : (2 * b + 1).Prime) (hKq : Nat.card K = 2 * b + 1) {i : K} (hi : i * i = -1) :
    ∃ (T : Subgroup (PSL2 K)) (w : PSL2 K), w * w = 1 ∧ (∀ t ∈ T, w * t * w⁻¹ = t⁻¹) ∧
      T.index = 2 * (b * (b + 1)) := by
  let D : SL(2, K) := ⟨!![i, 0; 0, -i], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : K) * hi⟩
  have hDborel : D ∈ sl2Borel K := by
    rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
    rfl
  have hDD : D * D ∈ Subgroup.center SL(2, K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [D, Matrix.mul_apply, Fin.sum_univ_two, hi]
  refine ⟨psl2UpperUnipotentSubgroup K, psl2QuotientMap K D, ?_, ?_, ?_⟩
  · rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hDD
  · intro t ht
    obtain ⟨c, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff t).mp ht
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv,
      sl2Borel_conj_upperUnipotent hDborel c, sl2UpperUnipotent_inv]
    have : (D.val 0 0) ^ 2 * c = -c := by
      change i ^ 2 * c = -c
      rw [sq, hi]
      ring
    rw [this]
  · have h1 := (psl2UpperUnipotentSubgroup K).card_mul_index
    rw [psl2UpperUnipotentSubgroup_card, hKq, opq4b_card_psl2 hq hKq] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1

theorem a38_invSyl_psl2odd {G : Type} [Group G] {L : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) (hL : IsPSL 2 q 1 ↥L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card L) (hexc : ¬ (p = q ∧ q % 4 = 3)) : InvSylAll L p := by
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨e⟩⟩ := hL
  have : Fact p.Prime := ⟨hp⟩
  have hKq : Nat.card K = q := by simpa using hKcard
  let e' : ↥L ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  refine opq4b_invSylAll_of_equiv e' ?_
  intro P hP hm
  have key : ∀ (T : Subgroup (PSL2 K)) (w : PSL2 K), w * w = 1 →
      (∀ t ∈ T, w * t * w⁻¹ = t⁻¹) → ¬ p ∣ T.index →
      ∃ τ : PSL2 K, τ * τ = 1 ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹ :=
    fun T w hw hwT hT => opq4b_exists_inverts_of_index hw hwT hT hP hm
  obtain ⟨b, rfl⟩ : ∃ b, q = 2 * b + 1 :=
    (hq.odd_of_ne_two (by omega)).exists_bit1.imp fun b hb => by omega
  have hb : 0 < b := by omega
  have hpL' : p ∣ (2 * b + 1) * (2 * (b * (b + 1))) := by
    rw [← opq4b_card_psl2 hq hKq, ← Nat.card_congr e'.toEquiv]
    exact hpL
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hcases : p ∣ 2 * b + 1 ∨ p ∣ b ∨ p ∣ b + 1 := by
    rcases (Nat.Prime.dvd_mul hp).mp hpL' with h | h
    · exact Or.inl h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact absurd h hp2'
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hcases with hpq | hpb | hpb
  ·
    have hpq' : p = 2 * b + 1 := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    have hmod : (2 * b + 1) % 4 ≠ 3 := fun h => hexc ⟨hpq', h⟩
    obtain ⟨i, hi⟩ : IsSquare (-1 : K) := by
      have := Fintype.ofFinite K
      rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card, hKq]
      exact hmod
    obtain ⟨T, w, hw, hwT, hidx⟩ := opq4b_unipotent_data hq hKq hi.symm
    refine key T w hw hwT ?_
    rw [hidx]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2' h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := Nat.le_of_dvd hb h
      omega
    · have := Nat.le_of_dvd (by omega) h
      omega
  ·
    obtain ⟨U, w, hw, hwU, hidx⟩ := opq4b_split_data hq hb hKq
    refine key U w hw hwU ?_
    rw [hidx]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp.one_lt.ne'
        (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpb 2)).mp h))
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2' h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpb).mp h))
  ·
    obtain ⟨S, w, hw, hwS, hidx⟩ := opq4b_nonsplit_data hq hKq
    refine key S w hw hwS ?_
    rw [hidx]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have h2 : p ∣ 2 * b + 1 + 1 := by
        rw [show 2 * b + 1 + 1 = 2 * (b + 1) by ring]
        exact dvd_mul_of_dvd_right hpb 2
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h2))
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2' h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hpb))

end CFSG.Quasithin
