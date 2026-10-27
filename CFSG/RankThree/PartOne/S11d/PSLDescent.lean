module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.RankThree.PartOne.KC.LinearNonsplitSubfieldFixedGroup
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank
  (StatedLieAdmissible StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_equiv_projectiveSL {T : Type} [Group T] {p f₀ n : ℕ}
    (hM : LieModel T .PSL n 2 (p * f₀)) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K), Finite K ∧ CharP K 2 ∧ Nat.card K = 2 ^ (p * f₀) ∧
      Nonempty (T ≃* projectiveSL n K) := by
  have hC : StatedClassicalModel T .PSL n 2 (p * f₀) :=
    (lieModel_classical_iff (by decide)).mp hM
  obtain ⟨⟨-, hf, hn2, -, -⟩, K, _, _, hK, ⟨e0⟩⟩ := hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := p * f₀) (by
    rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨hn2, K, inferInstance, inferInstance, inferInstance, hK,
    ⟨(e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩

theorem exists_fieldAut_model_PSL {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hn3 : 3 ≤ n) (hM : LieModel T .PSL n 2 (p * f₀)) (hf₀ : 1 ≤ f₀)
    (hpq : ¬ p ∣ 2 ^ (p * f₀) - 1) (α : MulAut T) (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    ∃ (K : Type) (_ : Field K), Finite K ∧ CharP K 2 ∧ Nat.card K = 2 ^ (p * f₀) ∧
      ∃ (φ : T ≃* projectiveSL n K) (σ : K ≃+* K), orderOf σ = p ∧
        Nat.card (semilinearFixedSubfield σ) = 2 ^ f₀ ∧ MulAut.congr φ α = fieldAut n K σ := by
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL hM
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1) := by
    rw [hK]
    exact fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  have : Finite (projectiveSL n K) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (projectiveSL n K) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by
    rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p := by
    refine orderOf_eq_prime hα'p ?_
    intro h1
    exact hα'inn (h1 ▸ (innerAut (projectiveSL n K)).one_mem)
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn3
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hE : MulAut.congr e α ∈ semilinearAutGroup n K := by
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2' : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2'
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ linearAutGroup n K := by
    intro hD
    exact hα'inn (OutStructure.linear_D2 hp hn3 hdiagK _ hD 1
      (by rw [pow_one, hα'p]; exact Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two hf
      hn3 hK
  obtain ⟨hpf, σ, hσord, ⟨h, -, hαh⟩, hkcard⟩ := hdesc p hp hp2 _ hE hD hα'ord
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hkcard
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK,
    e.trans (h⁻¹ : MulAut (projectiveSL n K)), σ, hσord, hkcard, ?_⟩
  have : MulAut.congr (e.trans (h⁻¹ : MulAut (projectiveSL n K))) α =
      h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ := rfl
  rw [this, hαh]
  group

theorem fixed_eq_range_PSL {p f₀ n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn3 : 3 ≤ n)
    (hf₀ : 1 ≤ f₀) {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2 ^ (p * f₀))
    (hpq : ¬ p ∣ 2 ^ (p * f₀) - 1) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    {x : projectiveSL n K | fieldAut n K σ x = x} =
      ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range : Set (projectiveSL n K)) := by
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  exact (nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp
    (by omega) (by omega) hf hn3 hK hpq σ hσ).2.2.1

end CFSG.RankThree.PartOne
