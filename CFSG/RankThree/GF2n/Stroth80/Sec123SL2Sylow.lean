module

public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Grp

open CFSG.ClassicalGroups.SpecialLinear

local notation "SLtwo" => Matrix.SpecialLinearGroup (Fin 2)

theorem sl2Idx01 : (0 : Fin 2) ≠ 1 := by decide

theorem sl2Idx10 : (1 : Fin 2) ≠ 0 := by decide

abbrev sl2Upper (K : Type) [Field K] : Subgroup (SLtwo K) := rootGroup K sl2Idx01

abbrev sl2Lower (K : Type) [Field K] : Subgroup (SLtwo K) := rootGroup K sl2Idx10

theorem sl2Upper_sup_Lower (K : Type) [Field K] : sl2Upper K ⊔ sl2Lower K = ⊤ := by
  refine eq_top_of_forall_transvection_mem _ fun i j hij c => ?_
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact Subgroup.mem_sup_left (transvection_mem_rootGroup sl2Idx01 c)
  · exact Subgroup.mem_sup_right (transvection_mem_rootGroup sl2Idx10 c)
  · exact (hij rfl).elim

theorem sl2_coe_t01 {K : Type} [Field K] (x : K) :
    ((Matrix.SpecialLinearGroup.transvection sl2Idx01 x : SLtwo K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]

theorem sl2_coe_t10 {K : Type} [Field K] (x : K) :
    ((Matrix.SpecialLinearGroup.transvection sl2Idx10 x : SLtwo K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, 0; x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]

theorem sl2_det {K : Type} [Field K] (h : SLtwo K) :
    (h : Matrix (Fin 2) (Fin 2) K) 0 0 * (h : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (h : Matrix (Fin 2) (Fin 2) K) 0 1 * (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
  have h2 := h.2
  rw [Matrix.det_fin_two] at h2
  exact h2

def sl2ConjU {K : Type} [Field K] (h : SLtwo K) (s : K) : SLtwo K :=
  h * Matrix.SpecialLinearGroup.transvection sl2Idx01 s * h⁻¹

theorem sl2_coe_conjU {K : Type} [Field K] (h : SLtwo K) (s : K) :
    ((sl2ConjU h s : SLtwo K) : Matrix (Fin 2) (Fin 2) K) =
      !![1 - (h : Matrix (Fin 2) (Fin 2) K) 0 0 * (h : Matrix (Fin 2) (Fin 2) K) 1 0 * s,
        (h : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * s;
        -((h : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 * s),
        1 + (h : Matrix (Fin 2) (Fin 2) K) 0 0 * (h : Matrix (Fin 2) (Fin 2) K) 1 0 * s] := by
  have hdet := sl2_det h
  unfold sl2ConjU
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, sl2_coe_t01]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (first | ring1 | linear_combination hdet | linear_combination (-1 : K) * hdet)

theorem sl2_map_conj_upper {K : Type} [Field K] (h : SLtwo K)
    (hc : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    Subgroup.map (MulAut.conj h).toMonoidHom (sl2Upper K) = sl2Upper K := by
  have ha : (h : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h0
    have hd := sl2_det h
    rw [h0, hc] at hd
    simp at hd
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := mem_rootGroup.1 hy
    refine mem_rootGroup.2 ⟨(h : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * t, ?_⟩
    apply Subtype.ext
    show ((Matrix.SpecialLinearGroup.transvection sl2Idx01
        ((h : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * t) : SLtwo K) :
          Matrix (Fin 2) (Fin 2) K) =
      ((sl2ConjU h t : SLtwo K) : Matrix (Fin 2) (Fin 2) K)
    rw [sl2_coe_conjU, sl2_coe_t01, hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro hx
    obtain ⟨t, rfl⟩ := mem_rootGroup.1 hx
    have hat : (h : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 *
        (t / (h : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2) = t := by
      first
        | (field_simp; done)
        | (rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (pow_ne_zero 2 ha), mul_one])
    refine ⟨Matrix.SpecialLinearGroup.transvection sl2Idx01
      (t / (h : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2), mem_rootGroup.2 ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    show ((sl2ConjU h (t / (h : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2) : SLtwo K) :
        Matrix (Fin 2) (Fin 2) K) =
      ((Matrix.SpecialLinearGroup.transvection sl2Idx01 t : SLtwo K) :
        Matrix (Fin 2) (Fin 2) K)
    rw [sl2_coe_conjU, sl2_coe_t01, hc, hat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem sl2_lower_mem_sup {K : Type} [Field K] (h : SLtwo K)
    (hc : (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) (τ : K) :
    Matrix.SpecialLinearGroup.transvection sl2Idx10 τ ∈
      sl2Upper K ⊔ Subgroup.map (MulAut.conj h).toMonoidHom (sl2Upper K) := by
  obtain ⟨x, hx⟩ : ∃ x : K, (h : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (h : Matrix (Fin 2) (Fin 2) K) 1 0 * x := by
    refine ⟨(h : Matrix (Fin 2) (Fin 2) K) 0 0 / (h : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    first
      | (field_simp; done)
      | (field_simp; ring)
  obtain ⟨s, rfl⟩ : ∃ s : K, τ = -((h : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 * s) := by
    refine ⟨-τ / (h : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2, ?_⟩
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hid : Matrix.SpecialLinearGroup.transvection sl2Idx10
      (-((h : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 * s)) =
      Matrix.SpecialLinearGroup.transvection sl2Idx01 (-x) * sl2ConjU h s *
        Matrix.SpecialLinearGroup.transvection sl2Idx01 x := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, sl2_coe_conjU,
      sl2_coe_t01, sl2_coe_t01, sl2_coe_t10, hx]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hid]
  refine mul_mem (mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_))
    (Subgroup.mem_sup_left ?_)
  · exact transvection_mem_rootGroup sl2Idx01 (-x)
  · exact Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom
      (transvection_mem_rootGroup sl2Idx01 s)
  · exact transvection_mem_rootGroup sl2Idx01 x

theorem sl2_sup_conj_top {K : Type} [Field K] (h : SLtwo K)
    (hV : Subgroup.map (MulAut.conj h).toMonoidHom (sl2Upper K) ≠ sl2Upper K) :
    sl2Upper K ⊔ Subgroup.map (MulAut.conj h).toMonoidHom (sl2Upper K) = ⊤ := by
  by_cases hc : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · exact absurd (sl2_map_conj_upper h hc) hV
  · rw [eq_top_iff, ← sl2Upper_sup_Lower K]
    refine sup_le le_sup_left ?_
    intro y hy
    obtain ⟨τ, rfl⟩ := mem_rootGroup.1 hy
    exact sl2_lower_mem_sup h hc τ

theorem sl2_card_upper (K : Type) [Field K] : Nat.card (sl2Upper K) = Nat.card K := by
  have e := MonoidHom.ofInjective (rootHom_injective (K := K) sl2Idx01)
  exact (Nat.card_congr e.toEquiv).symm

theorem sl2_card (K : Type) [Field K] [Finite K] :
    Nat.card (SLtwo K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem sl2_finite (K : Type) [Field K] [Finite K] : Finite (SLtwo K) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [sl2_card K]
  have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h2 : 4 ≤ Nat.card K ^ 2 := by nlinarith
  exact Nat.mul_ne_zero (by omega) (by omega)

theorem sl2_card_factorization (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card K = 2 ^ (Nat.card (SLtwo K)).factorization 2 := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have hq1 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq0 : Nat.card K ≠ 0 := by omega
  have hq2 : 2 ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self 2 m.ne_zero
  have hsq : 2 ∣ Nat.card K ^ 2 := dvd_pow hq2 two_ne_zero
  have hsq4 : 4 ≤ Nat.card K ^ 2 := by nlinarith
  have hodd : ¬ 2 ∣ Nat.card K ^ 2 - 1 := by omega
  have hne : Nat.card K ^ 2 - 1 ≠ 0 := by omega
  rw [sl2_card K, Nat.factorization_mul hq0 hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, hq,
    Nat.factorization_pow_self Nat.prime_two]

theorem sl2_exists_conj (K : Type) [Field K] [Finite K] [CharP K 2] (H : Subgroup (SLtwo K))
    (hH : Nat.card H = Nat.card K) :
    ∃ g : SLtwo K, H = Subgroup.map (MulAut.conj g).toMonoidHom (sl2Upper K) := by
  haveI : Finite (SLtwo K) := sl2_finite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 (SLtwo K)) := Finite.of_injective
    (fun S : Sylow 2 (SLtwo K) => ((S : Subgroup (SLtwo K)) : Set (SLtwo K)))
    (fun S T hST => Sylow.ext (SetLike.coe_injective hST))
  obtain ⟨S₀, hS₀⟩ : ∃ S : Sylow 2 (SLtwo K), (S : Subgroup (SLtwo K)) = sl2Upper K :=
    ⟨Sylow.ofCard (p := 2) (sl2Upper K)
      ((sl2_card_upper K).trans (sl2_card_factorization K)), rfl⟩
  obtain ⟨S₁, hS₁⟩ : ∃ S : Sylow 2 (SLtwo K), (S : Subgroup (SLtwo K)) = H :=
    ⟨Sylow.ofCard (p := 2) H (hH.trans (sl2_card_factorization K)), rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SLtwo K) S₀ S₁
  refine ⟨g, ?_⟩
  have h2 : ((g • S₀ : Sylow 2 (SLtwo K)) : Subgroup (SLtwo K)) =
      (S₁ : Subgroup (SLtwo K)) := by
    rw [hg]
  rw [Sylow.coe_subgroup_smul, hS₀, hS₁] at h2
  ext x
  rw [← h2, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  all_goals exact Iff.rfl

theorem two_sylow_generate {K : Type} [Field K] [Finite K] [CharP K 2]
    {P P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hc : Nat.card P = Nat.card K)
    (hc' : Nat.card P' = Nat.card K) (hne : P ≠ P') : P ⊔ P' = ⊤ := by
  obtain ⟨g, rfl⟩ := sl2_exists_conj K P hc
  obtain ⟨g', rfl⟩ := sl2_exists_conj K P' hc'
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj (g⁻¹ * g')).toMonoidHom =
      (MulAut.conj g').toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    show g * (g⁻¹ * g' * x * (g⁻¹ * g')⁻¹) * g⁻¹ = g' * x * g'⁻¹
    group
  have hV : Subgroup.map (MulAut.conj (g⁻¹ * g')).toMonoidHom (sl2Upper K) ≠ sl2Upper K := by
    intro heq
    apply hne
    have e1 : Subgroup.map (MulAut.conj g).toMonoidHom (sl2Upper K) =
        Subgroup.map (MulAut.conj g).toMonoidHom
          (Subgroup.map (MulAut.conj (g⁻¹ * g')).toMonoidHom (sl2Upper K)) := by
      rw [heq]
    rw [e1, Subgroup.map_map, hcomp]
  have htop : Subgroup.map (MulAut.conj g).toMonoidHom
      (sl2Upper K ⊔ Subgroup.map (MulAut.conj (g⁻¹ * g')).toMonoidHom (sl2Upper K)) = ⊤ := by
    rw [sl2_sup_conj_top _ hV]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  rw [Subgroup.map_sup, Subgroup.map_map, hcomp] at htop
  exact htop

end CFSG.RankThree.GF2n.Stroth80.SL2Grp
