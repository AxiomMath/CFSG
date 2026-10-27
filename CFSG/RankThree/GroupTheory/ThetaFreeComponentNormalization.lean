module

public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.CentralCover.AlternatingFourGroupWitness
public import CFSG.RankThree.CentralCover.LinearUnitaryFourGroupWitness
import CFSG.RankThree.CentralCover.SymplecticFourGroupWitness
import CFSG.RankThree.CentralCover.HigherClassicalFourGroupWitness
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
import CFSG.RankThree.CentralLift.LinearTwoLifting

public section

namespace CFSG.RankThree

open Subgroup CFSG CFSG.RankThree.CentralExtension CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem theta_free_alternating_component_normalization_at_three
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ n : ℕ, 5 ≤ n →
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) → A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ n : ℕ, 5 ≤ n →
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) → A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ n : ℕ, 5 ≤ n →
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) → A ≤ normalizer (L : Set G) := by
    rintro L hL n hn ⟨e⟩
    refine normalizes_of_noncentral_three_element hθ he hq h3 hA hL fun _ hZ3 => ?_
    set π := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = center L := ker_comp_mk'_center e
    obtain ⟨⟨U, ⟨hU2, hUV, hinj⟩, -⟩, hcov⟩ :=
      CentralCover.alternating_central_three_cover_split_four_group_witness_cover hn π hπ
        hker.le (hker ▸ hZ3)
    obtain ⟨-, -, x, hxN, hxo, -, -, hxZ, -⟩ := hcov U hU2 hUV hinj
    refine ⟨U, fun hb => ?_, hU2, x, hxN, hxo ▸ pow_orderOf_eq_one x, hxZ⟩
    have hV := (CentralCover.alternating_central_three_cover_split_four_group_witness_quotient
      hn).2.1
    rw [← hUV, hb, Subgroup.map_bot] at hV
    have h4 := hV.card_four
    rw [Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

open CentralCover in
theorem theta_free_linear_and_odd_unitary_three_component_normalization {G : Type} [Group G]
    [Finite G] (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G,
      ((∃ p f : ℕ, Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSL 3 p f) ∨
        (∃ p f : ℕ, 2 < p ∧
          Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSU 3 p f)) →
      A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L →
      ((∃ p f : ℕ, Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSL 3 p f) ∨
        (∃ p f : ℕ, 2 < p ∧
          Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSU 3 p f)) →
      A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G,
      ((∃ p f : ℕ, Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSL 3 p f) ∨
        (∃ p f : ℕ, 2 < p ∧
          Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSU 3 p f)) →
      A ≤ normalizer (L : Set G) := by
    rintro L hL (⟨p, f, -, F, _, _, -, ⟨e⟩⟩ | ⟨p, f, hp2, ⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩)
    · refine normalizes_of_cover_witness hθ he hq h3 hA hL e fun π hπ hZ hZ3 => ?_
      by_cases h2 : ringChar F = 2
      · have : CharP F 2 := ringChar.eq_iff.1 h2
        obtain ⟨⟨U, ⟨hU2, hUV, hinj⟩, -⟩, hcov⟩ :=
          linear_and_odd_unitary_three_central_cover_four_group_witness_linear_even_cover
            π hπ hZ hZ3
        obtain ⟨-, -, x, hxN, hxo, -, ⟨u₁, _u₂, _u₃, hU, hu₁, -⟩, hxZ, -⟩ := hcov U hU2 hUV hinj
        exact ⟨U, ne_bot_of_coe_eq_four hU hu₁, hU2, x, hxN, hxo, hxZ⟩
      · obtain ⟨⟨U, ⟨hU2, hUV, hinj⟩, -⟩, hcov⟩ :=
          linear_and_odd_unitary_three_central_cover_four_group_witness_linear_odd_cover
            h2 π hπ hZ hZ3
        obtain ⟨-, -, x, hxN, hxo, -, ⟨u₁, _u₂, _u₃, hU, hu₁, -⟩, hxZ, -⟩ := hcov U hU2 hUV hinj
        exact ⟨U, ne_bot_of_coe_eq_four hU hu₁, hU2, x, hxN, hxo, hxZ⟩
    · refine normalizes_of_cover_witness hθ he hq h3 hA hL e fun π hπ hZ hZ3 => ?_
      have hqpp : IsPrimePow (p ^ f) := (Nat.Prime.prime hp).isPrimePow.pow (by omega)
      have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two (by omega)).pow
      obtain ⟨⟨U, ⟨hU2, hUV, hinj⟩, -⟩, hcov⟩ :=
        CentralCover.linear_and_odd_unitary_three_central_cover_four_group_witness_unitary_odd_cover
          hqpp hqodd hF π hπ hZ hZ3
      obtain ⟨-, -, x, hxN, hxo, -, ⟨u₁, _u₂, _u₃, hU, hu₁, -⟩, hxZ, -⟩ := hcov U hU2 hUV hinj
      exact ⟨U, ne_bot_of_coe_eq_four hU hu₁, hU2, x, hxN, hxo, hxZ⟩
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

theorem theta_free_higher_classical_component_normalization_at_three {G : Type} [Group G]
    [Finite G] (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) t n p f →
      (((t = .PSL ∨ t = .PSU) ∧ 4 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨
        (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)) →
      A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) t n p f →
      (((t = .PSL ∨ t = .PSU) ∧ 4 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨
        (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)) →
      A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) t n p f →
      (((t = .PSL ∨ t = .PSU) ∧ 4 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨
        (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)) →
      A ≤ normalizer (L : Set G) := by
    intro L hL t n p f hmodel ht
    obtain ⟨V, a, -, -, -, -, -, -, -, -, -, -, hcov⟩ :=
      CentralCover.higher_classical_central_three_cover_four_group_witness hmodel ht
    refine normalizes_of_cover_witness hθ he hq h3 hA hL (MulEquiv.refl _)
      fun π hπ hZ hZ3 => ?_
    obtain ⟨⟨U, ⟨hU2, hUV, hinj⟩, -⟩, hcov'⟩ := hcov L π hπ hZ hZ3
    obtain ⟨-, -, x, hxN, hxo, -, ⟨u₁, _u₂, _u₃, hU, hu₁, -⟩, hxZ, -⟩ := hcov' U hU2 hUV hinj
    exact ⟨U, ne_bot_of_coe_eq_four hU hu₁, hU2, x, hxN, hxo, hxZ⟩
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

theorem theta_free_symplectic_four_component_normalization_at_three {G : Type} [Group G]
    [Finite G] (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ p f : ℕ,
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSp 2 p f →
      A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ p f : ℕ,
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSp 2 p f →
      A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ p f : ℕ,
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSp 2 p f →
      A ≤ normalizer (L : Set G) := by
    rintro L hL p f ⟨-, F, _, _, -, ⟨e⟩⟩
    obtain ⟨V, a, -, -, -, -, -, -, -, -, -, hcov⟩ :=
      CentralCover.symplectic_four_central_three_cover_four_group_witness F
    refine normalizes_of_cover_witness hθ he hq h3 hA hL e fun π hπ hZ hZ3 => ?_
    obtain ⟨⟨U, ⟨hU2, hUV, hinj⟩, -⟩, hcov'⟩ := hcov L π hπ hZ hZ3
    obtain ⟨-, -, x, hxN, hxo, -, ⟨u₁, _u₂, _u₃, hU, hu₁, -⟩, hxZ, -⟩ := hcov' U hU2 hUV hinj
    exact ⟨U, ne_bot_of_coe_eq_four hU hu₁, hU2, x, hxN, hxo, hxZ⟩
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

section Nine

open Matrix CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

noncomputable abbrev slProj (F : Type) [Field F] :
    SpecialLinearGroup (Fin 2) F →* StatedProj (StatedSL 2 F) :=
  (CentralCover.statedProjMk (StatedSL 2 F)).comp
    (specialLinearGroupEquivStatedSL 2 F).toMonoidHom

theorem slProj_eq_one_iff (x : SpecialLinearGroup (Fin 2) F) :
    slProj F x = 1 ↔ x ∈ center (SpecialLinearGroup (Fin 2) F) := by
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    ← map_center_eq_statedScalars]
  exact (Subgroup.mem_map_iff_mem (specialLinearGroupEquivStatedSL 2 F).injective).trans Iff.rfl

section Matrices

theorem sl_mul_eq {A B C : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : (A : Matrix (Fin 2) (Fin 2) F) * B = C) : A * B = C :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact h)

noncomputable def q9i : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by rw [det_fin_two_of]; ring⟩

noncomputable def q9z : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![-1, 0; 0, -1], by rw [det_fin_two_of]; ring⟩

theorem q9z_mem_center : q9z (F := F) ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [q9z]

theorem q9i_mul_q9i : q9i * q9i = (q9z : Matrix.SpecialLinearGroup (Fin 2) F) := by
  refine sl_mul_eq ?_
  change !![(0 : F), 1; -1, 0] * !![0, 1; -1, 0] = !![-1, 0; 0, -1]
  rw [Matrix.mul_fin_two]
  ext a b; fin_cases a <;> fin_cases b <;> simp

variable (ω : F) (hω : ω ^ 2 = -1) (h3 : (3 : F) = 0)

noncomputable def q9j : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![ω, 0; 0, -ω], by rw [det_fin_two_of]; linear_combination (-1 : F) * hω⟩

noncomputable def q9h : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1 - ω, ω - 1; 1 + ω, 1 + ω], by
    rw [det_fin_two_of]; linear_combination (-2 : F) * hω + (1 : F) * h3⟩

noncomputable def q9b : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, ω; -ω, -1], by rw [det_fin_two_of]; linear_combination (1 : F) * hω + (-1 : F) * h3⟩

theorem q9j_mul_q9j : q9j ω hω * q9j ω hω = q9z := by
  refine sl_mul_eq ?_
  change !![ω, 0; 0, -ω] * !![ω, 0; 0, -ω] = !![-1, 0; 0, -1]
  rw [Matrix.mul_fin_two]
  ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination hω

theorem q9i_mul_q9j : q9i * q9j ω hω = q9j ω hω * q9i * q9z := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change !![(0 : F), 1; -1, 0] * !![ω, 0; 0, -ω] =
    !![ω, 0; 0, -ω] * !![0, 1; -1, 0] * !![-1, 0; 0, -1]
  simp only [Matrix.mul_fin_two]
  ext a b; fin_cases a <;> fin_cases b <;> simp

theorem q9h_pow_three : q9h ω hω h3 ^ 3 = 1 := by
  rw [pow_three]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change !![1 - ω, ω - 1; 1 + ω, 1 + ω] * (!![1 - ω, ω - 1; 1 + ω, 1 + ω] *
    !![1 - ω, ω - 1; 1 + ω, 1 + ω]) = 1
  simp only [Matrix.mul_fin_two, Matrix.one_fin_two]
  ext a b; fin_cases a <;> fin_cases b <;> simp
  · linear_combination (6 - 2 * ω) * hω + (-3 : F) * h3
  · linear_combination (2 * ω - 2) * hω
  · linear_combination (2 * ω + 2) * hω
  · linear_combination (2 * ω + 6) * hω + (-3 : F) * h3

theorem q9h_mul_q9i : q9h ω hω h3 * q9i = q9i * q9j ω hω * q9h ω hω h3 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change !![1 - ω, ω - 1; 1 + ω, 1 + ω] * !![0, 1; -1, 0] =
    !![0, 1; -1, 0] * !![ω, 0; 0, -ω] * !![1 - ω, ω - 1; 1 + ω, 1 + ω]
  simp only [Matrix.mul_fin_two]
  ext a b; fin_cases a <;> fin_cases b <;> simp
  · linear_combination hω
  · linear_combination hω
  · linear_combination (-1 : F) * hω
  · linear_combination hω

theorem q9h_mul_q9j : q9h ω hω h3 * q9j ω hω = q9i * q9h ω hω h3 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change !![1 - ω, ω - 1; 1 + ω, 1 + ω] * !![ω, 0; 0, -ω] =
    !![0, 1; -1, 0] * !![1 - ω, ω - 1; 1 + ω, 1 + ω]
  simp only [Matrix.mul_fin_two]
  ext a b; fin_cases a <;> fin_cases b <;> simp
  · linear_combination (-1 : F) * hω
  · linear_combination (-1 : F) * hω
  · linear_combination hω
  · linear_combination (-1 : F) * hω

theorem q9b_mul_q9h :
    q9b ω hω h3 * q9h ω hω h3 = q9h ω hω h3 * q9h ω hω h3 * q9b ω hω h3 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change !![1, ω; -ω, -1] * !![1 - ω, ω - 1; 1 + ω, 1 + ω] =
    !![1 - ω, ω - 1; 1 + ω, 1 + ω] * !![1 - ω, ω - 1; 1 + ω, 1 + ω] * !![1, ω; -ω, -1]
  simp only [Matrix.mul_fin_two]
  ext a b; fin_cases a <;> fin_cases b <;> simp
  · linear_combination hω
  · linear_combination (3 - 2 * ω) * hω + (2 * ω - 2) * h3
  · linear_combination (2 * ω + 3) * hω + (-2 * ω - 2) * h3
  · linear_combination (-1 : F) * hω

end Matrices

theorem q9i_not_mem_center : q9i (F := F) ∉ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  simp [q9i] at h

theorem q9h_not_mem_center (ω : F) (hω : ω ^ 2 = -1) (h3 : (3 : F) = 0) :
    q9h ω hω h3 ∉ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  simp only [q9h, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h
  have hω1 : ω = 1 := by linear_combination -h
  rw [hω1] at hω
  have h2 : (2 : F) = 0 := by linear_combination hω
  have : (1 : F) = 0 := by linear_combination h3 - h2
  exact one_ne_zero this

theorem psl_two_nine_witness [Finite F] (hF : Nat.card F = 9) :
    ∃ V : Subgroup (StatedProj (StatedSL 2 F)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∃ t ∈ normalizer (V : Set (StatedProj (StatedSL 2 F))), orderOf t = 3 ∧ IsConj t t⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h9 : (9 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hcard] at h
    exact_mod_cast h
  have h3 : (3 : F) = 0 := mul_self_eq_zero.mp (by linear_combination h9)
  obtain ⟨ω, hω'⟩ := (FiniteField.isSquare_neg_one_iff (F := F)).mpr (by rw [hcard]; norm_num)
  have hω : ω ^ 2 = -1 := by rw [sq]; exact hω'.symm
  set ρ := slProj F with hρ
  set vi := ρ q9i
  set vj := ρ (q9j ω hω)
  set a := ρ (q9h ω hω h3)
  set c := ρ (q9b ω hω h3)
  have hz : ρ q9z = 1 := (slProj_eq_one_iff _).2 q9z_mem_center
  have hvi2 : vi * vi = 1 := by rw [← map_mul, q9i_mul_q9i, hz]
  have hvj2 : vj * vj = 1 := by rw [← map_mul, q9j_mul_q9j, hz]
  have hcomm : vi * vj = vj * vi := by
    rw [← map_mul, q9i_mul_q9j, map_mul, map_mul, hz, mul_one]
  have ha3 : a ^ 3 = 1 := by rw [← map_pow, q9h_pow_three, map_one]
  have hai : a * vi = vi * vj * a := by rw [← map_mul, q9h_mul_q9i, map_mul, map_mul]
  have haj : a * vj = vi * a := by rw [← map_mul, q9h_mul_q9j, map_mul]
  have hca : c * a = a * a * c := by rw [← map_mul, q9b_mul_q9h, map_mul, map_mul]
  have hvi1 : vi ≠ 1 := fun h => q9i_not_mem_center ((slProj_eq_one_iff _).1 h)
  have ha1 : a ≠ 1 := fun h => q9h_not_mem_center ω hω h3 ((slProj_eq_one_iff _).1 h)
  have hcyc : ∀ v : StatedProj (StatedSL 2 F), v * v = 1 → IsPGroup 2 (zpowers v) := by
    intro v hv g
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, ← hk, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm, _root_.zpow_mul, zpow_natCast, sq, hv, _root_.one_zpow]
  have hjN : zpowers vj ≤ normalizer (zpowers vi : Set (StatedProj (StatedSL 2 F))) := by
    refine zpowers_le.2 (centralizer_le_normalizer _ ?_)
    rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    exact hcomm.symm
  set V := zpowers vi ⊔ zpowers vj with hV
  have hV2 : IsPGroup 2 V := (hcyc vi hvi2).to_sup_of_normal_left' (hcyc vj hvj2) hjN
  have hviV : vi ∈ V := mem_sup_left (mem_zpowers vi)
  have hvjV : vj ∈ V := mem_sup_right (mem_zpowers vj)
  have hconj_i : a * vi * a⁻¹ = vi * vj := by rw [hai, mul_inv_cancel_right]
  have hconj_j : a * vj * a⁻¹ = vi := by rw [haj, mul_inv_cancel_right]
  have hmap : V.map (MulAut.conj a).toMonoidHom ≤ V := by
    rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hconj_i]
      exact V.mul_mem hviV hvjV
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hconj_j]
      exact hviV
  have haN : a ∈ normalizer (V : Set (StatedProj (StatedSL 2 F))) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge hmap ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
  refine ⟨V, fun hb => hvi1 (by rw [hb] at hviV; exact hviV), hV2, a, haN,
    orderOf_eq_prime ha3 ha1, isConj_iff.2 ⟨c, ?_⟩⟩
  have hinv : a * a = a⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three']
    exact ha3
  rw [hca, mul_inv_cancel_right, hinv]

end Nine

theorem statedScalars_subgroupOf_statedSL_two_eq_bot {F : Type} [Field F] [CharP F 2] :
    (Assembly.LowTwoRank.StatedScalars (Fin 2) F).subgroupOf (Assembly.LowTwoRank.StatedSL 2 F) =
      ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

theorem theta_free_linear_two_component_normalization_at_three {G : Type} [Group G]
    [Finite G] (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, ∀ p f : ℕ,
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → ∀ p f : ℕ,
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      A ≤ normalizer (L : Set G) := by
  have hmain : ∀ L ∈ thetaComponents 3 G, ∀ p f : ℕ,
      Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      A ≤ normalizer (L : Set G) := by
    rintro L hL p f ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩
    have : Fact p.Prime := ⟨hp⟩
    by_cases h9 : p ^ f = 9
    · refine normalizes_of_quotient_witness hθ he hq h3 hA hL fun _ _ => ?_
      exact quotient_witness_of_mulEquiv e
        (psl_two_nine_witness (hF.trans h9) |>.imp fun V ⟨hV, hV2, t, htN, hto, hc⟩ =>
          ⟨hV, hV2, Or.inr ⟨t, htN, hto, hc⟩⟩)
    refine normalizes_of_center_eq_bot hθ he hq h3 hA hL fun hZ3 => ?_
    have hL' := hL
    have : Group.IsPerfect L := hL.1
    set π := e.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hπdef
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = center L := ker_comp_mk'_center e
    have hodd : Odd (Nat.card π.ker) := by
      rw [hker]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
      rw [hk]
      exact Odd.pow (by decide)
    by_cases hp2 : p = 2
    ·
      subst hp2
      have h2 : (2 : F) = 0 := by
        have : Fintype F := Fintype.ofFinite F
        have h := FiniteField.cast_card_eq_zero F
        rw [← Nat.card_eq_fintype_card, hF, Nat.cast_pow] at h
        exact (pow_eq_zero_iff (by omega : f ≠ 0)).1 (by exact_mod_cast h)
      have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
      set j :=
        (QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_statedSL_two_eq_bot).trans
          (QuotientGroup.quotientBot (G := Assembly.LowTwoRank.StatedSL 2 F))
      set π' := j.toMonoidHom.comp π
      have hπ' : Function.Surjective π' := j.surjective.comp hπ
      have hker' : π'.ker = center L := by
        rw [← hker]
        ext x
        simp only [π', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          map_eq_one_iff _ j.injective]
      obtain ⟨s, hs, -⟩ := SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated
        (by norm_num) hπ' hker'.le (hker' ▸ hker ▸ hodd)
      let κ : L →* L :=
        { toFun := fun l => l * (s (π' l))⁻¹
          map_one' := by simp
          map_mul' := fun a b => by
            have hb : b * (s (π' b))⁻¹ ∈ center L := by
              rw [← hker', MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
            have hc := mem_center_iff.1 hb (s (π' a))⁻¹
            calc a * b * (s (π' (a * b)))⁻¹ = a * (b * (s (π' b))⁻¹) * (s (π' a))⁻¹ := by
                  rw [map_mul, map_mul]; group
              _ = a * ((s (π' a))⁻¹ * (b * (s (π' b))⁻¹)) := by rw [mul_assoc, hc]
              _ = a * (s (π' a))⁻¹ * (b * (s (π' b))⁻¹) := by group }
      have hκ : κ = 1 := CentralLift.eq_one_of_isPerfect_of_mem_center κ fun l => by
        change l * (s (π' l))⁻¹ ∈ center L
        rw [← hker', MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
      rw [eq_bot_iff]
      intro z hz
      have hz1 : π' z = 1 := by rw [← MonoidHom.mem_ker, hker']; exact hz
      have h := congrArg (fun φ : L →* L => φ z) hκ
      simp only [MonoidHom.one_apply] at h
      change z * (s (π' z))⁻¹ = 1 at h
      rw [hz1, map_one, inv_one, mul_one] at h
      rw [h]
      exact one_mem _
    ·
      have hcov := (SectionRank.OddCover.odd_psl_two_perfect_odd_cover_kernel hp2 hF π hπ hker.le
        hodd).1 h9
      rw [← hker, hcov]
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

end CFSG.RankThree
