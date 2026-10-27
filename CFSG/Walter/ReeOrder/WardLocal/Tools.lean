module

public import CFSG.CharacterTheory.Semidihedral.Principal.FullPrimePartBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Walter.ReeOrder.Ward.Columns4

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

theorem exists_maximal_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ m : Ideal ComplexAlgebraicIntegers, m.IsMaximal ∧ (p : ComplexAlgebraicIntegers) ∈ m := by
  let : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hPprime : P.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out)
  have hPbot : P ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hPmax : P.IsMaximal := hPprime.isMaximal hPbot
  have hker : RingHom.ker (algebraMap ℤ ComplexAlgebraicIntegers) ≤ P := by
    intro z hz
    rw [RingHom.mem_ker] at hz
    have hz' : (z : ℂ) = 0 := by
      have := congrArg Subtype.val hz
      simpa using this
    have : z = 0 := by exact_mod_cast hz'
    rw [this]
    exact P.zero_mem
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
  have hpQ : ((p : ℤ) : ComplexAlgebraicIntegers) ∈ Q := by
    have hpP : (p : ℤ) ∈ P := Ideal.subset_span rfl
    rw [← hQ] at hpP
    simpa using hpP
  exact ⟨Q, hQmax, by simpa using hpQ⟩

theorem charP_quotient {p : ℕ} [hp : Fact p.Prime] {m : Ideal ComplexAlgebraicIntegers}
    (hm : m.IsMaximal) (hpm : (p : ComplexAlgebraicIntegers) ∈ m) :
    CharP (ComplexAlgebraicIntegers ⧸ m) p := by
  have := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk m) p,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hpm

theorem mem_range_basis {S : Type} [Group S] [Fintype S]
    (basis : FiniteIrreducibleCharacterBasis S) {χ : S → ℂ} (hχ : χ ∈ BlocksIrr S) :
    ∃ label, (basis.representation label).character = χ := by
  rw [blocksIrr_eq_irreducible_characters] at hχ
  obtain ⟨data, hirr, rfl⟩ := hχ
  exact finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr

theorem basis_mem_blocksIrr {S : Type} [Group S] [Fintype S]
    (basis : FiniteIrreducibleCharacterBasis S) (l : basis.index) :
    (basis.representation l).character ∈ BlocksIrr S :=
  ⟨(basis.representation l).vector, inferInstance, inferInstance, inferInstance,
    (basis.representation l).representation, basis.irreducible l, rfl⟩

theorem defect_zero_vanish {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (p : ℕ) [Fact p.Prime] (hdeg : ((p ^ (Nat.card G).factorization p : ℕ) : ℤ) ∣ deg χ)
    {g : G} (hg : p ∣ orderOf g) : χ g = 0 := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨m, hm, hpm⟩ := exists_maximal_prime p
  have : m.IsMaximal := hm
  have : CharP (ComplexAlgebraicIntegers ⧸ m) p := charP_quotient hm hpm
  obtain ⟨label, rfl⟩ := mem_range_basis basis hχ
  have hdim : (deg (basis.representation label).character : ℂ) =
      (Module.finrank ℂ (basis.representation label).vector : ℂ) := by
    rw [deg_eq (basis_mem_blocksIrr basis label)]
    exact Representation.char_one _
  have hdim' : deg (basis.representation label).character =
      (Module.finrank ℂ (basis.representation label).vector : ℤ) := by exact_mod_cast hdim
  rw [hdim'] at hdeg
  exact (full_prime_part_character_degree_singleton_block_singular_vanishing
    basis m p label (by exact_mod_cast hdeg)).2 g hg

theorem exists_conj_mem_of_full {G : Type*} [Group G] [Finite G] {r : ℕ} [hr : Fact r.Prime]
    (H : Subgroup G) (hH : r ^ (Nat.card G).factorization r ∣ Nat.card H) {y : G}
    (hy : IsPGroup r (Subgroup.zpowers y)) : ∃ g : G, g⁻¹ * y * g ∈ H := by
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  let P : Sylow r H := default
  let P' : Subgroup G := (P : Subgroup H).map H.subtype
  have hP'card : Nat.card P' = r ^ (Nat.card G).factorization r := by
    have h1 : Nat.card P' = Nat.card P := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
    rw [h1, P.card_eq_multiplicity]
    have hle : (Nat.card H).factorization r ≤ (Nat.card G).factorization r :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card H) r
    have hge : (Nat.card G).factorization r ≤ (Nat.card H).factorization r :=
      (Nat.Prime.pow_dvd_iff_le_factorization hr.out Nat.card_pos.ne').mp hH
    rw [le_antisymm hle hge]
  let P'' : Sylow r G := Sylow.ofCard P' (by rw [hP'card])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P'' Q
  have hyQ : y ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
  refine ⟨g, ?_⟩
  have hmem : (MulAut.conj g)⁻¹ • y ∈ P' := hyQ
  rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hmem
  obtain ⟨z, -, hz⟩ := Subgroup.mem_map.mp hmem
  rw [← hz]
  exact z.2

theorem isIntegral_irr {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (g : G) : IsIntegral ℤ (χ g) := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨label, rfl⟩ := mem_range_basis basis hχ
  exact finite_character_value_isIntegral _ g

theorem exists_int_of_isIntegral {z : ℂ} (hz : IsIntegral ℤ z) {r : ℚ} (hr : z = r) :
    ∃ n : ℤ, z = n := by
  have hrat : IsIntegral ℤ r := IsIntegral.tower_bot_of_field (B := ℂ) (by
    simpa only [← hr, eq_ratCast] using hz)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrat
  refine ⟨n, ?_⟩
  rw [hr, ← hn]
  simp

end CFSG.Walter.WardLocal
