module

public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import CFSG.RankThree.PartOne.S11c.J4Extraspecial
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap
public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LinearAlgebra Module Polynomial Subgroup
open scoped commutatorElement

theorem orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 11 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

section Group

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem extraspecial_eleven_facts (hQ : IsExtraspecialPGroup 11 Q) (hexp : Monoid.exponent Q = 11)
    {x y z : Q} (hz : z = ⁅x, y⁆) :
    (∀ g : Q, Commute g z) ∧ (∀ g : Q, g ^ 11 = 1) ∧ y⁻¹ * x * y = x * z := by
  have hzc : ∀ g : Q, Commute g z := by
    intro g
    have hmem : z ∈ Subgroup.center Q := by
      rw [← hQ.2.1, hz, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    exact (Subgroup.mem_center_iff.1 hmem) g
  have hexp' : ∀ g : Q, g ^ 11 = 1 := fun g => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one g
  refine ⟨hzc, hexp', ?_⟩
  have hzy : y⁻¹ * z * y = z := by
    rw [mul_assoc, ← (hzc y).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  calc y⁻¹ * x * y = y⁻¹ * (x * y * x⁻¹ * y⁻¹) * y * x := by group
    _ = y⁻¹ * z * y * x := by rw [hz, commutatorElement_def]
    _ = z * x := by rw [hzy]
    _ = x * z := ((hzc x).eq).symm

theorem zpowers_eq_center_of_mem (hQ : IsExtraspecialPGroup 11 Q) (hexp : Monoid.exponent Q = 11)
    {β : Q} (hβZ : β ∈ Subgroup.center Q) (hβ : β ≠ 1) :
    Subgroup.zpowers β = Subgroup.center Q := by
  have hexp' : ∀ g : Q, g ^ 11 = 1 := fun g => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one g
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hβZ) ?_
  rw [hQ.2.2.2, Nat.card_zpowers]
  have h1 : orderOf β ∣ 11 := orderOf_dvd_of_pow_eq_one (hexp' β)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp h1 with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hβ
  · exact h.ge

theorem center_eq_zpowers (hQ : IsExtraspecialPGroup 11 Q) (hexp : Monoid.exponent Q = 11)
    {x y z : Q} (hz : z = ⁅x, y⁆) (hz1 : z ≠ 1) :
    Subgroup.zpowers z = Subgroup.center Q := by
  have hzZ : z ∈ Subgroup.center Q := by
    rw [← hQ.2.1, hz, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  exact zpowers_eq_center_of_mem hQ hexp hzZ hz1

theorem exists_conj_eq_mul_center (hQ : IsExtraspecialPGroup 11 Q)
    (hexp : Monoid.exponent Q = 11) {z x : Q}
    (hzgen : Subgroup.zpowers z = Subgroup.center Q) (hx : x ∉ Subgroup.center Q) :
    ∃ y : Q, y⁻¹ * x * y = x * z := by
  have hexp' : ∀ g : Q, g ^ 11 = 1 := fun g => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one g
  obtain ⟨g, hg⟩ : ∃ g : Q, g * x ≠ x * g := by
    by_contra h
    push Not at h
    exact hx (Subgroup.mem_center_iff.mpr h)
  set c := x⁻¹ * (g⁻¹ * x * g) with hc
  have hcZ : c ∈ Subgroup.center Q := by
    rw [← hQ.2.1]
    have e : c = ⁅x⁻¹, g⁻¹⁆ := by
      rw [hc, commutatorElement_def, inv_inv, inv_inv]
      group
    rw [e, commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)
  have hc1 : c ≠ 1 := by
    intro h1
    apply hg
    have h' : x = g⁻¹ * x * g := inv_mul_eq_one.mp (by rw [← hc]; exact h1)
    calc g * x = g * (g⁻¹ * x * g) := by rw [← h']
      _ = x * g := by group
  have hcc : ∀ h : Q, h * c = c * h := fun h => Subgroup.mem_center_iff.mp hcZ h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, z ^ m = c := by
    have hcz : c ∈ Subgroup.zpowers z := hzgen ▸ hcZ
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hcz)
  have hpm : ¬ 11 ∣ m := by
    rintro ⟨t, rfl⟩
    apply hc1
    rw [← hm, pow_mul, hexp', one_pow]
  obtain ⟨k, hk⟩ := exists_pow_pow_eq_self (p := 11) (hexp' z) hpm
  have hgxg : g⁻¹ * x * g = x * c := by rw [hc]; group
  have hiter : ∀ n : ℕ, (g ^ n)⁻¹ * x * g ^ n = x * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : g⁻¹ * c ^ n * g = c ^ n := by
        rw [mul_assoc, ← ((Commute.pow_right (hcc g) n)).eq, ← mul_assoc, inv_mul_cancel,
          one_mul]
      calc (g ^ (n + 1))⁻¹ * x * g ^ (n + 1) = g⁻¹ * ((g ^ n)⁻¹ * x * g ^ n) * g := by
            rw [pow_succ]; group
        _ = g⁻¹ * (x * c ^ n) * g := by rw [ih]
        _ = (g⁻¹ * x * g) * (g⁻¹ * c ^ n * g) := by group
        _ = x * c * c ^ n := by rw [hgxg, hcn]
        _ = x * c ^ (n + 1) := by rw [pow_succ', mul_assoc]
  refine ⟨g ^ k, ?_⟩
  rw [hiter, ← hm, hk]

end Group

section Setting

variable {Q : Type*} [Group Q] [Finite Q] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

variable (hQ : IsExtraspecialPGroup 11 Q) (hexp : Monoid.exponent Q = 11)
  {x y z : Q} (hz : z = ⁅x, y⁆) (ρ : Representation (ZMod 2) Q V)

include hQ hexp hz

omit [Finite Q] in
theorem finrank_centralImage_center_facts (hρz : ρ z ≠ 1) :
    11 * 10 ≤ finrank (ZMod 2) (centralImage ρ z) ∧
      10 ∣ finrank (ZMod 2) (centralImage ρ z) := by
  obtain ⟨hzc, hexp', hyx⟩ := extraspecial_eleven_facts hQ hexp hz
  have hp2 : (11 : ℕ) ≠ 2 := by norm_num
  have hTp : ρ z ^ 11 = 1 := by rw [← map_pow, hexp', map_one]
  have hW : ∀ g : Q, ∀ s ∈ centralImage ρ z, ρ g s ∈ centralImage ρ z :=
    fun g => mapsTo_centralImage ((hzc g).map ρ)
  have hW0 : centralImage ρ z ≠ ⊥ := by
    intro h
    apply hρz
    refine LinearMap.ext fun v => ?_
    have hv : (ρ z - 1) v ∈ centralImage ρ z := ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at hv
    have : ρ z v - v = 0 := by simpa using hv
    simpa [sub_eq_zero] using this
  have : Nontrivial (centralImage ρ z) := Submodule.nontrivial_iff_ne_bot.mpr hW0
  have hΦ := irreducible_cyclotomic_two (p := 11) hp2 orderOf_two_zmod_eleven
  have hKzero := aeval_centralImageOp_cyclotomic (ρ := ρ) (p := 11) hp2 hTp
  have hK : IsField (centralImageAlgebra ρ z) :=
    isField_adjoin_singleton_of_aeval_eq_zero hΦ _ hKzero
  have hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = 11 - 1 := by
    rw [centralImageAlgebra, finrank_adjoin_singleton_of_aeval_eq_zero hΦ
      (cyclotomic.monic 11 (ZMod 2)) _ hKzero, natDegree_cyclotomic_two]
  constructor
  · have hlow : ∀ k : Fin 11, 11 - 1 ≤ finrank (ZMod 2) ↥(centralImage ρ z ⊓
        cosetFixed ρ z x k) := by
      intro k
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (inf_cosetFixed_ne_bot hp2 hzc hexp' hyx le_rfl hW hW0 k)
      rw [← hKdim]
      exact finrank_centralImageAlgebra_le hK inf_le_left (inf_cosetFixed_invariant hzc hW k)
        hw hw0
    have hsum := sum_finrank_inf_cosetFixed_le (ρ := ρ) (x := x) hp2 hzc hexp'
      (S := centralImage ρ z)
    have h2 : ∑ _k : Fin 11, (11 - 1) ≤ ∑ k : Fin 11, finrank (ZMod 2)
        ↥(centralImage ρ z ⊓ cosetFixed ρ z x k) := Finset.sum_le_sum fun k _ => hlow k
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
    omega
  · have : Finite (centralImage ρ z) := Module.finite_of_finite (ZMod 2)
    have : Finite (Module.End (ZMod 2) (centralImage ρ z)) :=
      Finite.of_injective _ (DFunLike.coe_injective (F := centralImage ρ z →ₗ[ZMod 2] _))
    have : Finite (centralImageAlgebra ρ z) := Subtype.finite
    have : Module.Finite (ZMod 2) (centralImageAlgebra ρ z) := Module.Finite.of_finite
    let _ : Field (centralImageAlgebra ρ z) := hK.toField
    have h := Module.finrank_mul_finrank (ZMod 2) (centralImageAlgebra ρ z) (centralImage ρ z)
    rw [hKdim] at h
    exact ⟨_, h.symm⟩

omit [Finite Q] in
theorem finrank_centralFixed_center_eq_two (hρz : ρ z ≠ 1)
    (hV : finrank (ZMod 2) V = 112) : finrank (ZMod 2) (centralFixed ρ z) = 2 := by
  obtain ⟨hzc, hexp', hyx⟩ := extraspecial_eleven_facts hQ hexp hz
  have hTp : ρ z ^ 11 = 1 := by rw [← map_pow, hexp', map_one]
  have hUW := isCompl_centralFixed_centralImage (p := 11) (by norm_num) hTp
  have hdim := Submodule.finrank_add_eq_of_isCompl hUW
  obtain ⟨h1, k, hk⟩ := finrank_centralImage_center_facts hQ hexp hz ρ hρz
  have := Submodule.finrank_le (centralImage ρ z)
  omega

variable (hcard : Nat.card Q = 11 ^ 3) (hgen : Subgroup.closure ({x, y} : Set Q) = ⊤)
include hcard hgen

omit [Finite Q] in
theorem trivial_on_centralFixed (hρz : ρ z ≠ 1) (hV : finrank (ZMod 2) V = 112) :
    ∀ g : Q, ∀ u ∈ centralFixed ρ z, ρ g u = u := by
  have hU2 := finrank_centralFixed_center_eq_two hQ hexp hz ρ hρz hV
  exact (extraspecial_prime_cyclotomic_minimal_module (p := 11) (by norm_num)
    orderOf_two_zmod_eleven hQ hcard hexp hgen hz ρ (r := 2) (by norm_num) (by omega) hU2).2.1

theorem finrank_centralFixed_le_twelve (hρz : ρ z ≠ 1) (hV : finrank (ZMod 2) V = 112) {β : Q}
    (hβ : β ≠ 1) : finrank (ZMod 2) (centralFixed ρ β) ≤ 12 := by
  obtain ⟨hzc, hexp', hyx⟩ := extraspecial_eleven_facts hQ hexp hz
  have hp2 : (11 : ℕ) ≠ 2 := by norm_num
  have hz1 : z ≠ 1 := fun h => hρz (by rw [h, map_one])
  have hzgen := center_eq_zpowers hQ hexp hz hz1
  have hU2 := finrank_centralFixed_center_eq_two hQ hexp hz ρ hρz hV
  have hUtriv := trivial_on_centralFixed hQ hexp hz ρ hcard hgen hρz hV
  by_cases hβZ : β ∈ Subgroup.center Q
  ·
    have hzβ : z ∈ Subgroup.zpowers β := by
      rw [zpowers_eq_center_of_mem hQ hexp hβZ hβ]
      exact hzgen ▸ Subgroup.mem_zpowers z
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hzβ)
    have hle : centralFixed ρ β ≤ centralFixed ρ z := by
      intro v hv
      simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] at hv ⊢
      rw [← hm, map_pow, Module.End.pow_apply]
      exact Function.iterate_fixed hv m
    have := Submodule.finrank_mono hle
    omega
  ·
    obtain ⟨y', hy'⟩ := exists_conj_eq_mul_center hQ hexp hzgen hβZ
    have hTp : ρ z ^ 11 = 1 := by rw [← map_pow, hexp', map_one]
    have hUW := isCompl_centralFixed_centralImage (p := 11) hp2 hTp
    have hdim := Submodule.finrank_add_eq_of_isCompl hUW
    have hWdim : finrank (ZMod 2) (centralImage ρ z) = 11 * (11 - 1) := by omega
    have hW0 : centralImage ρ z ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hWdim
      omega
    have : Nontrivial (centralImage ρ z) := Submodule.nontrivial_iff_ne_bot.mpr hW0
    have hΦ := irreducible_cyclotomic_two (p := 11) hp2 orderOf_two_zmod_eleven
    have hKzero := aeval_centralImageOp_cyclotomic (ρ := ρ) (p := 11) hp2 hTp
    have hK : IsField (centralImageAlgebra ρ z) :=
      isField_adjoin_singleton_of_aeval_eq_zero hΦ _ hKzero
    have hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = 11 - 1 := by
      rw [centralImageAlgebra, finrank_adjoin_singleton_of_aeval_eq_zero hΦ
        (cyclotomic.monic 11 (ZMod 2)) _ hKzero, natDegree_cyclotomic_two]
    have h10 := finrank_inf_cosetFixed (ρ := ρ) (x := β) hp2 hzc hexp' hy' hK hKdim hWdim 0
    have h10' : finrank (ZMod 2) ↥(centralImage ρ z ⊓ cosetFixed ρ z β 0) = 10 := by
      simpa using h10
    have hsub : centralFixed ρ β ≤ centralFixed ρ z ⊔
        (centralImage ρ z ⊓ cosetFixed ρ z β 0) := by
      intro v hv
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp (hUW.codisjoint.eq_top ▸
        Submodule.mem_top (x := v))
      refine Submodule.mem_sup.mpr ⟨u, hu, w, ?_, rfl⟩
      refine Submodule.mem_inf.mpr ⟨hw, ?_⟩
      rw [mem_cosetFixed]
      refine ⟨hw, ?_⟩
      have hv' : ρ β (u + w) = u + w := by
        simpa [centralFixed, sub_eq_zero] using hv
      rw [pow_zero, mul_one]
      have h1 : ρ β u = u := hUtriv β u hu
      rw [map_add, h1] at hv'
      simpa using hv'
    have h1 := Submodule.finrank_mono hsub
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (centralFixed ρ z)
      (centralImage ρ z ⊓ cosetFixed ρ z β 0)
    omega

theorem finrank_centralImage_ge (hρz : ρ z ≠ 1) (hV : finrank (ZMod 2) V = 112) {β : Q}
    (hβ : β ≠ 1) : 100 ≤ finrank (ZMod 2) (centralImage ρ β) := by
  obtain ⟨-, hexp', -⟩ := extraspecial_eleven_facts hQ hexp hz
  have hTp : ρ β ^ 11 = 1 := by rw [← map_pow, hexp', map_one]
  have hUW := isCompl_centralFixed_centralImage (p := 11) (by norm_num) hTp
  have hdim := Submodule.finrank_add_eq_of_isCompl hUW
  have := finrank_centralFixed_le_twelve hQ hexp hz ρ hcard hgen hρz hV hβ
  omega

end Setting

end CFSG.RankThree.PartOne
