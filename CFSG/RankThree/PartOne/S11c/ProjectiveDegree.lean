module

public import CFSG.RankThree.PartOne.S11c.UnitaryFiveLift
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.RankThree.PartOne.S11c.UnitaryFiveData

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

noncomputable def glToEndIdx (ι : Type) [Fintype ι] [DecidableEq ι] (k : Type) [Field k] :
    GL ι k →* Module.End k (ι → k) :=
  (Matrix.toLinAlgEquiv' (R := k) (n := ι)).toAlgHom.toMonoidHom.comp
    (Units.coeHom (Matrix ι ι k))

theorem glToEndIdx_injective (ι : Type) [Fintype ι] [DecidableEq ι] (k : Type) [Field k] :
    Function.Injective (glToEndIdx ι k) := by
  intro a b hab
  apply Units.ext
  exact (Matrix.toLinAlgEquiv' (R := k) (n := ι)).injective hab

theorem unitary_three_five_projective_degree_bound_idx {B G : Type} [Group B] [Group G]
    (hB : StatedClassicalModel B .PSU 3 5 1) {k : Type} [Field k] [Finite k] (hk : (5 : k) ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : G →* GL ι k) (hρ : Function.Injective ρ)
    (ν : G →* B) (hν : Function.Surjective ν)
    (hker : ∀ g ∈ ν.ker, ρ g ∈ StatedScalars ι k) : 20 ≤ Fintype.card ι := by
  have : Finite G := Finite.of_injective ρ hρ
  obtain ⟨hcard, hperf, -, -⟩ := CFSG.RankThree.Classical.unitary_three_five_model B hB
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcentE : ν.ker ≤ Subgroup.center G := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    have hgs : ρ g ∈ StatedScalars ι k := hker g hg
    have hgc : ρ g ∈ Subgroup.center (GL ι k) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hgs
    exact hρ (by rw [map_mul, map_mul]; exact Subgroup.mem_center_iff.mp hgc (ρ g'))
  obtain ⟨-, hFperf, hFsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective ν hν hcentE hperf
  have : Group.IsPerfect (commutator G) := hFperf
  let νF : commutator G →* B := ν.comp (commutator G).subtype
  have hνF : Function.Surjective νF := hFsurj
  have hcentF : νF.ker ≤ Subgroup.center (commutator G) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    have hgE : (g : G) ∈ ν.ker := hg
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcentE hgE) (g' : G))
  have hC5 := not_five_dvd_card_ker hB νF hνF hcentF
  obtain ⟨x, y, h, m, hm, hx, hy, hcx, hcy, hz5, hz1, hhz⟩ :=
    unitary_three_five_heisenberg_data hB
  obtain ⟨x', y', h', hx', hy', hh', hx5, hcx', hcy', hz5', hhz'⟩ :=
    exists_lifted_heisenberg hνF hcentF hC5 hx hy hcx hcy hhz
  have hz1' : ⁅y', x'⁆ ≠ 1 := by
    intro h1
    apply hz1
    rw [← hx', ← hy', ← map_commutatorElement, h1, map_one]
  let ρ' : commutator G →* Module.End k (ι → k) :=
    (glToEndIdx ι k).comp (ρ.comp (commutator G).subtype)
  have hρinj : Function.Injective ρ' :=
    (glToEndIdx_injective ι k).comp (hρ.comp (commutator G).subtype_injective)
  have key := finrank_ge_twenty_of_heisenberg (k := k) (V := ι → k) hk
    (X := ρ' x') (Z := ρ' ⁅y', x'⁆) (Y := ρ' y') (Yi := ρ' y'⁻¹) (H := ρ' h') (Hi := ρ' h'⁻¹)
    (by rw [← map_mul, inv_mul_cancel, map_one]) (by rw [← map_mul, inv_mul_cancel, map_one])
    (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_pow, hx5, map_one]) (by rw [← map_pow, hz5', map_one])
    (by rw [← map_mul, ← map_mul, hcx'.eq.symm])
    (by rw [← map_mul, ← map_mul, hcy'.eq.symm])
    (by
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      rw [← hcx'.eq, commutatorElement_def]
      group)
    hm
    (by rw [← map_mul, ← map_mul, hhz', map_pow])
    (fun h1 => hz1' (hρinj (h1.trans (map_one ρ').symm)))
  rwa [Module.finrank_fintype_fun_eq_card] at key

theorem degree_ge_twenty_of_proj_model {V : Type} [Group V] (K : Subgroup V)
    (hK : StatedClassicalModel K .PSU 3 5 1) {k : Type} [Field k] [Finite k] (hk : (5 : k) ≠ 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (E : Subgroup (GL ι k)) (e : V ≃* StatedProj E) :
    20 ≤ Fintype.card ι := by
  let q : E →* StatedProj E := QuotientGroup.mk' _
  let P : Subgroup E := (K.map e.toMonoidHom).comap q
  have hPmem : ∀ g : E, g ∈ P ↔ ∃ x ∈ K, e x = q g := by
    intro g
    simp only [P, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  let ρ : P →* GL ι k := E.subtype.comp P.subtype
  have hρ : Function.Injective ρ := E.subtype_injective.comp P.subtype_injective
  have hmemK : ∀ g : P, e.symm (q g) ∈ K := by
    intro g
    obtain ⟨x, hx, hxg⟩ := (hPmem g).1 g.2
    rw [← hxg, MulEquiv.symm_apply_apply]
    exact hx
  let ν : P →* K :=
    (e.symm.toMonoidHom.comp (q.comp P.subtype)).codRestrict K fun g => hmemK g
  have hν : Function.Surjective ν := by
    intro x
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective (StatedScalars ι k |>.subgroupOf E)
      (e (x : V))
    have hg₀P : g₀ ∈ P := (hPmem g₀).2 ⟨x, x.2, hg₀.symm⟩
    refine ⟨⟨g₀, hg₀P⟩, Subtype.ext ?_⟩
    change e.symm (q g₀) = x
    rw [show q g₀ = e (x : V) from hg₀, MulEquiv.symm_apply_apply]
  refine unitary_three_five_projective_degree_bound_idx hK hk ρ hρ ν hν ?_
  intro g hg
  have hg1 : e.symm (q g) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    exact this
  have hq1 : q g = 1 := by
    have := congrArg e hg1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have : (g : E) ∈ (StatedScalars ι k).subgroupOf E := (QuotientGroup.eq_one_iff _).1 hq1
  exact this

@[expose] def naturalDim : StatedLieTag → ℕ → ℕ
  | .PSL, n => n
  | .PSU, n => n
  | .PSp, n => 2 * n
  | .POmegaOdd, n => 2 * n + 1
  | .POmegaPlus, n => 2 * n
  | .POmegaMinus, n => 2 * n
  | _, _ => 0

theorem five_ne_zero_of_charP {k : Type} [Field k] {ℓ : ℕ} [CharP k ℓ] (hℓ : ℓ.Prime)
    (hℓ5 : ℓ ≠ 5) : (5 : k) ≠ 0 := by
  intro h
  have : ℓ ∣ 5 := (CharP.cast_eq_zero_iff k ℓ 5).1 (by exact_mod_cast h)
  exact hℓ5 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 this)

theorem degree_ge_twenty_of_classical_model {V : Type} [Group V] (K : Subgroup V)
    (hK : StatedClassicalModel K .PSU 3 5 1) {τ : StatedLieTag} {n ℓ f : ℕ}
    (hmod : StatedClassicalModel V τ n ℓ f) (hℓ5 : ℓ ≠ 5) : 20 ≤ naturalDim τ n := by
  obtain ⟨⟨hℓ, hf, hadm⟩, hrest⟩ := hmod
  cases τ
  · obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hrest
    have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ hf hk
    simpa [naturalDim] using
      degree_ge_twenty_of_proj_model K hK (five_ne_zero_of_charP hℓ hℓ5) _ e
  · obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hrest
    have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ (k := f * 2) (by omega) (by rw [hk, ← pow_mul])
    simpa [naturalDim] using
      degree_ge_twenty_of_proj_model K hK (five_ne_zero_of_charP hℓ hℓ5) _ e
  · obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hrest
    have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ hf hk
    have := degree_ge_twenty_of_proj_model K hK (five_ne_zero_of_charP hℓ hℓ5) _ e
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    simp only [naturalDim]
    omega
  · obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hrest
    have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ hf hk
    have := degree_ge_twenty_of_proj_model K hK (five_ne_zero_of_charP hℓ hℓ5) _ e
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at this
    simp only [naturalDim]
    omega
  · obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hrest
    have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ hf hk
    have := degree_ge_twenty_of_proj_model K hK (five_ne_zero_of_charP hℓ hℓ5) _ e
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    simp only [naturalDim]
    omega
  · obtain ⟨k, _, _, hk, b, c, -, ⟨e⟩⟩ := hrest
    have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ hf hk
    have := degree_ge_twenty_of_proj_model K hK (five_ne_zero_of_charP hℓ hℓ5) _ e
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    simp only [naturalDim]
    have h4 : 4 ≤ n := hadm
    omega
  all_goals exact hrest.elim

end CFSG.RankThree.PartOne.HNRed
