module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_6_b

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 11.6(c)

This file contains the Section 11 Corollary 11.6(c) statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_mem_normalizer_of_conjBy_eq
    {H : Subgroup G} {g : G} (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by simp [mul_assoc]
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by
            simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by simp [mul_assoc]
    simpa [hxy] using hy

private theorem CFSG.section11_sq_not_mem_of_not_mem_subgroup
    {H : Subgroup G} {g : G} (hg : g ∉ H) :
    g ^ 2 ∉ H := by
  intro hg2
  have horder_odd : Odd (orderOf g) :=
    odd_of_card_dvd IsMinCE.odd_order (orderOf_dvd_natCard g)
  rcases horder_odd with ⟨k, hk⟩
  have hpow_mem : (g ^ 2) ^ (k + 1) ∈ H := H.pow_mem hg2 (k + 1)
  have hpow_eq : (g ^ 2) ^ (k + 1) = g := by
    rw [← pow_mul]
    have hnat : 2 * (k + 1) = orderOf g + 1 := by omega
    rw [hnat, pow_succ, pow_orderOf_eq_one, one_mul]
  exact hg (by simpa [hpow_eq] using hpow_mem)

/-- Corollary 11.6(c). -/
public theorem CFSG.corollary_11_6_c
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    ∃ A1 A2 : Subgroup G,
      A1 ∈ section10PrimeOrderSubgroupsIn p A ∧
        A2 ∈ section10PrimeOrderSubgroupsIn p A ∧
          A1 ≠ A2 ∧
            subgroupCentralizerIn (section10Msigma M) A1 = ⊥ ∧
              subgroupCentralizerIn (section10Msigma M) A2 = ⊥ := by
  classical
  let Pamb : Subgroup G := section10AmbientSylowSubgroup M P
  obtain ⟨g, hgN, hgM⟩ :
      ∃ g : G, g ∈ Subgroup.normalizer (Pamb : Set G) ∧ g ∉ M := by
    by_contra h
    apply h11.not_normalizer_ambient_sylow_le
    intro x hxN
    by_contra hxM
    exact h ⟨x, hxN, hxM⟩
  have hAeqΩ : A = section11OmegaOne p Pamb := by
    simpa [Pamb] using corollary_11_6_a h11
  have hnormA_of_normP :
      ∀ {x : G}, x ∈ Subgroup.normalizer (Pamb : Set G) →
        x ∈ Subgroup.normalizer (A : Set G) := by
    intro x hxN
    have hxΩ : x ∈ Subgroup.normalizer (section11OmegaOne p Pamb : Set G) :=
      section11_normalizer_le_normalizer_omegaOne p Pamb hxN
    simpa [hAeqΩ] using hxΩ
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := hnormA_of_normP hgN
  have hginvN : g⁻¹ ∈ Subgroup.normalizer (Pamb : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Pamb : Set G)) hgN
  have hginvA : g⁻¹ ∈ Subgroup.normalizer (A : Set G) := hnormA_of_normP hginvN
  have hginvM : g⁻¹ ∉ M := by
    intro hgInvM
    exact hgM (by simpa using M.inv_mem hgInvM)
  have hg2M : g ^ 2 ∉ M := section11_sq_not_mem_of_not_mem_subgroup hgM
  have hA_le_Mconj :
      ∀ {x : G}, x ∈ Subgroup.normalizer (A : Set G) → A ≤ M.conjBy x := by
    intro x hxA
    have hxinvA : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.inv_mem (Subgroup.normalizer (A : Set G)) hxA
    have hA_conj_inv : A.conjBy x⁻¹ = A :=
      section11_conjBy_eq_of_mem_normalizer hxinvA
    have hA_conj_inv_le_M : A.conjBy x⁻¹ ≤ M := by
      simpa [hA_conj_inv] using h11.A_le_M
    simpa using
      (section11_le_conjBy_inv_of_conjBy_le
        (G := G) (H := A) (K := M) (g := x⁻¹) hA_conj_inv_le_M)
  have hprime_conj :
      ∀ {x : G}, x ∈ Subgroup.normalizer (A : Set G) →
        A0.conjBy x ∈ section10PrimeOrderSubgroupsIn p A := by
    intro x hxA
    have hA_conj : A.conjBy x = A :=
      section11_conjBy_eq_of_mem_normalizer hxA
    refine ⟨?_, ?_⟩
    · calc
        A0.conjBy x ≤ A.conjBy x := Subgroup.map_mono h11.A0_le_A
        _ = A := hA_conj
    · simpa [section11_card_conjBy A0 x] using h11.A0_prime_order.2
  have hfix_conj :
      ∀ {x : G}, x ∉ M → x ∈ Subgroup.normalizer (A : Set G) →
        subgroupCentralizerIn (section10Msigma M) (A0.conjBy x) = ⊥ := by
    intro x hxM hxA
    simpa [subgroupCentralizerIn] using
      corollary_11_2_b h11 hxM (hA_le_Mconj hxA)
  have hdistinct : A0.conjBy g ≠ A0.conjBy g⁻¹ := by
    intro hEq
    have hconj_sq : A0.conjBy (g ^ 2) = A0 := by
      calc
        A0.conjBy (g ^ 2) = A0.conjBy (g * g) := by rw [pow_two]
        _ = (A0.conjBy g).conjBy g :=
            (section11_conjBy_conjBy (G := G) A0 g g).symm
        _ = (A0.conjBy g⁻¹).conjBy g := by rw [hEq]
        _ = A0 := section11_conjBy_inv' (G := G) A0 g
    have hg2_norm_A0 : g ^ 2 ∈ Subgroup.normalizer (A0 : Set G) :=
      section11_mem_normalizer_of_conjBy_eq hconj_sq
    exact hg2M (h11.normalizer_A0_le hg2_norm_A0)
  refine ⟨A0.conjBy g, A0.conjBy g⁻¹, ?_, ?_, hdistinct, ?_, ?_⟩
  · exact hprime_conj hgA
  · exact hprime_conj hginvA
  · exact hfix_conj hgM hgA
  · exact hfix_conj hginvM hginvA

end Section11
