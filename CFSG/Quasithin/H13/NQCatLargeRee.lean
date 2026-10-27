module

public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.Quasithin.SteinbergBTLargeReeTwoPrimeBorel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.NQTerm
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise commutatorElement

variable {C : Type*} [Group C]

structure TwoPrimeBorelDatum (p : ℕ) (U B : Subgroup C) : Prop where
  le : U ≤ B
  commutator_le : ⁅B, B⁆ ≤ U
  normalizer_le : normalizer (U : Set C) ≤ B
  isPGroup : IsPGroup 2 U
  two_prime : ∀ D : Subgroup C, U ≤ D → (∃ b c : ℕ, Nat.card D = 2 ^ b * p ^ c) → D ≤ B

namespace TwoPrimeBorelDatum

variable {p : ℕ} {U B : Subgroup C}

theorem map (h : TwoPrimeBorelDatum p U B) (e : C ≃* C) :
    TwoPrimeBorelDatum p (U.map e.toMonoidHom) (B.map e.toMonoidHom) where
  le := Subgroup.map_mono h.le
  commutator_le := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono h.commutator_le
  normalizer_le := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono h.normalizer_le
  isPGroup := h.isPGroup.map _
  two_prime D hUD hD := by
    have hD' : D = (D.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map]
      ext x
      simp
    rw [hD']
    refine Subgroup.map_mono (h.two_prime _ ?_ ?_)
    · have := Subgroup.map_mono (f := e.symm.toMonoidHom) hUD
      rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id C from
        MonoidHom.ext fun x => by simp, Subgroup.map_id] at this
    · rwa [Subgroup.card_map_of_injective e.symm.injective]

theorem commute_of_permutable [Finite C] (h : TwoPrimeBorelDatum p U B) (hp : p.Prime)
    (hp2 : p ≠ 2) (A : Subgroup C) (hA : IsPGroup p A)
    (hAU : (A : Set C) * (U : Set C) = (U : Set C) * A) :
    A ≤ B ∧ A ⊓ U = ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ g ∈ normalizer (U : Set C), g ∈ normalizer (A : Set C) → ∀ a ∈ A, g * a * g⁻¹ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := h.isPGroup.exists_card_eq
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hcardD : ∃ b c : ℕ, Nat.card (permProd A U hAU) = 2 ^ b * p ^ c := by
    obtain ⟨d, hdA, hcard⟩ := card_permProd A U hAU
    rw [hk] at hdA
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdA
    exact ⟨m, j, by rw [hcard, hm]⟩
  have hAB : A ≤ B := (le_permProd_left A U hAU).trans
    (h.two_prime _ (le_permProd_right A U hAU) hcardD)
  have hAU' : A ⊓ U = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk, hm]
    exact Nat.Coprime.pow k m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hkey : ∀ x ∈ A, ∀ y ∈ B, x ∈ B → y * x * y⁻¹ ∈ A → y * x * y⁻¹ = x := by
    intro x hx y hy hxB hyx
    have hc : ⁅y, x⁆ ∈ U :=
      h.commutator_le (Subgroup.commutator_mem_commutator hy hxB)
    have hcA : ⁅y, x⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem hyx (A.inv_mem hx)
    have h1 : ⁅y, x⁆ = 1 := by
      have : ⁅y, x⁆ ∈ A ⊓ U := ⟨hcA, hc⟩
      rwa [hAU', Subgroup.mem_bot] at this
    rw [commutatorElement_def] at h1
    calc y * x * y⁻¹ = y * x * y⁻¹ * x⁻¹ * x := by group
      _ = x := by rw [h1, one_mul]
  refine ⟨hAB, hAU', fun a ha b hb => ?_, fun g hgU hgA a ha => ?_⟩
  · have := hkey b hb a (hAB ha) (hAB hb) (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha))
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [this]
  · exact hkey a ha g (h.normalizer_le hgU) (hAB ha) ((mem_normalizer_iff.1 hgA a).1 ha)

end TwoPrimeBorelDatum

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem commutator_reeFixedBorel_le
    :
    ⁅F4.reeFixedBorel K a, F4.reeFixedBorel K a⁆ ≤ F4.reeFixedPosUnipotent K a := by
  obtain ⟨-, hUH, -, -, hnorm, -, hcomm, -⟩ := ree_fixed_Bruhat_decomposition F4 a K
  have hN : F4.reeFixedBorel K a ≤
      normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer reeFixedPosUnipotent_le_reeFixedBorel).1 hnorm
  refine commutator_le_of_coe_eq_mul hUH hcomm fun t ht u hu => ?_
  exact (mem_normalizer_iff.1 (hN (reeFixedTorus_le_reeFixedBorel ht)) u).1 hu

theorem reeFixedPosUnipotent_le_reeGamma
    : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a :=
  inf_le_right

theorem exists_sylow_reeFixedPosUnipotent
    :
    ∃ P : Sylow 2 (F4.reeGamma K a), (P : Subgroup (F4.reeGamma K a)) =
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  exact (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1

theorem twoPrimeBorelDatum_reeGamma
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    TwoPrimeBorelDatum p ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a)) where
  le := fun x hx => reeFixedPosUnipotent_le_reeFixedBorel hx
  commutator_le := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_subgroupOf]
    have h := commutator_reeFixedBorel_le (K := K) (a := a)
      (Subgroup.commutator_mem_commutator hg₁ hg₂)
    simpa [commutatorElement_def] using h
  normalizer_le := by
    intro g hg
    rw [← Subgroup.subgroupOf_normalizer_eq reeFixedPosUnipotent_le_reeGamma,
      Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_subgroupOf, ← reeGamma_inf_normalizer_reeFixedPosUnipotent]
    exact ⟨g.2, hg⟩
  isPGroup := by
    obtain ⟨P, hP⟩ := exists_sylow_reeFixedPosUnipotent (K := K) (a := a)
    rw [← hP]
    exact P.isPGroup'
  two_prime D hUD hD := by
    obtain ⟨b, c, hbc⟩ := hD
    have hle := Quasithin.SteinbergBT.large_Ree_two_prime_positive_subgroup_overgroups_are_Borel
      ha hK hp hp2 (D := D.map (F4.reeGamma K a).subtype) (Subgroup.map_subtype_le D)
      (fun u hu => ⟨⟨u, reeFixedPosUnipotent_le_reeGamma hu⟩, hUD hu, rfl⟩)
      (b := b) (c := c)
      (by rw [Subgroup.card_map_of_injective (F4.reeGamma K a).subtype_injective]; exact hbc)
    intro x hx
    exact hle ⟨x, hx, rfl⟩

theorem large_Ree_common_sylow_prime_subgroup_normalizer_action_is_cyclic
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (U : Sylow 2 (F4.reeGamma K a)) (A : Subgroup (F4.reeGamma K a)) (hA : IsPGroup p A)
    (hAU : (A : Set (F4.reeGamma K a)) * (U : Set (F4.reeGamma K a)) =
      (U : Set (F4.reeGamma K a)) * (A : Set (F4.reeGamma K a))) :
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
    (∀ α ∈ pairAutSubgroup A (U : Subgroup (F4.reeGamma K a)) ⊓
        (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range,
      ∀ x ∈ A, α x = x) ∧
    (IsCyclic (pairAutRestrict A (U : Subgroup (F4.reeGamma K a))).range ∧
      Nat.card (pairAutRestrict A (U : Subgroup (F4.reeGamma K a))).range ∣ 2 * a + 1) ∧
    ∀ Δ : Subgroup (pairAutSubgroup A (U : Subgroup (F4.reeGamma K a))), IsPGroup 2 Δ →
      ∀ α ∈ Δ, ∀ x ∈ A, (α : MulAut (F4.reeGamma K a)) x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_reeFixedPosUnipotent (K := K) (a := a)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (F4.reeGamma K a) P₀ U
  have hUc : (U : Subgroup (F4.reeGamma K a)) =
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).map
        (MulAut.conj c).toMonoidHom := by
    rw [← hc, coe_smul_sylow_eq_map, hP₀]
  have hdat := (twoPrimeBorelDatum_reeGamma ha hK hp hp2).map (MulAut.conj c)
  rw [← hUc] at hdat
  obtain ⟨-, -, hcomm, hfix⟩ := hdat.commute_of_permutable hp hp2 A hA hAU
  have hinner : ∀ α ∈ pairAutSubgroup A (U : Subgroup (F4.reeGamma K a)) ⊓
      (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range,
        ∀ x ∈ A, α x = x := by
    rintro α ⟨hαΛ, g, rfl⟩ x hx
    exact hfix g (mem_normalizer_of_map_conj_eq hαΛ.2) (mem_normalizer_of_map_conj_eq hαΛ.1) x hx
  obtain ⟨-, -, -, hcyc, hcard, -⟩ :=
    ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK
  have : Finite (Outer (F4.reeGamma K a)) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  set Λ := pairAutSubgroup A (U : Subgroup (F4.reeGamma K a))
  set ρ := pairAutRestrict A (U : Subgroup (F4.reeGamma K a))
  let Θ : MulAut (F4.reeGamma K a) →* Outer (F4.reeGamma K a) := QuotientGroup.mk' _
  have hker : (Θ.comp Λ.subtype).ker ≤ ρ.ker := by
    intro α hα
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hα
    have hαI : (α : MulAut (F4.reeGamma K a)) ∈ inner (F4.reeGamma K a) :=
      (QuotientGroup.eq_one_iff _).1 hα
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    exact hinner α ⟨α.2, hαI⟩ x x.2
  have hΔ := map_isCyclic_of_ker_le (Θ.comp Λ.subtype) ρ hker
  rw [hcard] at hΔ
  refine ⟨hcomm, hinner, ?_, fun Δ hΔ2 α hα x hx => ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact hΔ ⊤
  · obtain ⟨-, hdvd⟩ := hΔ Δ
    have h2 : IsPGroup 2 (Δ.map ρ) := hΔ2.map ρ
    have : Finite (Δ.map ρ) := Nat.finite_of_card_ne_zero fun h0 => by
      rw [h0] at hdvd
      omega
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hn0 : n = 0 := by
      by_contra hn0
      have h2dvd : 2 ∣ 2 * a + 1 :=
        (dvd_pow_self 2 hn0).trans (hn ▸ hdvd)
      omega
    rw [hn0, pow_zero, Subgroup.card_eq_one] at hn
    have hρα : ρ α = 1 := by
      have hmem : ρ α ∈ Δ.map ρ := Subgroup.mem_map_of_mem ρ hα
      rwa [hn, Subgroup.mem_bot] at hmem
    have := congrArg (fun φ : MulAut A => ((φ ⟨x, hx⟩ : A) : F4.reeGamma K a)) hρα
    exact this

end CFSG.Quasithin.H13.NQCat
