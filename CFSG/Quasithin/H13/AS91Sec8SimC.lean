module

public import CFSG.Quasithin.H13.AS91Sec8Defs
public import CFSG.Quasithin.H13.AS91Sec8Aux

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction
open scoped Pointwise

universe u v

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]

private theorem mem_inf_stab_iff' {I : Subgroup G} (x : X) {a : G} (ha : a ∈ I) :
    a ∈ I ⊓ stabilizer G x ↔ a • x = x := by
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩

private theorem fixA_iff {I : Subgroup G} {x : X} (φ : ↥I ≃* ↥I)
    (hφ : autPres I (I ⊓ stabilizer G x) φ) (a : ↥I) :
    (a : G) • x = x ↔ ((φ a : ↥I) : G) • x = x :=
  (mem_inf_stab_iff' x a.2).symm.trans ((hφ a).trans (mem_inf_stab_iff' x (φ a).2))

private theorem exists_p_step {I : Subgroup G} {x y : X} (φ : ↥I ≃* ↥I) (hxy : x ≠ y)
    (τ : ↥I) (hτx : (τ : G) • x = y) (hτy : (τ : G) • y = x)
    (hφ : autPres I (I ⊓ stabilizer G x) φ)
    (hD : ∀ d : ↥I, (d : G) ∈ dblSet I x y ↔ ((φ d : ↥I) : G) ∈ dblSet I x y) :
    ∃ p ∈ I ⊓ stabilizer G x, ((φ τ : ↥I) : G) • x = p • y ∧
      ((φ τ : ↥I) : G) • (p • y) = x ∧ ((φ τ : ↥I) : G) • x ≠ x := by
  have hτB : (τ : G) ∈ ((I ⊓ stabilizer G ({x, y} : Set X) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨τ.2, (mem_stabilizer_pair_iff hxy _).2 (Or.inr ⟨hτx, hτy⟩)⟩
  have h1A : (1 : G) ∈ ((I ⊓ stabilizer G x : Subgroup G) : Set G) :=
    (I ⊓ stabilizer G x).one_mem
  have hτD : (τ : G) ∈ dblSet I x y := by
    have h := Set.mul_mem_mul (Set.mul_mem_mul h1A hτB) h1A
    simpa only [dblSet, one_mul, mul_one] using h
  have hTD : ((φ τ : ↥I) : G) ∈ dblSet I x y := (hD τ).1 hτD
  simp only [dblSet] at hTD
  obtain ⟨ab, hab, c, hc, habc⟩ := Set.mem_mul.1 hTD
  obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.1 hab
  have haA : a ∈ I ⊓ stabilizer G x := ha
  have hcA : c ∈ I ⊓ stabilizer G x := hc
  have hqB : q ∈ I ⊓ stabilizer G ({x, y} : Set X) := hq
  have hax : a • x = x := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 haA).2
  have hcx : c • x = x := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hcA).2
  have hqxy := (mem_stabilizer_pair_iff hxy q).1 (Subgroup.mem_inf.1 hqB).2
  have hTx : ((φ τ : ↥I) : G) • x ≠ x := by
    intro h
    have hτA : ¬ ((τ : G) ∈ I ⊓ stabilizer G x) := by
      intro hm
      have h2 : (τ : G) • x = x := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hm).2
      exact hxy (h2.symm.trans hτx)
    apply hτA
    apply (hφ τ).2
    exact Subgroup.mem_inf.2 ⟨(φ τ).2, MulAction.mem_stabilizer_iff.2 h⟩
  have hTxa : ((φ τ : ↥I) : G) • x = a • y := by
    rcases hqxy with ⟨hqx, _⟩ | ⟨hqx, _⟩
    · exact (hTx (by rw [← habc, mul_smul, mul_smul, hcx, hqx, hax])).elim
    · rw [← habc, mul_smul, mul_smul, hcx, hqx]
  refine ⟨a, haA, hTxa, ?_, hTx⟩
  have hτ2 : ((τ * τ : ↥I) : G) • x = x := by
    rw [Subgroup.coe_mul, mul_smul, hτx, hτy]
  have hφ2 : ((φ (τ * τ) : ↥I) : G) • x = x := (fixA_iff φ hφ (τ * τ)).1 hτ2
  rw [map_mul, Subgroup.coe_mul, mul_smul] at hφ2
  rw [← hTxa]
  exact hφ2

private theorem conj_fix_iff {I : Subgroup G} {x y : X} (φ : ↥I ≃* ↥I)
    (hφ : autPres I (I ⊓ stabilizer G x) φ) (τ : ↥I) (hτx : (τ : G) • x = y) (g : ↥I) :
    (g : G) • y = y ↔ ((φ g : ↥I) : G) • (((φ τ : ↥I) : G) • x) = ((φ τ : ↥I) : G) • x := by
  have hu1 : ((τ⁻¹ * g * τ : ↥I) : G) = (τ : G)⁻¹ * (g : G) * (τ : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hu2 : ((φ (τ⁻¹ * g * τ) : ↥I) : G) =
      ((φ τ : ↥I) : G)⁻¹ * ((φ g : ↥I) : G) * ((φ τ : ↥I) : G) := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have e1 : ((τ⁻¹ * g * τ : ↥I) : G) • x = x ↔ (g : G) • y = y := by
    rw [hu1, mul_smul, hτx, mul_smul, inv_smul_eq_iff, hτx]
  have e2 : ((φ (τ⁻¹ * g * τ) : ↥I) : G) • x = x ↔
      ((φ g : ↥I) : G) • (((φ τ : ↥I) : G) • x) = ((φ τ : ↥I) : G) • x := by
    rw [hu2, mul_smul, mul_smul, inv_smul_eq_iff]
  exact e1.symm.trans ((fixA_iff φ hφ _).trans e2)

theorem exists_p_of_phi {Γ : SimpleGraph X} {ΓI : Γ.Subgraph} {I : Subgroup G} {x y : X}
    (hU : IsUniquenessSystem Γ I ΓI x y) (φ : ↥I ≃* ↥I)
    (hφ : autPres I (I ⊓ stabilizer G x) φ)
    (hD : ∀ d : ↥I, (d : G) ∈ dblSet I x y ↔ ((φ d : ↥I) : G) ∈ dblSet I x y) :
    ∃ p ∈ I ⊓ stabilizer G x,
      ∀ g : ↥I, (g : G) ∈ stabilizer G ({x, y} : Set X) ↔
        ((φ g : ↥I) : G) ∈ stabilizer G ({x, p • y} : Set X) := by
  by_cases hxy : x = y
  ·
    refine ⟨1, (I ⊓ stabilizer G x).one_mem, fun g => ?_⟩
    have hset : ({x, y} : Set X) = {x} := by
      rw [hxy]
      exact Set.pair_eq_singleton y
    have hset' : ({x, (1 : G) • y} : Set X) = {x} := by
      rw [one_smul, hset]
    rw [hset, hset', MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      Set.smul_set_singleton, Set.smul_set_singleton, Set.singleton_eq_singleton_iff,
      Set.singleton_eq_singleton_iff]
    exact fixA_iff φ hφ g
  obtain ⟨τ₀, hτ₀, htx, hty⟩ := hU.swap
  obtain ⟨τ, rfl⟩ : ∃ τ : ↥I, (τ : G) = τ₀ := ⟨⟨τ₀, hτ₀⟩, rfl⟩
  obtain ⟨p, hp, hpx, hpy, hTx⟩ := exists_p_step φ hxy τ htx hty hφ hD
  have hK : ∀ g : ↥I, (g : G) • y = y ↔ ((φ g : ↥I) : G) • (p • y) = p • y := by
    intro g
    rw [← hpx]
    exact conj_fix_iff φ hφ τ htx g
  have hfac : ∀ g : ↥I, ((φ g : ↥I) : G) = ((φ τ : ↥I) : G) * ((φ (τ⁻¹ * g) : ↥I) : G) := by
    intro g
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have hfac' : ∀ g : ↥I, ((φ (τ⁻¹ * g) : ↥I) : G) = ((φ τ : ↥I) : G)⁻¹ * ((φ g : ↥I) : G) := by
    intro g
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨p, hp, fun g => ?_⟩
  have hy₁ : x ≠ p • y := fun h => hTx (hpx.trans h.symm)
  rw [mem_stabilizer_pair_iff hxy, mem_stabilizer_pair_iff hy₁]
  constructor
  · rintro (⟨hgx, hgy⟩ | ⟨hgx, hgy⟩)
    · exact Or.inl ⟨(fixA_iff φ hφ g).1 hgx, (hK g).1 hgy⟩
    ·
      have hg'x : ((τ⁻¹ * g : ↥I) : G) • x = x := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hgx, inv_smul_eq_iff, htx]
      have hg'y : ((τ⁻¹ * g : ↥I) : G) • y = y := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hgy, inv_smul_eq_iff, hty]
      have h1 : ((φ (τ⁻¹ * g) : ↥I) : G) • x = x := (fixA_iff φ hφ _).1 hg'x
      have h2 : ((φ (τ⁻¹ * g) : ↥I) : G) • (p • y) = p • y := (hK _).1 hg'y
      refine Or.inr ⟨?_, ?_⟩
      · rw [hfac g, mul_smul, h1, hpx]
      · rw [hfac g, mul_smul, h2, hpy]
  · rintro (⟨hgx, hgy⟩ | ⟨hgx, hgy⟩)
    · exact Or.inl ⟨(fixA_iff φ hφ g).2 hgx, (hK g).2 hgy⟩
    ·
      have hφg'x : ((φ (τ⁻¹ * g) : ↥I) : G) • x = x := by
        rw [hfac' g, mul_smul, hgx, inv_smul_eq_iff, hpx]
      have hφg'py : ((φ (τ⁻¹ * g) : ↥I) : G) • (p • y) = p • y := by
        rw [hfac' g, mul_smul, hgy, inv_smul_eq_iff, hpy]
      have hg'x : ((τ⁻¹ * g : ↥I) : G) • x = x := (fixA_iff φ hφ _).2 hφg'x
      have hg'y : ((τ⁻¹ * g : ↥I) : G) • y = y := (hK _).2 hφg'py
      have hgτ : (g : G) = (τ : G) * ((τ⁻¹ * g : ↥I) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      refine Or.inr ⟨?_, ?_⟩
      · rw [hgτ, mul_smul, hg'x]
        exact htx
      · rw [hgτ, mul_smul, hg'y]
        exact hty

end CFSG.Quasithin.H13.AS91
