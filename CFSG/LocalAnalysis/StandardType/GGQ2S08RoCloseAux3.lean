module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggQ2s08r4_zmod3_sq
     : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

theorem ggQ2s08r4_zmod3_eq_neg_one
     : ∀ p : ZMod 3, p ≠ 1 → p * p = 1 → p = -1 := by decide

theorem ggQ2s08r4_ind_inv
    {G : Type} [Group G] {Bs : Subgroup G}
     {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ) :
    GGQ2Ind Bs g⁻¹ φ⁻¹ := by
  refine ⟨Subgroup.inv_mem _ hInd.1, fun b => ?_⟩
  have h : (b : G) = g * ((φ⁻¹ b : ↥Bs) : G) * g⁻¹ := by
    simpa using hInd.2 (φ⁻¹ b)
  rw [h]
  group

theorem ggQ2s08r4_ind_mul
    {G : Type} [Group G] {Bs : Subgroup G}
     {g₁ g₂ : G} {φ₁ φ₂ : MulAut ↥Bs}
    (h₁ : GGQ2Ind Bs g₁ φ₁) (h₂ : GGQ2Ind Bs g₂ φ₂) :
    GGQ2Ind Bs (g₁ * g₂) (φ₁ * φ₂) := by
  refine ⟨Subgroup.mul_mem _ h₁.1 h₂.1, fun b => ?_⟩
  rw [MulAut.mul_apply, h₁.2 (φ₂ b), h₂.2 b]
  group

theorem ggQ2s08r4_eq_of_model
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     (M : GGQ2LDatum 3 Bs L x) {u v : ↥Bs}
    (h : M.model (Additive.ofMul u) = M.model (Additive.ofMul v)) : u = v :=
  Additive.ofMul.injective (M.model.injective h)

theorem ggQ2s08r4_conj_eq
    {G : Type} [Group G] {Bs : Subgroup G}
     {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ) (w : ↥Bs) :
    g * (w : G) * g⁻¹ = (φ w : G) :=
  (hInd.2 w).symm

theorem ggQ2s08r4_conj_eq_of_model
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     (M : GGQ2LDatum 3 Bs L x)
    {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ) (w v : ↥Bs)
    (h : M.model (Additive.ofMul (φ w)) = M.model (Additive.ofMul v)) :
    g * (w : G) * g⁻¹ = (v : G) := by
  rw [ggQ2s08r4_conj_eq hInd w, ggQ2s08r4_eq_of_model M h]

theorem ggQ2s08r4_conj_eq_of_lin
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     (M : GGQ2LDatum 3 Bs L x)
    {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ) (w v : ↥Bs)
    (h : ggLin (p := 3) M.model φ (M.model (Additive.ofMul w)) =
      M.model (Additive.ofMul v)) :
    g * (w : G) * g⁻¹ = (v : G) := by
  refine ggQ2s08r4_conj_eq_of_model M hInd w v ?_
  rwa [ggLin_apply_ofMul] at h

theorem ggQ2s08r4_final
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     [Finite G] {B : Subgroup G} {D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hL : L.map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      K.map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  have hmap : (ggG0 3 B x L D J).map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J := by
    unfold ggG0
    rw [Subgroup.map_sup]
    refine sup_le hL ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun h => hK y K h
  have hcard : Nat.card ↥((ggG0 3 B x L D J).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥(ggG0 3 B x L D J) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact mem_normalizer_iff_map_conj.mpr (Subgroup.eq_of_le_of_card_ge hmap hcard.ge)

theorem ggQ2s08r4_reduce
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     [Finite G] {B : Subgroup G} {D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x)
    {N : ℕ} (h2 : 2 ≤ N) (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f)
    (hD : ∀ g : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f g →
      ∃ (k : G) (φ : MulAut ↥Bs), GGQ2Ind Bs k φ ∧
        k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧ ggLin (p := 3) M.model φ = g)
    (hcore : ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ →
      (ggLin (p := 3) M.model φ = 1 ∨
        ∃ k : Fin N, ggLin (p := 3) M.model φ = ggQ2s08r4_singleEquiv M
          (ggQ2s08r4_basis M f hf) k) →
      g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) :
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGQ2S08Mono f (ggLin (p := 3) M.model φ) →
      g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  intro g φ hInd hMono
  obtain ⟨σ, ε, hε, hT⟩ := hMono
  let T : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model φ
  let b : Module.Basis (Fin N) (ZMod 3) M.V := ggQ2s08r4_basis M f hf
  have hT' : T = ggLin (p := 3) M.model φ := rfl
  by_cases hprod : (∏ i, ε i) = 1
  ·
    have hTeven : GGQ2S08MonoEven f T := ⟨σ, ε, hε, hprod, hT⟩
    obtain ⟨k, φk, hIndk, hkG0, hklin⟩ := hD T hTeven
    have hInd' : GGQ2Ind Bs (k⁻¹ * g) (φk⁻¹ * φ) :=
      ggQ2s08r4_ind_mul (ggQ2s08r4_ind_inv hIndk) hInd
    have hlin' : ggLin (p := 3) M.model (φk⁻¹ * φ) = 1 := by
      rw [map_mul, map_inv, hklin, ← hT']
      exact inv_mul_cancel T
    have hg' := hcore (k⁻¹ * g) (φk⁻¹ * φ) hInd' (Or.inl hlin')
    have h := Subgroup.mul_mem _ hkG0 hg'
    rwa [mul_inv_cancel_left] at h
  ·
    let k₀ : Fin N := ⟨0, Nat.lt_of_lt_of_le (by norm_num) h2⟩
    let s : M.V ≃ₗ[ZMod 3] M.V := ggQ2s08r4_singleEquiv M b k₀
    have hsquares : ∀ i, ε i * ε i = 1 := fun i => ggQ2s08r4_zmod3_sq (ε i) (hε i)
    have hpsq : (∏ i, ε i) * (∏ i, ε i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      simp [hsquares]
    have hpneg : (∏ i, ε i) = -1 := ggQ2s08r4_zmod3_eq_neg_one _ hprod hpsq
    have hε' : ∀ i, ggQ2s08r4_singleSign k₀ i * ε i ≠ 0 := fun i =>
      mul_ne_zero (ggQ2s08r4_singleSign_ne_zero k₀ i) (hε i)
    have hprod' : (∏ i, ggQ2s08r4_singleSign k₀ i * ε i) = 1 := by
      rw [Finset.prod_mul_distrib, ggQ2s08r4_singleSign_prod, hpneg]
      decide
    have hTnew : ∀ i, (T * s) (f i) = (ggQ2s08r4_singleSign k₀ i * ε i) • f (σ i) := by
      intro i
      rw [LinearEquiv.mul_apply, ← ggQ2s08r4_basis_apply M f hf i,
        ggQ2s08r4_singleEquiv_basis, map_smul, ggQ2s08r4_basis_apply, hT i, smul_smul]
    have hTeven : GGQ2S08MonoEven f (T * s) :=
      ⟨σ, fun i => ggQ2s08r4_singleSign k₀ i * ε i, hε', hprod', hTnew⟩
    obtain ⟨k, φk, hIndk, hkG0, hklin⟩ := hD (T * s) hTeven
    have hsinv : s⁻¹ = s := by
      have h : s * s = 1 := ggQ2s08r4_singleEquiv_involutive M b k₀
      exact (eq_inv_iff_mul_eq_one.mpr h).symm
    have hInd' : GGQ2Ind Bs (k⁻¹ * g) (φk⁻¹ * φ) :=
      ggQ2s08r4_ind_mul (ggQ2s08r4_ind_inv hIndk) hInd
    have hlin' : ggLin (p := 3) M.model (φk⁻¹ * φ) = s := by
      rw [map_mul, map_inv, hklin, ← hT']
      rw [mul_inv_rev, hsinv]
      group
    have hg' := hcore (k⁻¹ * g) (φk⁻¹ * φ) hInd' (Or.inr ⟨k₀, hlin'⟩)
    have h := Subgroup.mul_mem _ hkG0 hg'
    rwa [mul_inv_cancel_left] at h

end CFSG.StandardType

end
