module

public import CFSG.Quasithin.MS93.ML3Sec

public section

namespace CFSG.Quasithin.MS93.S45R

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

section Linear

variable {F : Type} [Field F]

theorem natToDual_eq_zero (f : (Fin 3 → F) →+ (Fin 3 → F))
    (hf : ∀ (g : SL3 F) (x : Fin 3 → F),
      f (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = dualMat g *ᵥ f x)
    (x : Fin 3 → F) : f x = 0 := by
  by_contra hx
  apply not_equiv_dual (F := F)
  refine ⟨f, (injective_iff_map_eq_zero f).mpr fun y hy => ?_, hf⟩
  by_contra hy0
  have hS : ∀ (g : SL3 F), ∀ z ∈ f.ker, natAct false g *ᵥ z ∈ f.ker := by
    intro g z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    rw [natAct_false, hf, hz, Matrix.mulVec_zero]
  exact hx ((AddMonoidHom.mem_ker).mp
    (mem_of_natAct_invariant false f.ker hS ((AddMonoidHom.mem_ker).mpr hy) hy0 x))

theorem eq_zero_of_dualMat_fixed {y : Fin 3 → F} (hy : ∀ g : SL3 F, dualMat g *ᵥ y = y) :
    y = 0 := by
  have key : ∀ i j : Fin 3, i ≠ j → y i = 0 := by
    intro i j hij
    have h1 := hy (rootElt i j 1)
    rw [dualMat_rootElt_mulVec hij, add_eq_left] at h1
    have h2 := congrFun h1 j
    simpa using h2
  funext k
  fin_cases k
  · exact key 0 1 (by decide)
  · exact key 1 0 (by decide)
  · exact key 2 0 (by decide)

end Linear

section Abstract

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

theorem eq_zero_of_natSec_of_trivial {K X' W C : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : Function.Surjective ψ) (Nn : NatSec K X' W ψ false) (f : 𝔾 → (Fin 3 → F))
    (hCK : C ≤ K)
    (hadd : ∀ x ∈ C ⊔ X', ∀ y ∈ C ⊔ X', f (x * y) = f x + f y)
    (hW : ∀ w ∈ W, f w = 0)
    (heq : ∀ k : ↥K, ∀ x ∈ C ⊔ X',
      f ((k : 𝔾) * x * (k : 𝔾)⁻¹) = dualMat (toSL3 ψ k) *ᵥ f x)
    (hC : ∀ k : ↥K, ∀ x ∈ C, x⁻¹ * ((k : 𝔾) * x * (k : 𝔾)⁻¹) ∈ W) :
    ∀ x ∈ C ⊔ X', f x = 0 := by
  classical
  have hWX : W ≤ X' := Nn.le
  have hX : X' ≤ C ⊔ X' := le_sup_right
  have hCX : C ≤ C ⊔ X' := le_sup_left
  have hwd : ∀ x₁ ∈ X', ∀ x₂ ∈ X', Nn.coord x₁ = Nn.coord x₂ → f x₁ = f x₂ := by
    intro x₁ hx₁ x₂ hx₂ he
    have hw := Nn.inv_mul_mem_of_coord_eq hx₁ hx₂ he
    have e : x₂ = x₁ * (x₁⁻¹ * x₂) := by group
    rw [e, hadd _ (hX hx₁) _ (hX (hWX hw)), hW _ hw, add_zero]
  choose lift hlift hliftc using fun u : Fin 3 → F => Nn.exists_coord_eq u
  have hf1 : f 1 = 0 := by
    have := hadd 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at this
    exact (add_eq_left.mp this.symm)
  let F₀ : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun u => f (lift u)
      map_zero' := by
        show f (lift 0) = 0
        rw [hwd (lift 0) (hlift 0) 1 (Subgroup.one_mem _) (by rw [hliftc, Nn.coord_one]), hf1]
      map_add' := fun u v => by
        show f (lift (u + v)) = f (lift u) + f (lift v)
        rw [hwd (lift (u + v)) (hlift _) (lift u * lift v) (X'.mul_mem (hlift u) (hlift v))
          (by rw [hliftc, Nn.coord_mul (hlift u) (hlift v), hliftc, hliftc]),
          hadd _ (hX (hlift u)) _ (hX (hlift v))] }
  have hF₀ : ∀ x ∈ X', F₀ (Nn.coord x) = f x := fun x hx =>
    hwd _ (hlift _) _ hx (hliftc _)
  have hF₀eq : ∀ (g : SL3 F) (u : Fin 3 → F),
      F₀ (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) = dualMat g *ᵥ F₀ u := by
    intro g u
    obtain ⟨k, rfl⟩ := toSL3_surjective hψ g
    have hk := Nn.coord_conj k (hlift u)
    rw [natAct_false, hliftc] at hk
    rw [← hk, hF₀ _ (Nn.conj_mem k (hlift u)), heq k _ (hX (hlift u))]
    rfl
  have hX0 : ∀ x ∈ X', f x = 0 := fun x hx => by
    rw [← hF₀ x hx]
    exact natToDual_eq_zero F₀ hF₀eq _
  have hC0 : ∀ x ∈ C, f x = 0 := by
    intro x hx
    apply eq_zero_of_dualMat_fixed
    intro g
    obtain ⟨k, rfl⟩ := toSL3_surjective hψ g
    have hw := hC k x hx
    have hkx : (k : 𝔾) * x * (k : 𝔾)⁻¹ ∈ C ⊔ X' := by
      have e : (k : 𝔾) * x * (k : 𝔾)⁻¹ = x * (x⁻¹ * ((k : 𝔾) * x * (k : 𝔾)⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hCX hx) (hX (hWX hw))
    have hw' : ((k : 𝔾) * x * (k : 𝔾)⁻¹)⁻¹ * x ∈ W := by
      have := W.inv_mem hw
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have e : x = ((k : 𝔾) * x * (k : 𝔾)⁻¹) * (((k : 𝔾) * x * (k : 𝔾)⁻¹)⁻¹ * x) := by group
    have h1 : f x = f ((k : 𝔾) * x * (k : 𝔾)⁻¹) := by
      conv_lhs => rw [e]
      rw [hadd _ hkx _ (hX (hWX hw')), hW _ hw', add_zero]
    rw [← heq k x (hCX hx), ← h1]
  intro x hx
  have hCn : C ≤ Subgroup.normalizer (X' : Set 𝔾) := hCK.trans Nn.norm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hx
  obtain ⟨c, hc, x', hx', rfl⟩ := Set.mem_mul.mp hx
  rw [hadd _ (hCX hc) _ (hX hx'), hC0 c hc, hX0 x' hx', add_zero]

end Abstract

end CFSG.Quasithin.MS93.S45R
