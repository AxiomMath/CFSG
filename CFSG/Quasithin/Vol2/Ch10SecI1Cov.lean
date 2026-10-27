module

public import CFSG.Quasithin.Vol2.Ch10SecI1Dual

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ASInputs.C10KH

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {G : Type} [Group G] {V : Type} [CommGroup V] {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M]

section Form

variable [Module (ZMod 2) (Additive V)] (r : G →* MulAut V) (s : M →ₗ[ZMod 2] Additive V)
  (B : LinearMap.BilinForm (ZMod 2) M)

@[expose] def formDual (Λ : Additive V →ₗ[ZMod 2] ZMod 2) (γ : G) : M →ₗ[ZMod 2] ZMod 2 where
  toFun y := Λ (repOf r γ⁻¹ (s y)) - Λ (s y)
  map_add' y y' := by
    simp only [map_add]
    abel
  map_smul' c y := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply, mul_sub]

theorem formDual_apply (Λ : Additive V →ₗ[ZMod 2] ZMod 2) (γ : G) (y : M) :
    formDual r s Λ γ y = Λ (repOf r γ⁻¹ (s y)) - Λ (s y) :=
  rfl

variable [Finite M]

@[expose] def formCoc (hB : B.Nondegenerate) :
    (Additive V →ₗ[ZMod 2] ZMod 2) →ₗ[ZMod 2] (G → M) where
  toFun Λ γ := (B.toDual hB).symm (formDual r s Λ γ)
  map_add' Λ Λ' := by
    funext γ
    change (B.toDual hB).symm (formDual r s (Λ + Λ') γ) =
      (B.toDual hB).symm (formDual r s Λ γ) + (B.toDual hB).symm (formDual r s Λ' γ)
    rw [← map_add]
    congr 1
    ext y
    change formDual r s (Λ + Λ') γ y = formDual r s Λ γ y + formDual r s Λ' γ y
    simp only [formDual_apply, LinearMap.add_apply]
    abel
  map_smul' c Λ := by
    funext γ
    change (B.toDual hB).symm (formDual r s (c • Λ) γ) = c • (B.toDual hB).symm (formDual r s Λ γ)
    rw [← map_smul]
    congr 1
    ext y
    change formDual r s (c • Λ) γ y = c • formDual r s Λ γ y
    simp only [formDual_apply, LinearMap.smul_apply, smul_sub]

theorem formCoc_apply (hB : B.Nondegenerate) (Λ : Additive V →ₗ[ZMod 2] ZMod 2) (γ : G)
    (y : M) : B (formCoc r s B hB Λ γ) y = formDual r s Λ γ y := by
  rw [← LinearMap.BilinForm.toDual_def hB]
  change (B.toDual hB) ((B.toDual hB).symm (formDual r s Λ γ)) y = _
  rw [LinearEquiv.apply_symm_apply]

end Form

theorem card_le_card_H1_of_form [Finite G] [Finite V] [Finite M] (hV2 : ∀ v : V, v ^ 2 = 1)
    (r : G →* MulAut V) (Z : Subgroup V) (hZ : ∀ γ, ∀ z ∈ Z, r γ z = z)
    (hgen : ∀ v : V, v ∈ Subgroup.closure {x | ∃ γ w, x = r γ w * w⁻¹})
    (ρ : Representation (ZMod 2) G M) (β : V →* Multiplicative M)
    (hβs : Function.Surjective β) (hβk : ∀ v, β v = 1 ↔ v ∈ Z)
    (hβe : ∀ γ v, Multiplicative.toAdd (β (r γ v)) = ρ γ (Multiplicative.toAdd (β v)))
    (B : LinearMap.BilinForm (ZMod 2) M) (hB : B.Nondegenerate)
    (hBi : ∀ γ x y, B (ρ γ x) (ρ γ y) = B x y) :
    Nat.card Z ≤ Nat.card (H1 ρ) := by
  classical
  have h2 : ∀ x : Additive V, 2 • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hV2, ofMul_one]
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  let βA : Additive V →ₗ[ZMod 2] M := (MonoidHom.toAdditiveLeft β).toZModLinearMap 2
  have hβA : ∀ v, βA v = Multiplicative.toAdd (β (Additive.toMul v)) := fun _ => rfl
  have hβAs : LinearMap.range βA = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd y)
    exact ⟨Additive.ofMul v, by rw [hβA, toMul_ofMul, hv, toAdd_ofAdd]⟩
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective βA hβAs
  have hs' : ∀ y, βA (s y) = y := fun y => LinearMap.congr_fun hs y
  have hβAe : ∀ γ v, βA (repOf r γ v) = ρ γ (βA v) := fun γ v => hβe γ (Additive.toMul v)
  have hker : ∀ γ v, βA v = 0 → repOf r γ v = v := by
    intro γ v hv
    have hvZ : Additive.toMul v ∈ Z := by
      rw [← hβk]
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact hv
    change Additive.ofMul (r γ (Additive.toMul v)) = v
    rw [hZ γ _ hvZ]
    rfl
  have hBi' : ∀ γ x y, B (ρ γ x) y = B x (ρ γ⁻¹ y) := fun γ x y => by
    have hy : y = ρ γ (ρ γ⁻¹ y) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    conv_lhs => rw [hy]
    exact hBi γ x _
  let c := formCoc r s B hB
  have hc : ∀ Λ γ w, B (c Λ γ) (βA w) = Λ (repOf r γ⁻¹ w) - Λ w := by
    intro Λ γ w
    rw [formCoc_apply, formDual_apply]
    have hk : βA (s (βA w) - w) = 0 := by rw [map_sub, hs', sub_self]
    have h1 := hker γ⁻¹ _ hk
    rw [map_sub] at h1
    have e1 : repOf r γ⁻¹ (s (βA w)) = repOf r γ⁻¹ w + (s (βA w) - w) := by
      rw [← h1]
      abel
    rw [e1, map_add, map_sub]
    abel
  have hBinj : ∀ a b : M, (∀ n, B a n = B b n) → a = b := fun a b h =>
    (B.toDual hB).injective (LinearMap.ext fun n => by
      rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def]
      exact h n)
  have hZ1 : ∀ Λ, c Λ ∈ Z1 ρ := by
    intro Λ γ δ
    refine hBinj _ _ fun n => ?_
    rw [← hs' n, LinearMap.map_add₂, hc, hc, hBi', ← hβAe, hc, mul_inv_rev, map_mul,
      Module.End.mul_apply]
    abel
  let cZ : (Additive V →ₗ[ZMod 2] ZMod 2) →ₗ[ZMod 2] ↥(Z1 ρ) := LinearMap.codRestrict (Z1 ρ) c hZ1
  let T : Module.Dual (ZMod 2) (Additive V) →ₗ[ZMod 2] H1 ρ :=
    ((B1 ρ).comap (Z1 ρ).subtype).mkQ ∘ₗ cZ
  let ZA : Submodule (ZMod 2) (Additive V) := LinearMap.ker βA
  have hkerT : LinearMap.ker T ≤ ZA.dualAnnihilator := by
    intro Λ hΛ
    rw [LinearMap.mem_ker] at hΛ
    have h0 : cZ Λ ∈ (B1 ρ).comap (Z1 ρ).subtype := (Submodule.Quotient.mk_eq_zero _).1 hΛ
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp h0
    have hinv : ∀ γ w, Λ (repOf r γ⁻¹ w) - Λ w = B m (βA (repOf r γ⁻¹ w)) - B m (βA w) := by
      intro γ w
      rw [← hc]
      have hcm : c Λ γ = ρ γ m - m := (congrFun hm γ).symm
      have e : B (ρ γ m - m) (βA w) + B m (βA w) = B (ρ γ m) (βA w) := by
        rw [← LinearMap.map_add₂, sub_add_cancel]
      rw [hBi', ← hβAe] at e
      rw [hcm]
      exact eq_sub_of_add_eq e
    let f : Additive V →+ ZMod 2 :=
      { toFun := fun v => Λ v - B m (βA v)
        map_zero' := by simp
        map_add' := fun v v' => by
          simp only [map_add]
          abel }
    have hf : ∀ γ w, f (repOf r γ w) = f w := by
      intro γ w
      have h1 := hinv γ⁻¹ w
      rw [inv_inv] at h1
      change Λ (repOf r γ w) - B m (βA (repOf r γ w)) = Λ w - B m (βA w)
      linear_combination h1
    have hf0 : ∀ v : V, f (Additive.ofMul v) = 0 := by
      intro v
      let fM : V →* Multiplicative (ZMod 2) := AddMonoidHom.toMultiplicativeRight f
      have hle : Subgroup.closure {x | ∃ γ w, x = r γ w * w⁻¹} ≤ fM.ker := by
        rw [Subgroup.closure_le]
        rintro _ ⟨γ, w, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker]
        change Multiplicative.ofAdd (f (Additive.ofMul (r γ w * w⁻¹))) = 1
        have hw : f (Additive.ofMul (r γ w)) = f (Additive.ofMul w) := hf γ (Additive.ofMul w)
        rw [ofMul_mul, ofMul_inv, map_add, map_neg, hw, add_neg_cancel]
        rfl
      have h1 := hle (hgen v)
      rw [MonoidHom.mem_ker] at h1
      exact congrArg Multiplicative.toAdd h1
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    have h1 := hf0 (Additive.toMul w)
    rw [ofMul_toMul] at h1
    change Λ w - B m (βA w) = 0 at h1
    have hw0 : βA w = 0 := LinearMap.mem_ker.mp hw
    rw [hw0, map_zero] at h1
    simpa using h1
  have hZA : ∀ v : V, v ∈ Z ↔ Additive.ofMul v ∈ ZA := fun v => by
    rw [← hβk, LinearMap.mem_ker, hβA, toMul_ofMul]
    exact ⟨fun h => by rw [h, toAdd_one], fun h => Multiplicative.toAdd.injective h⟩
  have hZAcard : Nat.card ZA = 2 ^ Module.finrank (ZMod 2) ZA := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hZcard : Nat.card Z = 2 ^ Module.finrank (ZMod 2) ZA := by
    rw [← hZAcard]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul hZA)
  have hH1card : Nat.card (H1 ρ) = 2 ^ Module.finrank (ZMod 2) (H1 ρ) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hZcard, hH1card]
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2)
    (V := Module.Dual (ZMod 2) (Additive V)) (V₂ := H1 ρ) T
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq ZA
  have h3 := Submodule.finrank_mono hkerT
  have h4 := Submodule.finrank_le (LinearMap.range T)
  rw [Subspace.dual_finrank_eq] at h1
  omega

end CFSG.Quasithin.ASInputs.C10KH
