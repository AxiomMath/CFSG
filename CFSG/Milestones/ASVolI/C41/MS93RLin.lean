module

public import CFSG.Milestones.ASVolI.C41.Conj

public section

namespace CFSG.ASVolI

open CFSG.Open

variable {G : Type} [Group G] {F : Type} [Field F]

theorem burnsideMS93R_le_sup_of_line [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {K W R C V₁ : Subgroup G}
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (e : ↥W ≃* Multiplicative (Fin 3 → F))
    (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hβeq : ∀ (a : ↥K) (u v : ↥W), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (e v) =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u)))
    (W₀ : Submodule F (Fin 3 → F)) (hW₀ : Module.finrank F W₀ = 2)
    (hV₁ : ∀ u : ↥W, (u : G) ∈ V₁ ↔ Multiplicative.toAdd (e u) ∈ W₀)
    (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hRV : ∀ r ∈ R, ∀ x ∈ V₁, r * x = x * r) (hR2 : IsPGroup 2 R)
    (hCP : ∀ g ∈ K ⊔ R, g ∈ Subgroup.centralizer (W : Set G) → g ∈ C) :
    R ≤ K ⊔ C := by
  classical
  intro r hr
  have hr' : r⁻¹ ∈ R := R.inv_mem hr
  have hfix : ∀ g ∈ R, ∀ w ∈ W₀, burnsideC41b_conjCoord e g w = w := by
    intro g hg w hw
    obtain ⟨u, rfl⟩ := burnsideC41b_exists_coord e w
    have huV : (u : G) ∈ V₁ := (hV₁ u).mpr hw
    exact burnsideC41b_conjCoord_spec e u u (by rw [hRV g hg u huV, mul_inv_cancel_right])
  obtain ⟨w₀, hw₀, hw₀0⟩ : ∃ w ∈ W₀, w ≠ 0 := by
    have hne : W₀ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW₀
      exact absurd hW₀ (by norm_num)
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hNorm : ∀ g : G, g ∈ R → ∀ γ : ↥(StatedSL 3 F), ∃ γ' : ↥(StatedSL 3 F), ∀ v,
      burnsideC41b_conjCoord e g (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        ((γ' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (burnsideC41b_conjCoord e g v) := by
    intro g hg γ
    obtain ⟨k, rfl⟩ := hα γ
    exact ⟨_, burnsideC41b_conjCoord_equivariant e hKW hβeq (hRW hg) (hRK hg) k⟩
  let θ₁ : (Fin 3 → F) →+ (Fin 3 → F) :=
    AddMonoidHom.mk' (burnsideC41b_conjCoord e r) (burnsideC41b_conjCoord_add e (hRW hr))
  let θ₂ : (Fin 3 → F) →+ (Fin 3 → F) :=
    AddMonoidHom.mk' (burnsideC41b_conjCoord e r⁻¹) (burnsideC41b_conjCoord_add e (hRW hr'))
  have hlin : ∀ (c : F) (v : Fin 3 → F),
      burnsideC41b_conjCoord e r (c • v) = c • burnsideC41b_conjCoord e r v := by
    intro c v
    refine burnsideC41b_smul_of_normalizes θ₁ θ₂ ?_ ?_ (hNorm _ hr) (hNorm _ hr') hw₀0 ?_ c v
    · intro v
      show burnsideC41b_conjCoord e r (burnsideC41b_conjCoord e r⁻¹ v) = v
      rw [← burnsideC41b_conjCoord_mul e (hRW hr) (hRW hr'), mul_inv_cancel,
        burnsideC41b_conjCoord_one]
    · intro v
      show burnsideC41b_conjCoord e r⁻¹ (burnsideC41b_conjCoord e r v) = v
      rw [← burnsideC41b_conjCoord_mul e (hRW hr') (hRW hr), inv_mul_cancel,
        burnsideC41b_conjCoord_one]
    · intro c
      exact hfix r hr _ (W₀.smul_mem c hw₀)
  let θL : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := burnsideC41b_conjCoord e r
      map_add' := burnsideC41b_conjCoord_add e (hRW hr)
      map_smul' := hlin }
  obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
  have hrm : r ^ (2 ^ m) = 1 := by
    have h := congrArg Subtype.val hm
    simpa using h
  have hpow : θL ^ (2 ^ m) = 1 := by
    apply LinearMap.ext
    intro v
    rw [Module.End.pow_apply, Module.End.one_apply]
    have h1 : (⇑θL)^[2 ^ m] = (burnsideC41b_conjCoord e r)^[2 ^ m] := rfl
    rw [h1, ← burnsideC41b_conjCoord_pow e (hRW hr), hrm, burnsideC41b_conjCoord_one]
  have hdet : (LinearMap.toMatrix' θL).det = 1 := by
    rw [LinearMap.det_toMatrix']
    apply burnsideC41b_eq_one_of_pow_two_pow hF (m := m)
    rw [← map_pow, hpow, map_one]
  let γ : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix' θL)
    (by rw [hdet]; exact one_ne_zero)
  have hγ : γ ∈ StatedSL 3 F := by
    apply Subgroup.subset_closure
    show (γ : Matrix (Fin 3) (Fin 3) F).det = 1
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hdet
  obtain ⟨k, hk⟩ := hα ⟨γ, hγ⟩
  have hθk : ∀ v, burnsideC41b_conjCoord e (k : G) v = burnsideC41b_conjCoord e r v := by
    intro v
    obtain ⟨u, rfl⟩ := burnsideC41b_exists_coord e v
    rw [burnsideC41b_conjCoord_spec e u ⟨_, burnsideC41b_conj_mem (hKW k.2) u⟩ rfl,
      hβeq k u ⟨_, burnsideC41b_conj_mem (hKW k.2) u⟩ rfl, hk]
    show (γ : Matrix (Fin 3) (Fin 3) F).mulVec _ = _
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, ← Matrix.toLin'_apply,
      Matrix.toLin'_toMatrix']
    rfl
  have hkW : (k : G) ∈ Subgroup.normalizer (W : Set G) := hKW k.2
  have hkW' : (k : G)⁻¹ ∈ Subgroup.normalizer (W : Set G) := hKW (K.inv_mem k.2)
  have hid : ∀ v, burnsideC41b_conjCoord e ((k : G)⁻¹ * r) v = v := by
    intro v
    rw [burnsideC41b_conjCoord_mul e hkW' (hRW hr), ← hθk v,
      ← burnsideC41b_conjCoord_mul e hkW' hkW, inv_mul_cancel, burnsideC41b_conjCoord_one]
  have hcen := burnsideC41b_mem_centralizer_of_conjCoord e
    (Subgroup.mul_mem _ hkW' (hRW hr)) hid
  have hkC : (k : G)⁻¹ * r ∈ C :=
    hCP _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem k.2))
      (Subgroup.mem_sup_right hr)) hcen
  have hr_eq : r = (k : G) * ((k : G)⁻¹ * r) := by group
  rw [hr_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hkC)

end CFSG.ASVolI
