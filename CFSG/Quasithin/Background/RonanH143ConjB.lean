module

public import CFSG.Quasithin.Background.RonanH143ConjA

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code

@[expose] noncomputable def conjBwEquiv (c : P24) (H : Subgroup P24) : ↥(conjSubg c H) ≃* ↥H where
  toFun y := ⟨c⁻¹ * (y : P24) * c, mem_conjSubg_iff.1 y.2⟩
  invFun x := ⟨c * (x : P24) * c⁻¹, by
    show c * (x : P24) * c⁻¹ ∈ conjSubg c H
    rw [mem_conjSubg_iff, show c⁻¹ * (c * (x : P24) * c⁻¹) * c = (x : P24) by group]
    exact x.2⟩
  left_inv y := Subtype.ext (by
    show c * (c⁻¹ * (y : P24) * c) * c⁻¹ = (y : P24)
    group)
  right_inv x := Subtype.ext (by
    show c⁻¹ * (c * (x : P24) * c⁻¹) * c = (x : P24)
    group)
  map_mul' y z := Subtype.ext (by
    show c⁻¹ * ((y : P24) * (z : P24)) * c = (c⁻¹ * (y : P24) * c) * (c⁻¹ * (z : P24) * c)
    group)

theorem conjBwEquiv_coe (c : P24) (H : Subgroup P24) (y : ↥(conjSubg c H)) :
    ((conjBwEquiv c H y : ↥H) : P24) = c⁻¹ * (y : P24) * c := rfl

theorem conjBw_conjSubg_mul (a b : P24) (W : Subgroup P24) :
    conjSubg a (conjSubg b W) = conjSubg (a * b) W := by
  ext x
  simp only [mem_conjSubg_iff]
  rw [show b⁻¹ * (a⁻¹ * x * a) * b = (a * b)⁻¹ * x * (a * b) by group]

theorem conjBw_ConjIsoModel_fwd (c : P24) (G K : Subgroup P24) (A : Type*) [CommGroup A]
    (Γ : Set (MulAut A)) (h : ConjIsoModel G K A Γ) :
    ConjIsoModel (conjSubg c G) (conjSubg c K) A Γ := by
  obtain ⟨φ, π, hKG, hΓ, hsurj, hker, hφ⟩ := h
  refine ⟨(conjBwEquiv c K).trans φ, π.comp (conjBwEquiv c G).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact conjSubg_le_conjSubg_iff.2 hKG
  · intro g
    exact hΓ (conjBwEquiv c G g)
  · intro γ hγ
    obtain ⟨g, hg⟩ := hsurj γ hγ
    refine ⟨(conjBwEquiv c G).symm g, ?_⟩
    show π (conjBwEquiv c G ((conjBwEquiv c G).symm g)) = γ
    rw [MulEquiv.apply_symm_apply]
    exact hg
  · intro g
    have h4 := hker (conjBwEquiv c G g)
    rw [conjBwEquiv_coe] at h4
    rw [mem_conjSubg_iff]
    exact h4
  · intro g k k' hk
    have key : ((conjBwEquiv c K k' : ↥K) : P24) = ((conjBwEquiv c G g : ↥G) : P24) *
        ((conjBwEquiv c K k : ↥K) : P24) * ((conjBwEquiv c G g : ↥G) : P24)⁻¹ := by
      simp only [conjBwEquiv_coe]
      rw [hk]
      group
    exact hφ _ _ _ key

theorem conjBw_ConjSymNatural_fwd (c : P24) (G K : Subgroup P24) (n : ℕ)
    (R : Subgroup (Equiv.Perm (Fin n))) (h : ConjSymNatural G K n R) :
    ConjSymNatural (conjSubg c G) (conjSubg c K) n R := by
  obtain ⟨hKG, π, β, hπR, hπker, hβrange, hβker, hnat⟩ := h
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom :=
    fun x y hxy => (MulAut.conj c).injective hxy
  have hsurjG : (conjBwEquiv c G).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.2 (fun y => ⟨(conjBwEquiv c G).symm y, (conjBwEquiv c G).apply_symm_apply y⟩)
  refine ⟨conjSubg_le_conjSubg_iff.2 hKG, π.comp (conjBwEquiv c G).toMonoidHom,
    (MulAut.conj c).toMonoidHom.comp β, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hsurjG, ← MonoidHom.range_eq_map, hπR]
  · rw [← MonoidHom.comap_ker, hπker]
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      conjBwEquiv_coe, mem_conjSubg_iff]
  · rw [MonoidHom.range_comp, hβrange]
    rfl
  · rw [MonoidHom.ker_comp_of_injective β (MulAut.conj c).toMonoidHom hinj, hβker]
  · intro g u
    have h1 : β (G6.coreAct n (π (conjBwEquiv c G g)) u) =
        ((conjBwEquiv c G g : ↥G) : P24) * β u * ((conjBwEquiv c G g : ↥G) : P24)⁻¹ :=
      hnat (conjBwEquiv c G g) u
    show (MulAut.conj c) (β (G6.coreAct n (π (conjBwEquiv c G g)) u)) =
      (g : P24) * (MulAut.conj c) (β u) * (g : P24)⁻¹
    rw [h1]
    simp only [MulAut.conj_apply, conjBwEquiv_coe]
    group

theorem conjBw_exists_perm_fwd (c : P24) (M K : Subgroup P24) (n : ℕ)
    (h : ∃ π : ↥M →* Equiv.Perm (Fin n), π.range = ⊤ ∧ π.ker = K.subgroupOf M) :
    ∃ π : ↥(conjSubg c M) →* Equiv.Perm (Fin n), π.range = ⊤ ∧
        π.ker = (conjSubg c K).subgroupOf (conjSubg c M) := by
  obtain ⟨π, hr, hk⟩ := h
  have hsurjM : (conjBwEquiv c M).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.2 (fun y => ⟨(conjBwEquiv c M).symm y, (conjBwEquiv c M).apply_symm_apply y⟩)
  refine ⟨π.comp (conjBwEquiv c M).toMonoidHom, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hsurjM, ← MonoidHom.range_eq_map, hr]
  · rw [← MonoidHom.comap_ker, hk]
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      conjBwEquiv_coe, mem_conjSubg_iff]

theorem conjBw_indec_fwd (c : P24) (M K : Subgroup P24)
    (h : ∀ W₁ W₂ : Subgroup P24, W₁ ≤ K → W₂ ≤ K →
        (∀ g ∈ M, conjSubg g W₁ = W₁) → (∀ g ∈ M, conjSubg g W₂ = W₂) →
        W₁ ⊔ W₂ = K → W₁ ⊓ W₂ = ⊥ → W₁ = ⊥ ∨ W₂ = ⊥) :
    ∀ W₁ W₂ : Subgroup P24, W₁ ≤ conjSubg c K → W₂ ≤ conjSubg c K →
        (∀ g ∈ conjSubg c M, conjSubg g W₁ = W₁) → (∀ g ∈ conjSubg c M, conjSubg g W₂ = W₂) →
        W₁ ⊔ W₂ = conjSubg c K → W₁ ⊓ W₂ = ⊥ → W₁ = ⊥ ∨ W₂ = ⊥ := by
  intro W₁ W₂ h₁ h₂ hs₁ hs₂ hj hm
  have hle : ∀ W : Subgroup P24, W ≤ conjSubg c K → conjSubg c⁻¹ W ≤ K := by
    intro W hW
    have h0 := (conjSubg_le_conjSubg_iff (c := c⁻¹)).2 hW
    rwa [conjSubg_conjSubg_inv] at h0
  have hstab : ∀ W : Subgroup P24, (∀ g ∈ conjSubg c M, conjSubg g W = W) →
      ∀ g ∈ M, conjSubg g (conjSubg c⁻¹ W) = conjSubg c⁻¹ W := by
    intro W hW g hg
    have hx : c * g * c⁻¹ ∈ conjSubg c M := by
      rw [mem_conjSubg_iff, show c⁻¹ * (c * g * c⁻¹) * c = g by group]
      exact hg
    calc conjSubg g (conjSubg c⁻¹ W) = conjSubg (g * c⁻¹) W := conjBw_conjSubg_mul _ _ _
      _ = conjSubg (c⁻¹ * (c * g * c⁻¹)) W := by
          rw [show c⁻¹ * (c * g * c⁻¹) = g * c⁻¹ by group]
      _ = conjSubg c⁻¹ (conjSubg (c * g * c⁻¹) W) := (conjBw_conjSubg_mul _ _ _).symm
      _ = conjSubg c⁻¹ W := by rw [hW _ hx]
  have hj' : conjSubg c⁻¹ W₁ ⊔ conjSubg c⁻¹ W₂ = K := by
    rw [← conjSubg_sup, hj, conjSubg_conjSubg_inv]
  have hm' : conjSubg c⁻¹ W₁ ⊓ conjSubg c⁻¹ W₂ = ⊥ := by
    rw [← conjSubg_inf, hm, conjSubg_bot]
  rcases h (conjSubg c⁻¹ W₁) (conjSubg c⁻¹ W₂) (hle W₁ h₁) (hle W₂ h₂)
      (hstab W₁ hs₁) (hstab W₂ hs₂) hj' hm' with h1 | h2
  · exact Or.inl (conjSubg_inj.1 (h1.trans (conjSubg_bot c⁻¹).symm))
  · exact Or.inr (conjSubg_inj.1 (h2.trans (conjSubg_bot c⁻¹).symm))

theorem ConjIsoModel_conj (c : P24) (G K : Subgroup P24) (A : Type*) [CommGroup A]
    (Γ : Set (MulAut A)) :
    ConjIsoModel (conjSubg c G) (conjSubg c K) A Γ ↔ ConjIsoModel G K A Γ := by
  constructor
  · intro h
    have h' := conjBw_ConjIsoModel_fwd c⁻¹ _ _ A Γ h
    rw [conjSubg_conjSubg_inv, conjSubg_conjSubg_inv] at h'
    exact h'
  · intro h
    exact conjBw_ConjIsoModel_fwd c G K A Γ h

theorem ConjSymNatural_conj (c : P24) (G K : Subgroup P24) (n : ℕ)
    (R : Subgroup (Equiv.Perm (Fin n))) :
    ConjSymNatural (conjSubg c G) (conjSubg c K) n R ↔ ConjSymNatural G K n R := by
  constructor
  · intro h
    have h' := conjBw_ConjSymNatural_fwd c⁻¹ _ _ n R h
    rw [conjSubg_conjSubg_inv, conjSubg_conjSubg_inv] at h'
    exact h'
  · intro h
    exact conjBw_ConjSymNatural_fwd c G K n R h

theorem exists_perm_surj_conj (c : P24) (M K : Subgroup P24) (n : ℕ) :
    (∃ π : ↥(conjSubg c M) →* Equiv.Perm (Fin n), π.range = ⊤ ∧
        π.ker = (conjSubg c K).subgroupOf (conjSubg c M)) ↔
      (∃ π : ↥M →* Equiv.Perm (Fin n), π.range = ⊤ ∧ π.ker = K.subgroupOf M) := by
  constructor
  · intro h
    have h' := conjBw_exists_perm_fwd c⁻¹ (conjSubg c M) (conjSubg c K) n h
    rw [conjSubg_conjSubg_inv c M, conjSubg_conjSubg_inv c K] at h'
    exact h'
  · intro h
    exact conjBw_exists_perm_fwd c M K n h

theorem indecomposable_conj (c : P24) (M K : Subgroup P24) :
    (∀ W₁ W₂ : Subgroup P24, W₁ ≤ conjSubg c K → W₂ ≤ conjSubg c K →
        (∀ g ∈ conjSubg c M, conjSubg g W₁ = W₁) → (∀ g ∈ conjSubg c M, conjSubg g W₂ = W₂) →
        W₁ ⊔ W₂ = conjSubg c K → W₁ ⊓ W₂ = ⊥ → W₁ = ⊥ ∨ W₂ = ⊥) ↔
      (∀ W₁ W₂ : Subgroup P24, W₁ ≤ K → W₂ ≤ K →
        (∀ g ∈ M, conjSubg g W₁ = W₁) → (∀ g ∈ M, conjSubg g W₂ = W₂) →
        W₁ ⊔ W₂ = K → W₁ ⊓ W₂ = ⊥ → W₁ = ⊥ ∨ W₂ = ⊥) := by
  constructor
  · intro h
    have h' := conjBw_indec_fwd c⁻¹ (conjSubg c M) (conjSubg c K) h
    rw [conjSubg_conjSubg_inv c M, conjSubg_conjSubg_inv c K] at h'
    exact h'
  · intro h
    exact conjBw_indec_fwd c M K h

end CFSG.Quasithin.RonanH143
