module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzWeights
public import TauCeti.RepresentationTheory.Unipotent.PowerOrder

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private theorem tau_conj_mem {K : Type} [Field K] {m : ℕ} {Γ : Type}
    [Group Γ] (𝔇 : SzPairDatum K m Γ) (g : Kˣ × Kˣ) {u : Γ} (hu : u ∈ 𝔇.U) :
    𝔇.tau g * u * (𝔇.tau g)⁻¹ ∈ 𝔇.U := by
  obtain ⟨l₁, l₂⟩ := g
  exact 𝔇.T_norm l₁ l₂ u hu

private theorem tau_inv_conj_mem {K : Type} [Field K] {m : ℕ}
    {Γ : Type} [Group Γ] (𝔇 : SzPairDatum K m Γ) (g : Kˣ × Kˣ) {u : Γ} (hu : u ∈ 𝔇.U) :
    (𝔇.tau g)⁻¹ * u * 𝔇.tau g ∈ 𝔇.U := by
  have h := tau_conj_mem 𝔇 g⁻¹ hu
  simpa using h

private theorem tau_smul_mem_invariants {K : Type} [Field K] {m : ℕ}
    {Γ : Type} [Group Γ] {k : Type} [Field k] [Algebra K k] {W : Type} [AddCommGroup W]
    [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W) (g : Kˣ × Kˣ) {v : W}
    (hv : v ∈ Representation.invariants (ρ.comp 𝔇.U.subtype)) :
    ((ρ.comp 𝔇.tau) g) v ∈ Representation.invariants (ρ.comp 𝔇.U.subtype) := by
  rw [Representation.mem_invariants] at hv ⊢
  intro u
  have hconj : (𝔇.tau g)⁻¹ * (u : Γ) * 𝔇.tau g ∈ 𝔇.U := tau_inv_conj_mem 𝔇 g u.2
  have hfix : ρ ((𝔇.tau g)⁻¹ * (u : Γ) * 𝔇.tau g) v = v := hv ⟨_, hconj⟩
  have hmul : (u : Γ) * 𝔇.tau g = 𝔇.tau g * ((𝔇.tau g)⁻¹ * (u : Γ) * 𝔇.tau g) := by group
  calc (ρ.comp 𝔇.U.subtype) u (((ρ.comp 𝔇.tau) g) v)
      = ρ ((u : Γ) * 𝔇.tau g) v := by
          simp only [MonoidHom.comp_apply]
          rw [← Module.End.mul_apply, ← map_mul]
          rfl
    _ = ρ (𝔇.tau g * ((𝔇.tau g)⁻¹ * (u : Γ) * 𝔇.tau g)) v := by rw [hmul]
    _ = ρ (𝔇.tau g) (ρ ((𝔇.tau g)⁻¹ * (u : Γ) * 𝔇.tau g) v) := by
          rw [map_mul, Module.End.mul_apply]
    _ = ρ (𝔇.tau g) v := by rw [hfix]
    _ = ((ρ.comp 𝔇.tau) g) v := rfl

private theorem exists_weightSpace_ne_bot {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ}
    {k : Type} [Field k] [Algebra K k] [CharP k 2] [IsAlgClosed k]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Nontrivial V] (τ : Representation k Kˣ V) :
    ∃ x : ZMod (2 ^ (2 * m + 1) - 1), weightSpace τ (wchar1 (K := K) k x) ≠ ⊥ := by
  by_contra h
  have hbot : ∀ x : ZMod (2 ^ (2 * m + 1) - 1), weightSpace τ (wchar1 (K := K) k x) = ⊥ := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have htop : (⊤ : Submodule k V) = ⊥ := by
    rw [← iSup_weightSpace_wchar1 (K := K) k hK τ, iSup_eq_bot.mpr hbot]
  obtain ⟨v, hv⟩ := (nontrivial_iff_exists_ne (0 : V)).mp ‹Nontrivial V›
  have hvbot : v ∈ (⊥ : Submodule k V) := by rw [← htop]; trivial
  have hv0 : v = 0 := by simpa using hvbot
  exact hv hv0

theorem exists_U_fixed_weight {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] [CharP k 2]
    [IsAlgClosed k] {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W] [Nontrivial W]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W) :
    ∃ (v : W) (lam : ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1)), v ≠ 0 ∧
      (∀ u ∈ 𝔇.U, ρ u v = v) ∧
      v ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k lam.1 lam.2) := by
  classical
  let S : Submodule k W := Representation.invariants (ρ.comp 𝔇.U.subtype)
  have hSne : S ≠ ⊥ := by
    have h := Representation.invariants_ne_bot_of_isPGroup 2 𝔇.pgroup (ρ.comp 𝔇.U.subtype)
    simpa [S] using h
  haveI : Nontrivial S := (Submodule.nontrivial_iff_ne_bot (p := S)).mpr hSne
  have hle : ∀ g : Kˣ × Kˣ, S ≤ S.comap ((ρ.comp 𝔇.tau) g) := by
    intro g v hv
    rw [Submodule.mem_comap]
    change ((ρ.comp 𝔇.tau) g) v ∈ Representation.invariants (ρ.comp 𝔇.U.subtype)
    exact tau_smul_mem_invariants 𝔇 ρ g hv
  let σ : Representation k (Kˣ × Kˣ) S :=
    Representation.subrepresentation (ρ.comp 𝔇.tau) S hle
  let τ₁ : Representation k Kˣ S := σ.comp (MonoidHom.inl Kˣ Kˣ)
  let τ₂ : Representation k Kˣ S := σ.comp (MonoidHom.inr Kˣ Kˣ)
  obtain ⟨x₁, hx₁⟩ := exists_weightSpace_ne_bot (K := K) (m := m) (k := k) hK τ₁
  let F₁ : Submodule k S := weightSpace τ₁ (wchar1 (K := K) k x₁)
  have hF₁ : F₁ ≠ ⊥ := hx₁
  haveI : Nontrivial F₁ := (Submodule.nontrivial_iff_ne_bot (p := F₁)).mpr hF₁
  have hle₂ : ∀ l : Kˣ, F₁ ≤ F₁.comap (τ₂ l) := by
    intro l v hv
    rw [Submodule.mem_comap]
    change v ∈ weightSpace τ₁ (wchar1 (K := K) k x₁) at hv
    change τ₂ l v ∈ weightSpace τ₁ (wchar1 (K := K) k x₁)
    rw [mem_weightSpace] at hv ⊢
    intro l'
    have hcomm : τ₁ l' (τ₂ l v) = τ₂ l (τ₁ l' v) := by
      have h₁ : τ₁ l' = σ (l', 1) := rfl
      have h₂ : τ₂ l = σ (1, l) := rfl
      rw [h₁, h₂]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      have hprod : (l', 1) * (1, l) = (1, l) * (l', 1) := by ext <;> simp
      rw [hprod]
    rw [hcomm, hv l', map_smul]
  let σ₂ : Representation k Kˣ F₁ := Representation.subrepresentation τ₂ F₁ hle₂
  obtain ⟨x₂, hx₂⟩ := exists_weightSpace_ne_bot (K := K) (m := m) (k := k) hK σ₂
  obtain ⟨v, hvF₂, hvne⟩ :=
    (Submodule.ne_bot_iff (weightSpace σ₂ (wchar1 (K := K) k x₂))).1 hx₂
  have hv₁ : ∀ l : Kˣ, σ (l, 1) v.val = (wchar1 (K := K) k x₁ l : k) • v.val := by
    intro l
    have h := (mem_weightSpace τ₁ (wchar1 (K := K) k x₁) v.val).1 v.property l
    rwa [show τ₁ l = σ (l, 1) from rfl] at h
  have hv₂ : ∀ l : Kˣ, σ (1, l) v.val = (wchar1 (K := K) k x₂ l : k) • v.val := by
    intro l
    have h := (mem_weightSpace σ₂ (wchar1 (K := K) k x₂) v).1 hvF₂ l
    have h2 : (σ₂ l v).val = σ (1, l) v.val := rfl
    have h3 : ((wchar1 (K := K) k x₂ l : k) • v).val =
        (wchar1 (K := K) k x₂ l : k) • v.val := rfl
    have h4 := congrArg Subtype.val h
    rw [h2, h3] at h4
    exact h4
  have hfix₁ : ∀ l₁ : Kˣ, ρ (𝔇.tau (l₁, 1)) v.val.val =
      (wchar1 (K := K) k x₁ l₁ : k) • v.val.val := by
    intro l₁
    have h : ρ (𝔇.tau (l₁, 1)) v.val.val = (σ (l₁, 1) v.val).val := rfl
    rw [h, hv₁ l₁]
    rfl
  have hfix₂ : ∀ l₂ : Kˣ, ρ (𝔇.tau (1, l₂)) v.val.val =
      (wchar1 (K := K) k x₂ l₂ : k) • v.val.val := by
    intro l₂
    have h : ρ (𝔇.tau (1, l₂)) v.val.val = (σ (1, l₂) v.val).val := rfl
    rw [h, hv₂ l₂]
    rfl
  refine ⟨v.val.val, (x₁, x₂), ?_, ?_, ?_⟩
  · intro h
    exact hvne (Subtype.ext (Subtype.ext h))
  · intro u hu
    have hmem : v.val.val ∈ Representation.invariants (ρ.comp 𝔇.U.subtype) := v.val.property
    have hfix := (Representation.mem_invariants (ρ.comp 𝔇.U.subtype) v.val.val).1 hmem ⟨u, hu⟩
    simpa using hfix
  · rw [mem_weightSpace]
    rintro ⟨l₁, l₂⟩
    have htau : 𝔇.tau (l₁, l₂) = 𝔇.tau (l₁, 1) * 𝔇.tau (1, l₂) := by
      rw [← map_mul]
      congr 1
      ext <;> simp
    calc ρ (𝔇.tau (l₁, l₂)) v.val.val
        = ρ (𝔇.tau (l₁, 1) * 𝔇.tau (1, l₂)) v.val.val := by rw [htau]
      _ = ρ (𝔇.tau (l₁, 1)) (ρ (𝔇.tau (1, l₂)) v.val.val) := by
            rw [map_mul, Module.End.mul_apply]
      _ = ρ (𝔇.tau (l₁, 1)) ((wchar1 (K := K) k x₂ l₂ : k) • v.val.val) := by
            rw [hfix₂ l₂]
      _ = (wchar1 (K := K) k x₂ l₂ : k) • ρ (𝔇.tau (l₁, 1)) v.val.val := by rw [map_smul]
      _ = (wchar1 (K := K) k x₂ l₂ : k) • ((wchar1 (K := K) k x₁ l₁ : k) • v.val.val) := by
            rw [hfix₁ l₁]
      _ = ((wchar k x₁ x₂ (l₁, l₂) : kˣ) : k) • v.val.val := by
            have h : ((wchar k x₁ x₂ (l₁, l₂) : kˣ) : k) =
                (wchar1 (K := K) k x₂ l₂ : k) * (wchar1 (K := K) k x₁ l₁ : k) := by
              rw [wchar_apply, Units.val_mul, mul_comm]
            rw [h, smul_smul]

end CFSG.StandardType.ReeB2Fixed
