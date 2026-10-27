module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzProbe
public import CFSG.LocalAnalysis.StandardType.GGReeB2WeightApi

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private theorem pair_conj_apply {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] {k : Type} [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    (g z : suzukiGroup m K) (v : W) :
    ρ (𝔇.φ₂ z) (ρ (𝔇.φ₁ g) v) = ρ (𝔇.φ₁ g) (ρ (𝔇.φ₂ z) v) := by
  simp only [← Module.End.mul_apply, ← map_mul, 𝔇.comm g z]

private theorem pair_conj_apply' {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] {k : Type} [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    (g z : suzukiGroup m K) (v : W) :
    ρ (𝔇.φ₁ z) (ρ (𝔇.φ₂ g) v) = ρ (𝔇.φ₂ g) (ρ (𝔇.φ₁ z) v) := by
  simp only [← Module.End.mul_apply, ← map_mul, (𝔇.comm z g).symm]

private theorem span_φ₂_apply {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] {k : Type} [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    (u : W) (z : suzukiGroup m K) (c : k) (hu : ρ (𝔇.φ₂ z) u = c • u) :
    ∀ v ∈ Submodule.span k (Set.range fun g => ρ (𝔇.φ₁ g) u), ρ (𝔇.φ₂ z) v = c • v := by
  intro v hv
  refine Submodule.span_induction (p := fun x _ => ρ (𝔇.φ₂ z) x = c • x) ?_ ?_ ?_ ?_ hv
  · rintro x ⟨g, rfl⟩
    rw [pair_conj_apply, hu, map_smul]
  · simp
  · intro x y _ _ ihx ihy
    rw [map_add, ihx, ihy, smul_add]
  · intro a x _ ih
    rw [map_smul, ih, smul_comm]

private theorem span_φ₁_apply {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] {k : Type} [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    (u : W) (z : suzukiGroup m K) (c : k) (hu : ρ (𝔇.φ₁ z) u = c • u) :
    ∀ v ∈ Submodule.span k (Set.range fun g => ρ (𝔇.φ₂ g) u), ρ (𝔇.φ₁ z) v = c • v := by
  intro v hv
  refine Submodule.span_induction (p := fun x _ => ρ (𝔇.φ₁ z) x = c • x) ?_ ?_ ?_ ?_ hv
  · rintro x ⟨g, rfl⟩
    rw [pair_conj_apply', hu, map_smul]
  · simp
  · intro x y _ _ ihx ihy
    rw [map_add, ihx, ihy, smul_add]
  · intro a x _ ih
    rw [map_smul, ih, smul_comm]

private theorem tau_mem_weightSpace {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] {k : Type} [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    (x y : ZMod (2 ^ (2 * m + 1) - 1)) (v : W)
    (hφ₁ : ∀ l : Kˣ, ρ (𝔇.φ₁ (szD K m l)) v = ((wchar1 (K := K) k x l : kˣ) : k) • v)
    (hφ₂ : ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v = ((wchar1 (K := K) k y l : kˣ) : k) • v) :
    v ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k x y) := by
  rintro ⟨l₁, l₂⟩
  calc (ρ.comp 𝔇.tau) (l₁, l₂) v
      = ρ (𝔇.φ₁ (szD K m l₁)) (ρ (𝔇.φ₂ (szD K m l₂)) v) := by
          rw [MonoidHom.comp_apply, SzPairDatum.tau_apply, map_mul, Module.End.mul_apply]
    _ = ρ (𝔇.φ₁ (szD K m l₁)) (((wchar1 (K := K) k y l₂ : kˣ) : k) • v) := by rw [hφ₂ l₂]
    _ = ((wchar1 (K := K) k y l₂ : kˣ) : k) • ρ (𝔇.φ₁ (szD K m l₁)) v := by rw [map_smul]
    _ = ((wchar1 (K := K) k y l₂ : kˣ) : k) •
          (((wchar1 (K := K) k x l₁ : kˣ) : k) • v) := by rw [hφ₁ l₁]
    _ = (((wchar1 (K := K) k y l₂ : kˣ) : k) *
          ((wchar1 (K := K) k x l₁ : kˣ) : k)) • v := by rw [smul_smul]
    _ = (((wchar1 (K := K) k x l₁ : kˣ) : k) *
          ((wchar1 (K := K) k y l₂ : kˣ) : k)) • v := by rw [mul_comm]
    _ = (wchar (K := K) k x y (l₁, l₂) : k) • v := by rw [wchar_apply, Units.val_mul]

theorem hw_probe {K : Type} [Field K] [CharP K 2] [Fintype K]
    {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] [CharP k 2] [IsAlgClosed k]
    {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    (u : W) (hu : u ≠ 0) (hX₁ : ∀ x ∈ szUp m K, ρ (𝔇.φ₁ x) u = u)
    (hX₂ : ∀ x ∈ szUp m K, ρ (𝔇.φ₂ x) u = u)
    (κ : ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1))
    (hκ : u ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ.1 κ.2))
    (h1 : κ.1 ≠ 0) (h2 : κ.2 ≠ 0) :
    ∃ I J : Finset (Fin (2 * m + 1)), hw m I = κ.1 ∧ hw m J = κ.2 ∧
      ∀ x ∈ wtSet m I, ∀ y ∈ wtSet m J, (x, y) ∈ 𝔇.wt k ρ := by
  have hσ₁ : ∀ l : Kˣ, (ρ.comp 𝔇.φ₁) (szD K m l) u =
      ((wchar1 (K := K) k κ.1 l : kˣ) : k) • u := by
    intro l
    have h := hκ (l, 1)
    simpa [MonoidHom.comp_apply, SzPairDatum.tau_apply, wchar_apply] using h
  have hσ₂ : ∀ l : Kˣ, (ρ.comp 𝔇.φ₂) (szD K m l) u =
      ((wchar1 (K := K) k κ.2 l : kˣ) : k) • u := by
    intro l
    have h := hκ (1, l)
    simpa [MonoidHom.comp_apply, SzPairDatum.tau_apply, wchar_apply] using h
  obtain ⟨J, hJ, -⟩ := szProbe (K := K) k hK (ρ.comp 𝔇.φ₂) u hu hX₂ κ.2 hσ₂
  obtain ⟨I, hI, hIwt⟩ := szProbe (K := K) k hK (ρ.comp 𝔇.φ₁) u hu hX₁ κ.1 hσ₁
  refine ⟨I, J, hI, hJ, ?_⟩
  intro x hx y hy
  obtain ⟨u₁, hu₁M, hu₁ne, hu₁wt⟩ := hIwt x hx
  have hu₁wt' : ∀ l : Kˣ, ρ (𝔇.φ₁ (szD K m l)) u₁ =
      ((wchar1 (K := K) k x l : kˣ) : k) • u₁ := fun l => hu₁wt l
  have hfix₁ : ∀ z ∈ szUp m K, (ρ.comp 𝔇.φ₂) z u₁ = u₁ := by
    intro z hz
    have h := span_φ₂_apply 𝔇 ρ u z (1 : k) (by simpa using hX₂ z hz) u₁ hu₁M
    simpa using h
  have hwt₁ : ∀ l : Kˣ, (ρ.comp 𝔇.φ₂) (szD K m l) u₁ =
      ((wchar1 (K := K) k κ.2 l : kˣ) : k) • u₁ := by
    intro l
    exact span_φ₂_apply 𝔇 ρ u (szD K m l)
      ((wchar1 (K := K) k κ.2 l : kˣ) : k) (hσ₂ l) u₁ hu₁M
  obtain ⟨J', hJ', hJ'wt⟩ := szProbe (K := K) k hK (ρ.comp 𝔇.φ₂) u₁ hu₁ne hfix₁ κ.2 hwt₁
  have hJ'J : J' = J :=
    hw_inj m (I := J') (J := J) (hJ'.trans hJ.symm) (by rw [hJ']; exact h2)
  have hy' : y ∈ wtSet m J' := by rw [hJ'J]; exact hy
  obtain ⟨u₂, hu₂M, hu₂ne, hu₂wt⟩ := hJ'wt y hy'
  have hu₂wt' : ∀ l : Kˣ, ρ (𝔇.φ₁ (szD K m l)) u₂ =
      ((wchar1 (K := K) k x l : kˣ) : k) • u₂ := by
    intro l
    exact span_φ₁_apply 𝔇 ρ u₁ (szD K m l)
      ((wchar1 (K := K) k x l : kˣ) : k) (hu₁wt' l) u₂ hu₂M
  have hmem : u₂ ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k x y) :=
    tau_mem_weightSpace 𝔇 ρ x y u₂ hu₂wt' hu₂wt
  exact (Submodule.ne_bot_iff _).mpr ⟨u₂, hmem, hu₂ne⟩

end CFSG.StandardType.ReeB2Fixed
