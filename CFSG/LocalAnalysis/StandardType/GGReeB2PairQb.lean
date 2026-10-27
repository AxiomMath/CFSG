module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzProbe
public import CFSG.LocalAnalysis.StandardType.GGReeB2WeightApi

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private theorem qb_span_ub_fixed {K : Type} [Field K] {m : ℕ}
    {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type} [AddCommGroup W]
    [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W) (v : W)
    (hvU : ∀ u ∈ 𝔇.U, ρ u v = v) :
    ∀ w ∈ Submodule.span k (Set.range fun g : suzukiGroup m K => (ρ.comp 𝔇.φ₁) g v),
      ∀ u ∈ 𝔇.Ub, ρ u w = w := by
  intro w hw
  refine Submodule.span_induction (p := fun x _ => ∀ u ∈ 𝔇.Ub, ρ u x = x) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨g, rfl⟩ u hu
    change ρ u (ρ (𝔇.φ₁ g) v) = ρ (𝔇.φ₁ g) v
    have hconj : (𝔇.φ₁ g)⁻¹ * u * 𝔇.φ₁ g ∈ 𝔇.Ub := by
      have h := 𝔇.Ub_norm g⁻¹ u hu
      simpa only [map_inv, inv_inv] using h
    have hfix : ρ ((𝔇.φ₁ g)⁻¹ * u * 𝔇.φ₁ g) v = v := hvU _ (𝔇.Ub_le hconj)
    have hgroup : u * 𝔇.φ₁ g = 𝔇.φ₁ g * ((𝔇.φ₁ g)⁻¹ * u * 𝔇.φ₁ g) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    calc ρ u (ρ (𝔇.φ₁ g) v)
        = ρ (u * 𝔇.φ₁ g) v := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (𝔇.φ₁ g * ((𝔇.φ₁ g)⁻¹ * u * 𝔇.φ₁ g)) v := by rw [hgroup]
      _ = ρ (𝔇.φ₁ g) (ρ ((𝔇.φ₁ g)⁻¹ * u * 𝔇.φ₁ g) v) := by
            rw [map_mul, Module.End.mul_apply]
      _ = ρ (𝔇.φ₁ g) v := by rw [hfix]
  · intro u _
    rw [map_zero]
  · intro a b _ _ ha hb u hu
    rw [map_add, ha u hu, hb u hu]
  · intro c a _ ha u hu
    rw [LinearMap.map_smul, ha u hu]

private theorem qb_span_phi2 {K : Type} [Field K] {m : ℕ}
    {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type} [AddCommGroup W]
    [Module k W] (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W) (v : W)
    (lam₂ : ZMod (2 ^ (2 * m + 1) - 1))
    (hv2 : ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v = ((wchar1 (K := K) k lam₂ l : kˣ) : k) • v) :
    ∀ w ∈ Submodule.span k (Set.range fun g : suzukiGroup m K => (ρ.comp 𝔇.φ₁) g v),
      ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) w = ((wchar1 (K := K) k lam₂ l : kˣ) : k) • w := by
  intro w hw
  refine Submodule.span_induction
    (p := fun x _ => ∀ l : Kˣ,
      ρ (𝔇.φ₂ (szD K m l)) x = ((wchar1 (K := K) k lam₂ l : kˣ) : k) • x) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨g, rfl⟩ l
    change ρ (𝔇.φ₂ (szD K m l)) (ρ (𝔇.φ₁ g) v) =
      ((wchar1 (K := K) k lam₂ l : kˣ) : k) • ρ (𝔇.φ₁ g) v
    have hcomm : 𝔇.φ₂ (szD K m l) * 𝔇.φ₁ g = 𝔇.φ₁ g * 𝔇.φ₂ (szD K m l) :=
      (𝔇.comm g (szD K m l)).symm
    calc ρ (𝔇.φ₂ (szD K m l)) (ρ (𝔇.φ₁ g) v)
        = ρ (𝔇.φ₂ (szD K m l) * 𝔇.φ₁ g) v := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (𝔇.φ₁ g * 𝔇.φ₂ (szD K m l)) v := by rw [hcomm]
      _ = ρ (𝔇.φ₁ g) (ρ (𝔇.φ₂ (szD K m l)) v) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (𝔇.φ₁ g) (((wchar1 (K := K) k lam₂ l : kˣ) : k) • v) := by rw [hv2 l]
      _ = ((wchar1 (K := K) k lam₂ l : kˣ) : k) • ρ (𝔇.φ₁ g) v := by
            rw [LinearMap.map_smul]
  · intro l
    rw [map_zero, smul_zero]
  · intro a b _ _ ha hb l
    rw [map_add, ha l, hb l, smul_add]
  · intro c a _ ha l
    rw [LinearMap.map_smul, ha l, smul_comm]

theorem qb_probe {K : Type} [Field K] [CharP K 2] [Fintype K]
    {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] [CharP k 2] [IsAlgClosed k]
    {W : Type} [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    (v : W) (hv : v ≠ 0) (hvU : ∀ u ∈ 𝔇.U, ρ u v = v)
    (lam : ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1))
    (hlam : v ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k lam.1 lam.2)) (h1 : lam.1 ≠ 0)
    (I : Finset (Fin (2 * m + 1))) (hI : hw m I = lam.1) :
    ∀ κ ∈ wtSet m I, ∃ w : W, w ≠ 0 ∧ (∀ u ∈ 𝔇.Ub, ρ u w = w) ∧
      w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ lam.2) := by
  intro κ hκ
  have hlamg : ∀ g : Kˣ × Kˣ,
      (ρ.comp 𝔇.tau) g v = (wchar (K := K) k lam.1 lam.2 g : k) • v :=
    (mem_weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k lam.1 lam.2) v).mp hlam
  have hfix : ∀ x ∈ szUp m K, (ρ.comp 𝔇.φ₁) x v = v := by
    intro x hx
    change ρ (𝔇.φ₁ x) v = v
    exact hvU (𝔇.φ₁ x) (𝔇.up₁ x hx)
  have hwt : ∀ l : Kˣ, (ρ.comp 𝔇.φ₁) (szD K m l) v =
      ((wchar1 (K := K) k lam.1 l : kˣ) : k) • v := by
    intro l
    change ρ (𝔇.φ₁ (szD K m l)) v = ((wchar1 (K := K) k lam.1 l : kˣ) : k) • v
    have h := hlamg (l, 1)
    rw [MonoidHom.comp_apply, SzPairDatum.tau_apply, wchar_apply] at h
    simpa using h
  obtain ⟨J, hJ, hJprop⟩ :=
    szProbe (K := K) k hK (ρ.comp 𝔇.φ₁) v hv hfix lam.1 hwt
  have hIJ : I = J := hw_inj m (I := I) (J := J) (by rw [hI, hJ]) (by rw [hI]; exact h1)
  have hκJ : κ ∈ wtSet m J := by rw [← hIJ]; exact hκ
  obtain ⟨u', hu'mem, hu'ne, hu'wt⟩ := hJprop κ hκJ
  have hu'fix : ∀ u ∈ 𝔇.Ub, ρ u u' = u' := qb_span_ub_fixed k 𝔇 ρ v hvU u' hu'mem
  have hu'wt1 : ∀ l : Kˣ, ρ (𝔇.φ₁ (szD K m l)) u' =
      ((wchar1 (K := K) k κ l : kˣ) : k) • u' := by
    intro l
    simpa only [MonoidHom.comp_apply] using hu'wt l
  have hv2 : ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v =
      ((wchar1 (K := K) k lam.2 l : kˣ) : k) • v := by
    intro l
    have h := hlamg (1, l)
    rw [MonoidHom.comp_apply, SzPairDatum.tau_apply, wchar_apply] at h
    simpa using h
  refine ⟨u', hu'ne, hu'fix, ?_⟩
  refine (mem_weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ lam.2) u').mpr ?_
  intro g
  obtain ⟨l₁, l₂⟩ := g
  have h2 := qb_span_phi2 k 𝔇 ρ v lam.2 hv2 u' hu'mem l₂
  rw [MonoidHom.comp_apply, SzPairDatum.tau_apply, wchar_apply]
  calc ρ (𝔇.φ₁ (szD K m l₁) * 𝔇.φ₂ (szD K m l₂)) u'
      = ρ (𝔇.φ₁ (szD K m l₁)) (ρ (𝔇.φ₂ (szD K m l₂)) u') := by
          rw [map_mul, Module.End.mul_apply]
    _ = ρ (𝔇.φ₁ (szD K m l₁)) (((wchar1 (K := K) k lam.2 l₂ : kˣ) : k) • u') := by
          rw [h2]
    _ = ((wchar1 (K := K) k lam.2 l₂ : kˣ) : k) • ρ (𝔇.φ₁ (szD K m l₁)) u' := by
          rw [LinearMap.map_smul]
    _ = ((wchar1 (K := K) k lam.2 l₂ : kˣ) : k) •
          (((wchar1 (K := K) k κ l₁ : kˣ) : k) • u') := by rw [hu'wt1 l₁]
    _ = ((wchar1 (K := K) k κ l₁ * wchar1 (K := K) k lam.2 l₂ : kˣ) : k) • u' := by
          rw [smul_smul, ← Units.val_mul,
            mul_comm (wchar1 (K := K) k lam.2 l₂) (wchar1 (K := K) k κ l₁)]

end CFSG.StandardType.ReeB2Fixed
