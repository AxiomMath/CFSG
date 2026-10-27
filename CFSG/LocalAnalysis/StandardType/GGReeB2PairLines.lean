module

public import CFSG.LocalAnalysis.StandardType.GGReeB2PairDefs
public import CFSG.LocalAnalysis.StandardType.GGReeB2WeightDefs

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private theorem wchar1_zero {K : Type} [Field K] {m : ℕ} (k : Type) [Field k] [Algebra K k]
    (l : Kˣ) : wchar1 (K := K) k (0 : ZMod (2 ^ (2 * m + 1) - 1)) l = 1 := by
  simp [wchar1]

private theorem wchar1_inv {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (κ : ZMod (2 ^ (2 * m + 1) - 1)) (l : Kˣ) :
    wchar1 (K := K) k κ l⁻¹ = wchar1 (K := K) k (-κ) l := by
  have h : wchar1 (K := K) k (-κ) l = (wchar1 (K := K) k κ l)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc wchar1 (K := K) k (-κ) l * wchar1 (K := K) k κ l
        = (wchar1 (K := K) k (-κ) * wchar1 (K := K) k κ) l := rfl
      _ = wchar1 (K := K) k (-κ + κ) l := by rw [wchar1_add k hK]
      _ = 1 := by rw [neg_add_cancel, wchar1_zero]
  rw [map_inv, h]

private theorem wchar_na {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ} (k : Type)
    [Field k] [Algebra K k] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (κ₁ κ₂ : ZMod (2 ^ (2 * m + 1) - 1)) (l₁ l₂ : Kˣ) :
    wchar (K := K) k κ₁ κ₂ ((l₂ / l₁) ^ 2 ^ m, (l₁ * l₂) ^ 2 ^ m) =
      wchar (K := K) k (sa m (κ₁, κ₂)).1 (sa m (κ₁, κ₂)).2 (l₁, l₂) := by
  have hsa1 : (sa m (κ₁, κ₂)).1 =
      (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * (κ₂ - κ₁)) := by
    simp only [sa, Nat.cast_pow]
    ring
  have hsa2 : (sa m (κ₁, κ₂)).2 =
      (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * (κ₁ + κ₂)) := by
    simp only [sa, Nat.cast_pow]
    ring
  have hBC : wchar1 (K := K) k
        (-(((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁)) l₁ *
      wchar1 (K := K) k (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂) l₁ =
      wchar1 (K := K) k
        (-(((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁) +
          ((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂) l₁ := by
    rw [← MonoidHom.mul_apply, ← wchar1_add k hK]
  have hAD : wchar1 (K := K) k (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁) l₂ *
      wchar1 (K := K) k (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂) l₂ =
      wchar1 (K := K) k
        (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁ +
          ((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂) l₂ := by
    rw [← MonoidHom.mul_apply, ← wchar1_add k hK]
  trans (wchar1 (K := K) k
          (-(((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁)) l₁ *
        wchar1 (K := K) k (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂) l₁) *
      (wchar1 (K := K) k (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁) l₂ *
        wchar1 (K := K) k (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂) l₂)
  · rw [wchar_apply, wchar1_pow (K := K) k hK κ₁ (2 ^ m) (l₂ / l₁),
      wchar1_pow (K := K) k hK κ₂ (2 ^ m) (l₁ * l₂)]
    simp only [div_eq_mul_inv, map_mul]
    rw [wchar1_inv (K := K) k hK (((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁) l₁]
    ac_rfl
  · rw [hBC, hAD,
      show -(((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁) +
            ((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂ = (sa m (κ₁, κ₂)).1 from by
        rw [hsa1]; ring,
      show ((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₁ +
            ((2 ^ m : ℕ) : ZMod (2 ^ (2 * m + 1) - 1)) * κ₂ = (sa m (κ₁, κ₂)).2 from by
        rw [hsa2]; ring]
    rw [wchar_apply]

private lemma invertible {K : Type} [Field K] {Γ : Type} [Group Γ] (k : Type) [Field k]
    [Algebra K k] {W : Type} [AddCommGroup W] [Module k W] (ρ : Representation k Γ W) (g : Γ)
    {w : W} (hw : w ≠ 0) : ρ g w ≠ 0 := by
  intro h
  have h1 : ρ g⁻¹ (ρ g w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h, map_zero] at h1
  exact hw h1.symm

private lemma na_weight_aux {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    {κ₁ κ₂ : ZMod (2 ^ (2 * m + 1) - 1)} {w : W}
    (hw : w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ₁ κ₂)) :
    ρ 𝔇.na⁻¹ w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k (sa m (κ₁, κ₂)).1 (sa m (κ₁, κ₂)).2) := by
  rw [mem_weightSpace] at hw ⊢
  have hwρ : ∀ g : Kˣ × Kˣ, ρ (𝔇.tau g) w = (wchar (K := K) k κ₁ κ₂ g : k) • w := hw
  intro t
  change ρ (𝔇.tau (t.1, t.2)) (ρ 𝔇.na⁻¹ w) =
    (wchar (K := K) k (sa m (κ₁, κ₂)).1 (sa m (κ₁, κ₂)).2 (t.1, t.2) : k) • ρ 𝔇.na⁻¹ w
  have hna : 𝔇.na⁻¹ = 𝔇.na := inv_eq_of_mul_eq_one_right 𝔇.na_sq
  have hconj : 𝔇.na⁻¹ * 𝔇.tau (t.1, t.2) * 𝔇.na =
      𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) := by
    simpa only [𝔇.tau_apply] using 𝔇.na_conj t.1 t.2
  have hconj' : 𝔇.na⁻¹ * 𝔇.tau (t.1, t.2) * 𝔇.na⁻¹ =
      𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) := by
    simpa only [hna] using hconj
  have hL : 𝔇.na * (𝔇.na⁻¹ * 𝔇.tau (t.1, t.2) * 𝔇.na⁻¹) =
      𝔇.tau (t.1, t.2) * 𝔇.na⁻¹ := by
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hτ : 𝔇.tau (t.1, t.2) * 𝔇.na⁻¹ =
      𝔇.na⁻¹ * 𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) := by
    have h2 : 𝔇.tau (t.1, t.2) * 𝔇.na⁻¹ =
        𝔇.na * 𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) := by
      calc 𝔇.tau (t.1, t.2) * 𝔇.na⁻¹ =
            𝔇.na * (𝔇.na⁻¹ * 𝔇.tau (t.1, t.2) * 𝔇.na⁻¹) := hL.symm
        _ = 𝔇.na * 𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) := by rw [hconj']
    calc 𝔇.tau (t.1, t.2) * 𝔇.na⁻¹ =
          𝔇.na * 𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) := h2
      _ = 𝔇.na⁻¹ * 𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) := by rw [hna]
  have hchar : wchar (K := K) k κ₁ κ₂ ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) =
      wchar (K := K) k (sa m (κ₁, κ₂)).1 (sa m (κ₁, κ₂)).2 (t.1, t.2) := by
    rw [wchar_na (K := K) k hK κ₁ κ₂ t.1 t.2]
  calc ρ (𝔇.tau (t.1, t.2)) (ρ 𝔇.na⁻¹ w)
      = ρ (𝔇.tau (t.1, t.2) * 𝔇.na⁻¹) w := by rw [map_mul]; rfl
    _ = ρ (𝔇.na⁻¹ * 𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m)) w := by rw [hτ]
    _ = ρ 𝔇.na⁻¹ (ρ (𝔇.tau ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m)) w) := by
          rw [map_mul]; rfl
    _ = ρ 𝔇.na⁻¹ ((wchar (K := K) k κ₁ κ₂
          ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) : k) • w) := by
          rw [hwρ ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m)]
    _ = (wchar (K := K) k κ₁ κ₂
          ((t.2 / t.1) ^ 2 ^ m, (t.1 * t.2) ^ 2 ^ m) : k) • ρ 𝔇.na⁻¹ w := by
          rw [LinearMap.map_smul]
    _ = (wchar (K := K) k (sa m (κ₁, κ₂)).1 (sa m (κ₁, κ₂)).2 (t.1, t.2) : k) • ρ 𝔇.na⁻¹ w := by
          rw [hchar]

private lemma nb_weight {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ)
    (ρ : Representation k Γ W)
    {κ₁ κ₂ : ZMod (2 ^ (2 * m + 1) - 1)} {w : W}
    (hw : w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ₁ κ₂)) :
    ρ (𝔇.φ₁ (suzukiWElt m K)) w ∈
      weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k (-κ₁) κ₂) := by
  rw [mem_weightSpace] at hw ⊢
  have hwρ : ∀ g : Kˣ × Kˣ, ρ (𝔇.tau g) w = (wchar (K := K) k κ₁ κ₂ g : k) • w := hw
  intro t
  change ρ (𝔇.tau (t.1, t.2)) (ρ (𝔇.φ₁ (suzukiWElt m K)) w) =
    (wchar (K := K) k (-κ₁) κ₂ (t.1, t.2) : k) • ρ (𝔇.φ₁ (suzukiWElt m K)) w
  have hDW : szD K m t.1 * suzukiWElt m K = suzukiWElt m K * szD K m t.1⁻¹ := by
    have h := suzukiWElt_D_W (a := m) (K := K) hK t.1
    have h2 := congrArg (fun x => suzukiWElt m K * x) h
    rw [show suzukiWElt m K * (suzukiWElt m K * suzukiDElt m K t.1 * suzukiWElt m K) =
        suzukiDElt m K t.1 * suzukiWElt m K by
          rw [← mul_assoc, ← mul_assoc, suzukiWElt_mul_self, one_mul]] at h2
    exact h2
  have hτ : 𝔇.tau (t.1, t.2) * 𝔇.φ₁ (suzukiWElt m K) =
      𝔇.φ₁ (suzukiWElt m K) * 𝔇.tau (t.1⁻¹, t.2) := by
    calc 𝔇.tau (t.1, t.2) * 𝔇.φ₁ (suzukiWElt m K)
        = 𝔇.φ₁ (szD K m t.1) * 𝔇.φ₂ (szD K m t.2) * 𝔇.φ₁ (suzukiWElt m K) := by
            rw [𝔇.tau_apply]
      _ = 𝔇.φ₁ (szD K m t.1) * (𝔇.φ₁ (suzukiWElt m K) * 𝔇.φ₂ (szD K m t.2)) := by
            rw [mul_assoc, (𝔇.comm (suzukiWElt m K) (szD K m t.2)).symm]
      _ = 𝔇.φ₁ (szD K m t.1 * suzukiWElt m K) * 𝔇.φ₂ (szD K m t.2) := by
            rw [← mul_assoc, ← map_mul]
      _ = 𝔇.φ₁ (suzukiWElt m K * szD K m t.1⁻¹) * 𝔇.φ₂ (szD K m t.2) := by rw [hDW]
      _ = (𝔇.φ₁ (suzukiWElt m K) * 𝔇.φ₁ (szD K m t.1⁻¹)) * 𝔇.φ₂ (szD K m t.2) := by
            rw [map_mul]
      _ = 𝔇.φ₁ (suzukiWElt m K) * (𝔇.φ₁ (szD K m t.1⁻¹) * 𝔇.φ₂ (szD K m t.2)) := by
            rw [mul_assoc]
      _ = 𝔇.φ₁ (suzukiWElt m K) * 𝔇.tau (t.1⁻¹, t.2) := by rw [𝔇.tau_apply]
  have hchar : wchar (K := K) k κ₁ κ₂ (t.1⁻¹, t.2) =
      wchar (K := K) k (-κ₁) κ₂ (t.1, t.2) := by
    rw [wchar_apply, wchar_apply, wchar1_inv (K := K) k hK κ₁ t.1]
  calc ρ (𝔇.tau (t.1, t.2)) (ρ (𝔇.φ₁ (suzukiWElt m K)) w)
      = ρ (𝔇.tau (t.1, t.2) * 𝔇.φ₁ (suzukiWElt m K)) w := by rw [map_mul]; rfl
    _ = ρ (𝔇.φ₁ (suzukiWElt m K) * 𝔇.tau (t.1⁻¹, t.2)) w := by rw [hτ]
    _ = ρ (𝔇.φ₁ (suzukiWElt m K)) (ρ (𝔇.tau (t.1⁻¹, t.2)) w) := by rw [map_mul]; rfl
    _ = ρ (𝔇.φ₁ (suzukiWElt m K))
          ((wchar (K := K) k κ₁ κ₂ (t.1⁻¹, t.2) : k) • w) := by rw [hwρ (t.1⁻¹, t.2)]
    _ = (wchar (K := K) k κ₁ κ₂ (t.1⁻¹, t.2) : k) • ρ (𝔇.φ₁ (suzukiWElt m K)) w := by
          rw [LinearMap.map_smul]
    _ = (wchar (K := K) k (-κ₁) κ₂ (t.1, t.2) : k) • ρ (𝔇.φ₁ (suzukiWElt m K)) w := by
          rw [hchar]

private lemma fixed_of_snd_zero {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ)
    (ρ : Representation k Γ W) {κ₁ : ZMod (2 ^ (2 * m + 1) - 1)} {w : W}
    (hw : w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ₁ 0)) :
    ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) w = w := by
  intro l
  rw [mem_weightSpace] at hw
  have htau : 𝔇.tau (1, l) = 𝔇.φ₂ (szD K m l) := by
    simp only [𝔇.tau_apply, map_one, one_mul]
  have hw1 := hw (1, l)
  simp only [MonoidHom.comp_apply] at hw1
  have hchi : wchar (K := K) k κ₁ 0 (1, l) = 1 := by
    rw [wchar_apply, map_one, wchar1_zero, mul_one]
  rw [hchi] at hw1
  simp only [Units.val_one, one_smul] at hw1
  rw [← htau]
  exact hw1

private lemma fixed_of_ne {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ)
    (ρ : Representation k Γ W)
    {κ₁ κ₂ : ZMod (2 ^ (2 * m + 1) - 1)} {w : W} (hw0 : w ≠ 0)
    (hw : w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ₁ κ₂)) (h : κ₁ = -κ₂) :
    ∃ v : W, v ≠ 0 ∧ ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v = v := by
  refine ⟨ρ 𝔇.na⁻¹ w, invertible (K := K) (W := W) k ρ 𝔇.na⁻¹ hw0, ?_⟩
  have hna := na_weight_aux (K := K) (W := W) k hK 𝔇 ρ hw
  have h2 : (sa m (κ₁, κ₂)).2 = 0 := by
    simp only [sa, Nat.cast_pow]
    rw [h]
    ring
  rw [h2] at hna
  exact fixed_of_snd_zero (K := K) (W := W) k hK 𝔇 ρ hna

private lemma fixed_of_eq {K : Type} [Field K] [CharP K 2]
    [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type}
    [AddCommGroup W] [Module k W] (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ)
    (ρ : Representation k Γ W)
    {κ₁ κ₂ : ZMod (2 ^ (2 * m + 1) - 1)} {w : W} (hw0 : w ≠ 0)
    (hw : w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ₁ κ₂)) (h : κ₁ = κ₂) :
    ∃ v : W, v ≠ 0 ∧ ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v = v := by
  exact fixed_of_ne (K := K) (W := W) k hK 𝔇 ρ (invertible (K := K) (W := W) k ρ (𝔇.φ₁ (suzukiWElt m K)) hw0)
    (nb_weight (K := K) (W := W) k hK 𝔇 ρ hw) (by rw [h])

private lemma exists_fixed_of_weight {K : Type} [Field K]
    [CharP K 2] [Fintype K] {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k]
    {W : Type} [AddCommGroup W] [Module k W] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (𝔇 : SzPairDatum K m Γ) (ρ : Representation k Γ W)
    {κ₁ κ₂ : ZMod (2 ^ (2 * m + 1) - 1)} {w : W} (hw0 : w ≠ 0)
    (hw : w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ₁ κ₂)) (hl : OnLines κ₁ κ₂) :
    ∃ v : W, v ≠ 0 ∧ ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v = v := by
  rcases hl with h | h | h | h
  · exact fixed_of_eq (K := K) (W := W) k hK 𝔇 ρ (invertible (K := K) (W := W) k ρ 𝔇.na⁻¹ hw0)
      (na_weight_aux (K := K) (W := W) k hK 𝔇 ρ hw)
      (by simp only [sa, Nat.cast_pow]; rw [h]; ring)
  · exact ⟨w, hw0, fixed_of_snd_zero (K := K) (W := W) k hK 𝔇 ρ (by simpa [h] using hw)⟩
  · exact fixed_of_eq (K := K) (W := W) k hK 𝔇 ρ hw0 hw h
  · exact fixed_of_ne (K := K) (W := W) k hK 𝔇 ρ hw0 hw h

theorem lines_fixed {K : Type} [Field K] [CharP K 2] [Fintype K]
    {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type} [AddCommGroup W]
    [Module k W] [CharP k 2] (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ)
    (ρ : Representation k Γ W)
    {p : ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1)} (hp : p ∈ 𝔇.wt k ρ)
    (hl : OnLines p.1 p.2) : ∃ v : W, v ≠ 0 ∧ ∀ l : Kˣ, ρ (𝔇.φ₂ (szD K m l)) v = v := by
  change weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k p.1 p.2) ≠ ⊥ at hp
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hp
  exact exists_fixed_of_weight (K := K) (W := W) k hK 𝔇 ρ hw0 hw hl

theorem na_weight {K : Type} [Field K] [CharP K 2] [Fintype K]
    {m : ℕ} {Γ : Type} [Group Γ] (k : Type) [Field k] [Algebra K k] {W : Type} [AddCommGroup W]
    [Module k W] (hK : Nat.card K = 2 ^ (2 * m + 1)) (𝔇 : SzPairDatum K m Γ)
    (ρ : Representation k Γ W)
    {κ : ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1)} {w : W}
    (hw : w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k κ.1 κ.2)) :
    ρ 𝔇.na⁻¹ w ∈ weightSpace (ρ.comp 𝔇.tau) (wchar (K := K) k (sa m κ).1 (sa m κ).2) := by
  exact na_weight_aux (K := K) (W := W) (κ₁ := κ.1) (κ₂ := κ.2) k hK 𝔇 ρ hw

end CFSG.StandardType.ReeB2Fixed
