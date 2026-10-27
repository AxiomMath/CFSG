module

public import CFSG.RankThree.GF2n.Stroth80.Sec717CorBHypProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveBridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

section Frame

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

private theorem conjSubgroup_L_eq_of_mem_normalizerV (F : MoveFrame B φ V L Nb Rb Tt q) {k : X}
    (hk : k ∈ normalizer (V : Set X)) : conjSubgroup k L = L := by
  have hk' : k⁻¹ ∈ normalizer (V : Set X) := inv_mem hk
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro hx
    have := F.L_norm k hk _ hx
    simpa [mul_assoc] using this
  · intro hx
    simpa using F.L_norm k⁻¹ hk' x hx

theorem MoveFrame.conjSubgroup_eq_of_le_centralizer (F : MoveFrame B φ V L Nb Rb Tt q)
    (hNorm : ∀ z ∈ V, z ≠ 1 → ∀ h : X, h * z * h⁻¹ ∈ L → h * z * h⁻¹ ∉ V →
      conjSubgroup h L = L)
    {z : X} (hz : z ∈ V) (hz1 : z ≠ 1) {g : X}
    (hg : conjSubgroup g L ≤ centralizer {z}) : conjSubgroup g L = L := by
  set w := g⁻¹ * z * g with hw
  have hwL : ∀ l ∈ L, l * w = w * l := by
    intro l hl
    have h1 : g * l * g⁻¹ ∈ conjSubgroup g L :=
      mem_conjSubgroup.mpr (by simpa [mul_assoc] using hl)
    have h2 : g * l * g⁻¹ * z = z * (g * l * g⁻¹) := mem_centralizer_singleton_iff.mp (hg h1)
    calc l * w = g⁻¹ * (g * l * g⁻¹ * z) * g := by rw [hw]; group
      _ = g⁻¹ * (z * (g * l * g⁻¹)) * g := by rw [h2]
      _ = w * l := by rw [hw]; group
  have hwV : ∀ a ∈ V, w * a = a * w := fun a ha => (hwL a (F.V_le_L ha)).symm
  have hwN : w ∈ normalizer (V : Set X) := by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [hwV a ha, mul_inv_cancel_right]
      exact ha
    · intro ha
      have e : a = w⁻¹ * (w * a * w⁻¹) * w := by group
      rw [e, mul_assoc, ← hwV _ ha, inv_mul_cancel_left]
      exact ha
  have hw2 : w ^ 2 = 1 := by
    rw [hw, pow_two]
    have hzz : z * z = 1 := F.V_sq z hz
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group
  have hw2g : IsPGroup 2 (zpowers w) := by
    have hd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2]; rfl)
  have hwR : w ∈ Rb := F.two_elements w hwN hwV hw2g
  have hwLm : w ∈ L := F.CL w hwR fun l hl => (hwL l hl).symm
  by_cases hwVm : w ∈ V
  · have hgN : g⁻¹ ∈ normalizer (V : Set X) := by
      refine F.ti g⁻¹ z hz hz1 ?_
      simpa [hw] using hwVm
    exact conjSubgroup_L_eq_of_mem_normalizerV F (by simpa using inv_mem hgN)
  · have h1 := hNorm z hz hz1 g⁻¹ (by simpa [hw] using hwLm) (by simpa [hw] using hwVm)
    have h2 : g⁻¹ ∈ normalizer (L : Set X) := mem_normalizer_iff_conjSubgroup_eq.mpr h1
    exact mem_normalizer_iff_conjSubgroup_eq.mp (by simpa using inv_mem h2)

end Frame


theorem sec717WC_of_frame (hF : Sec717MoveFrameStatement) (hNorm : Sec717NormalizeStatement) :
    Sec717WCStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK z hz hz1 g hg
  obtain ⟨K, _, E, _, _, _, B', φ, Tt, q, F⟩ :=
    hF G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn
  exact F.conjSubgroup_eq_of_le_centralizer
    (fun z' hz' hz1' h hm hnm =>
      hNorm G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn hex hLK z' hz' hz1' h hm hnm)
    hz hz1 hg

end CFSG.RankThree.GF2n.Stroth80
