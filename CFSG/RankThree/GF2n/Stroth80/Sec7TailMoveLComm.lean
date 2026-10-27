module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrameAPI

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] [Finite X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.fix_Tt_of_mem_L (F : MoveFrame B φ V L Nb Rb Tt q) (s g : X) (hs : s ∈ V)
    (hs1 : s ≠ 1) (ht : g * s * g⁻¹ ∈ L) {l : X} (hl : l ∈ L) {w : E} (hw : w ∈ Tt g) :
    φ l w = w := by
  rw [← F.Tt_range g s hs hs1, LinearMap.mem_range] at hw
  obtain ⟨z, rfl⟩ := hw
  have h := F.quad l hl (g * s * g⁻¹) ht z
  rw [opm_apply (φ l)] at h
  exact sub_eq_zero.mp h

theorem MoveFrame.L_comm_Vg (F : MoveFrame B φ V L Nb Rb Tt q) (s g : X) (hs : s ∈ V)
    (hs1 : s ≠ 1) (ht : g * s * g⁻¹ ∈ L) (htV : g * s * g⁻¹ ∉ V) :
    (∀ l ∈ L, l ∈ normalizer ((conjSubgroup g V : Subgroup X) : Set X)) ∧
      (∀ l ∈ L, ∀ v ∈ conjSubgroup g V, l * v = v * l) := by
  have htc : g * s * g⁻¹ ∈ conjSubgroup g V := mem_conjSubgroup_iff'.mpr ⟨s, hs, rfl⟩
  have ht1 : g * s * g⁻¹ ≠ 1 := by
    intro h
    apply hs1
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by simp
  have hN : ∀ l ∈ L, l ∈ normalizer ((conjSubgroup g V : Subgroup X) : Set X) := by
    intro l hl
    refine F.ti_conj g l htc ht1 ?_
    rw [F.L_comm l hl _ ht, mul_inv_cancel_right]
    exact htc
  refine ⟨hN, ?_⟩
  intro l hl v hv
  obtain ⟨a, ha, rfl⟩ := mem_conjSubgroup_iff'.mp hv
  by_cases ha1 : a = 1
  · subst ha1
    simp
  · have hfix : ∀ w ∈ Tt g, φ l w = w := fun w hw =>
      F.fix_Tt_of_mem_L s g hs hs1 ht hl hw
    have hc : φ l * φ (g * a * g⁻¹) = φ (g * a * g⁻¹) * φ l :=
      mul_comm_of_fixes B (φ l) (φ (g * a * g⁻¹)) (F.isom l) (Tt g) hfix
        (le_of_eq (F.Tt_range g a ha ha1)) (le_of_eq (F.ker_opm_conj g ha ha1).symm)
    apply F.inj
    rw [map_mul φ l (g * a * g⁻¹), map_mul φ (g * a * g⁻¹) l]
    exact hc

theorem MoveFrame.L_le_Nbg (F : MoveFrame B φ V L Nb Rb Tt q) (s g : X) (hs : s ∈ V)
    (hs1 : s ≠ 1) (ht : g * s * g⁻¹ ∈ L) (htV : g * s * g⁻¹ ∉ V)
    (hNg : ∀ l ∈ L, l ∈ normalizer ((conjSubgroup g V : Subgroup X) : Set X))
    (hcomm : ∀ l ∈ L, ∀ v ∈ conjSubgroup g V, l * v = v * l) :
    ∀ l ∈ L, l ∈ conjSubgroup g Nb := by
  intro l hl
  have hk1 : g⁻¹ * l * g ∈ normalizer (V : Set X) := mem_normalizer_conjSubgroup_iff.mp (hNg l hl)
  have hka : ∀ a ∈ V, g⁻¹ * l * g * a = a * (g⁻¹ * l * g) := by
    intro a ha
    have hc := hcomm l hl (g * a * g⁻¹) (mem_conjSubgroup_iff'.mpr ⟨a, ha, rfl⟩)
    calc g⁻¹ * l * g * a = g⁻¹ * (l * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * l) * g := by rw [hc]
      _ = a * (g⁻¹ * l * g) := by group
  have hlNb : l ∈ Nb := F.L_le_Nb hl
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (⟨l, hlNb⟩ : Nb) ^ 2 ^ n = 1 := F.Nb_pgroup _
  have hln : l ^ 2 ^ n = 1 := by
    have h := congrArg Subtype.val hn
    simpa using h
  have hkpow : (g⁻¹ * l * g) ^ 2 ^ n = 1 := by
    have h := conj_pow (a := g⁻¹) (b := l) (i := 2 ^ n)
    rw [inv_inv] at h
    rw [h, hln]
    simp
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hkpow)
  have hkp : IsPGroup 2 (zpowers (g⁻¹ * l * g)) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hkR : g⁻¹ * l * g ∈ Rb := F.two_elements _ hk1 hka hkp
  have hfix : ∀ w ∈ Tt 1, φ (g⁻¹ * l * g) w = w := by
    intro w hw
    have hgw : φ g w ∈ Tt g := by
      rw [F.Tt_eq_map g]
      exact Submodule.mem_map_of_mem hw
    have hlg : φ l (φ g w) = φ g w := F.fix_Tt_of_mem_L s g hs hs1 ht hl hgw
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hlg,
      phi_inv_apply_phi φ g w]
  have hkNb : g⁻¹ * l * g ∈ Nb := F.Rb_fix_Nb _ hkR hfix
  exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr hkNb

end CFSG.RankThree.GF2n.Stroth80
