module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpContBasic

public section

open Polynomial Module Multiplicative
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.Classical (spForm spLin spLin_injective spEnd)

namespace CFSG.StandardType

namespace SpNsCont

open CoordSpNs

section Swap

variable {F : Type} [Field F] {D : Type} [AddCommGroup D] [Module F D] {s : ℕ} {κ : Type}

@[expose] def swapTw (i j : Fin s) (Ti Tj : D ≃ₗ[F] D) : Fin s → (D ≃ₗ[F] D) :=
  fun k => if k = i then Ti else if k = j then Tj else LinearEquiv.refl F D

theorem swapTw_left (i j : Fin s) (Ti Tj : D ≃ₗ[F] D) : swapTw i j Ti Tj i = Ti := by
  simp [swapTw]

theorem swapTw_right {i j : Fin s} (hij : i ≠ j) (Ti Tj : D ≃ₗ[F] D) :
    swapTw i j Ti Tj j = Tj := by
  simp [swapTw, Ne.symm hij]

theorem swapTw_ne {i j k : Fin s} (hki : k ≠ i) (hkj : k ≠ j) (Ti Tj : D ≃ₗ[F] D) :
    swapTw i j Ti Tj k = LinearEquiv.refl F D := by
  simp [swapTw, hki, hkj]

@[expose] def swapMono (i j : Fin s) (Ti Tj : D ≃ₗ[F] D) :
    ((Fin s → D) × (κ → F)) ≃ₗ[F] ((Fin s → D) × (κ → F)) :=
  SpNS.monoEquiv (Equiv.swap i j) (swapTw i j Ti Tj)

theorem swapMono_apply (i j : Fin s) (Ti Tj : D ≃ₗ[F] D) (d : Fin s → D) (w : κ → F) :
    swapMono (κ := κ) i j Ti Tj (d, w) =
      (fun k => swapTw i j Ti Tj k (d (Equiv.swap i j k)), w) := rfl

theorem swapMono_single {i j : Fin s} (hij : i ≠ j) (Ti Tj : D ≃ₗ[F] D) (z : D) :
    swapMono (κ := κ) i j Ti Tj (Pi.single i z, 0) = (Pi.single j (Tj z), 0) := by
  rw [swapMono_apply]
  refine Prod.ext (funext fun k => ?_) rfl
  dsimp only
  by_cases hkj : k = j
  · rw [hkj, swapTw_right hij, Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_same]
  · have hki : Equiv.swap i j k ≠ i := by
      rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      exact hkj
    rw [Pi.single_eq_of_ne hki, map_zero, Pi.single_eq_of_ne hkj]

theorem swapMono_fix (i j : Fin s) (Ti Tj : D ≃ₗ[F] D) {d : Fin s → D} (hi : d i = 0)
    (hj : d j = 0) (w : κ → F) : swapMono (κ := κ) i j Ti Tj (d, w) = (d, w) := by
  rw [swapMono_apply]
  refine Prod.ext (funext fun k => ?_) rfl
  dsimp only
  by_cases hki : k = i
  · rw [hki, swapTw_left, Equiv.swap_apply_left, hj, map_zero, hi]
  · by_cases hkj : k = j
    · have hij : i ≠ j := fun h => hki (hkj.trans h.symm)
      rw [hkj, swapTw_right hij, Equiv.swap_apply_right, hi, map_zero, hj]
    · rw [swapTw_ne hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
      rfl

variable {n : ℕ} {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
  {ω : LinearMap.BilinForm F D}
  (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
    ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))

include hdec in
theorem swapMono_isom (i j : Fin s) {Ti Tj : D ≃ₗ[F] D} (hTi : ∀ u v, ω (Ti u) (Ti v) = ω u v)
    (hTj : ∀ u v, ω (Tj u) (Tj v) = ω u v) (x y : (Fin s → D) × (κ → F)) :
    spForm n F (Φ (swapMono i j Ti Tj x)) (Φ (swapMono i j Ti Tj y)) =
      spForm n F (Φ x) (Φ y) :=
  SpNS.monoEquiv_isom hdec _ (fun k u v => by
    unfold swapTw
    split_ifs
    · exact hTi u v
    · exact hTj u v
    · rfl) x y

variable {p : ℕ} {c : D ≃ₗ[F] D}

theorem swapMono_torD {i j : Fin s} {Ti Tj : D ≃ₗ[F] D} {a b : ZMod p}
    (hTi : ∀ (m : ZMod p) (z : D), Ti ((c ^ (a * m).val) z) = (c ^ m.val) (Ti z))
    (hTj : ∀ (m : ZMod p) (z : D), Tj ((c ^ (b * m).val) z) = (c ^ m.val) (Tj z))
    {β : Fin s → ZMod p} (hβa : β j = a * β i) (hβb : β i = b * β j)
    (y : (Fin s → D) × (κ → F)) :
    swapMono i j Ti Tj (torD c β y) = torD c β (swapMono i j Ti Tj y) := by
  obtain ⟨d, w⟩ := y
  rw [torD_apply, swapMono_apply, swapMono_apply, torD_apply]
  refine Prod.ext (funext fun k => ?_) rfl
  dsimp only
  by_cases hki : k = i
  · rw [hki, swapTw_left, Equiv.swap_apply_left, hβa, hTi]
  · by_cases hkj : k = j
    · have hij : i ≠ j := fun h => hki (hkj.trans h.symm)
      rw [hkj, swapTw_right hij, Equiv.swap_apply_right, hβb, hTj]
    · rw [swapTw_ne hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
      rfl

theorem swapMono_torD_single {i j : Fin s} (hij : i ≠ j) {Ti Tj : D ≃ₗ[F] D} {b b' : ZMod p}
    (hTj : ∀ (m : ZMod p) (z : D), Tj ((c ^ (b * m).val) z) = (c ^ m.val) (Tj z))
    (hbb : b * b' = 1) (y : (Fin s → D) × (κ → F)) :
    swapMono i j Ti Tj (torD c (Pi.single i (1 : ZMod p)) y) =
      torD c (Pi.single j b') (swapMono i j Ti Tj y) := by
  obtain ⟨d, w⟩ := y
  rw [torD_apply, swapMono_apply, swapMono_apply, torD_apply]
  refine Prod.ext (funext fun k => ?_) rfl
  dsimp only
  by_cases hkj : k = j
  · rw [hkj, swapTw_right hij, Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_same,
      ← hTj, hbb]
  · have hki : Equiv.swap i j k ≠ i := by
      rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      exact hkj
    rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, ZMod.val_zero, pow_zero]
    rfl

variable [NeZero p] (hc : c ^ p = 1) (hcω : ∀ x y, ω (c x) (c y) = ω x y)

theorem exists_swap {i j : Fin s} (hij : i ≠ j) {a b : (ZMod p)ˣ} (ha : a ∈ twistGroup ω c hc)
    (hb : b ∈ twistGroup ω c hc) {β : Fin s → ZMod p} (hβa : β j = a * β i)
    (hβb : β i = b * β j) :
    ∃ (Y : StatedSp n F) (T : D ≃ₗ[F] D),
      Y * torElt hc hdec hcω β = torElt hc hdec hcω β * Y ∧
      Y * torElt hc hdec hcω (Pi.single i (1 : ZMod p)) =
        torElt hc hdec hcω (Pi.single j ((b⁻¹ : (ZMod p)ˣ) : ZMod p)) * Y ∧
      (∀ z : D, frameEnd Φ Y (Pi.single i z, 0) = (Pi.single j (T z), 0)) ∧
      ∀ y : (Fin s → D) × (κ → F), y.1 i = 0 → y.1 j = 0 → frameEnd Φ Y y = y := by
  obtain ⟨Ti, hTi⟩ := mem_twistGroup.mp ha
  obtain ⟨Tj, hTj⟩ := mem_twistGroup.mp hb
  have hM := swapMono_isom hdec i j hTi.1 hTj.1
  refine ⟨frameSp Φ (swapMono i j Ti Tj) hM, Tj, eq_of_frameEnd (Φ := Φ) fun y => ?_,
    eq_of_frameEnd (Φ := Φ) fun y => ?_, fun z => ?_, fun y hi hj => ?_⟩
  · rw [frameEnd_mul, frameEnd_mul, frameEnd_frameSp, frameEnd_frameSp, frameEnd_torElt,
      frameEnd_torElt]
    exact swapMono_torD (hTi.apply_pow hc) (hTj.apply_pow hc) hβa hβb y
  · rw [frameEnd_mul, frameEnd_mul, frameEnd_frameSp, frameEnd_frameSp, frameEnd_torElt,
      frameEnd_torElt]
    exact swapMono_torD_single hij (hTj.apply_pow hc)
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) y
  · rw [frameEnd_frameSp]
    exact swapMono_single hij Ti Tj z
  · rw [frameEnd_frameSp]
    obtain ⟨d, w⟩ := y
    exact swapMono_fix i j Ti Tj hi hj w

end Swap

end SpNsCont

end CFSG.StandardType
