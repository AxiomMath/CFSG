module

public import CFSG.RankThree.PartTwo.Sec21.FF81SL32FixEx
public import CFSG.RankThree.PartTwo.Sec21.FF81SL32FixLayer
import Mathlib.Data.SetLike.Fintype

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix

open Subgroup

theorem sl32Fix_core {X : Type*} [Group X] [Finite X] (K U W : Subgroup X) (φ : K ≃* GL3)
    (hU2 : IsPGroup 2 U) (hWU : W ≤ U) (hWn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W)
    (hKU : ∀ x ∈ K, ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hKW : ∀ x ∈ K, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    {y : X} (hy : y ∈ K) (hy3 : orderOf y = 3) :
    Nat.card U * Nat.card ↥(W ⊓ centralizer ({y} : Set X)) ^ 4 ≤
      Nat.card W * Nat.card ↥(U ⊓ centralizer ({y} : Set X)) ^ 4 := by
  classical
  have hφy : orderOf (φ ⟨y, hy⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy3]
  obtain ⟨c, hc⟩ := exists_conj_y0 hφy
  let ψ : GL3 ≃* K := (MulAut.conj c).trans φ.symm
  have hψ : ψ y0 = ⟨y, hy⟩ := by
    show φ.symm (c * y0 * c⁻¹) = _
    rw [hc]
    exact φ.symm_apply_apply _
  have hKU' : ∀ x ∈ K, ∀ u ∈ U, x⁻¹ * u * x ∈ U := fun x hx u hu => by
    have h := hKU x⁻¹ (K.inv_mem hx) u hu
    simpa using h
  have main : ∀ W' : Subgroup X, W' ≤ U → (∀ u ∈ U, ∀ w ∈ W', u * w * u⁻¹ ∈ W') →
      (∀ x ∈ K, ∀ w ∈ W', x * w * x⁻¹ ∈ W') →
      Nat.card U * Nat.card ↥(W' ⊓ centralizer ({y} : Set X)) ^ 4 ≤
        Nat.card W' * Nat.card ↥(U ⊓ centralizer ({y} : Set X)) ^ 4 := by
    intro W'
    induction W' using WellFoundedGT.induction with
    | _ W' ih =>
    intro hle hn hk
    by_cases hWU' : W' = U
    · subst hWU'
      exact le_refl _
    · have hlt : W' < U := lt_of_le_of_ne hle hWU'
      set M := omegaZ U W' hn with hM
      have hMU : M ≤ U := omegaZ_le hn
      have hWM : W' ≤ M := le_omegaZ hn hle
      have hMW : W' < M := by
        refine lt_of_le_of_ne hWM fun h => ?_
        obtain ⟨u, hu, huW⟩ := exists_mem_omegaZ_not_mem hn hU2 hlt
        exact huW (h ▸ hu)
      haveI : (W'.subgroupOf M).Normal :=
        ⟨fun n hn' g => hn g.1 (hMU g.2) n hn'⟩
      have hKM : ∀ x ∈ K, ∀ m ∈ M, x * m * x⁻¹ ∈ M := fun x hx m hm =>
        omegaZ_conj_K hn (hKU x hx) (hKU' x hx) (hk x hx) hm
      have hA := layer_bound hWM hKM hk
        (fun a ha b hb => omegaZ_comm hn ha (hMU hb)) (fun a ha => omegaZ_sq hn ha)
        (hU2.to_le hle) ψ.toMonoidHom hy hy3 hψ
      have hB := ih M hMW hMU (fun u hu m hm => omegaZ_conj_U hn hu hm) hKM
      haveI : Nonempty ↥(M ⊓ centralizer ({y} : Set X)) := ⟨1⟩
      have hpos : 0 < Nat.card ↥(M ⊓ centralizer ({y} : Set X)) ^ 4 :=
        pow_pos Nat.card_pos 4
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc Nat.card U * Nat.card ↥(W' ⊓ centralizer ({y} : Set X)) ^ 4 *
            Nat.card ↥(M ⊓ centralizer ({y} : Set X)) ^ 4
          = (Nat.card U * Nat.card ↥(M ⊓ centralizer ({y} : Set X)) ^ 4) *
            Nat.card ↥(W' ⊓ centralizer ({y} : Set X)) ^ 4 := by ring
        _ ≤ (Nat.card M * Nat.card ↥(U ⊓ centralizer ({y} : Set X)) ^ 4) *
            Nat.card ↥(W' ⊓ centralizer ({y} : Set X)) ^ 4 := Nat.mul_le_mul_right _ hB
        _ = (Nat.card M * Nat.card ↥(W' ⊓ centralizer ({y} : Set X)) ^ 4) *
            Nat.card ↥(U ⊓ centralizer ({y} : Set X)) ^ 4 := by ring
        _ ≤ (Nat.card W' * Nat.card ↥(M ⊓ centralizer ({y} : Set X)) ^ 4) *
            Nat.card ↥(U ⊓ centralizer ({y} : Set X)) ^ 4 := Nat.mul_le_mul_right _ hA
        _ = Nat.card W' * Nat.card ↥(U ⊓ centralizer ({y} : Set X)) ^ 4 *
            Nat.card ↥(M ⊓ centralizer ({y} : Set X)) ^ 4 := by ring
  exact main W hWU hWn hKW

end CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix
