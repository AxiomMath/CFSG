
module


public import CFSG.YGroups.Ctil233
public import CFSG.Certificates.Kernel.CosetBounds
import Certificates.Kernel.YChain.Step
import Certificates.Kernel.YChain.Tables.YCt233
import CFSG.YGroups.Model233FBase

public section

namespace Certificates

open CFSG.YGroups CFSG.Certificates.KB CertificateChecks.KernelYChain

open CFSG.YGroups

open CFSG.YGroups CFSG.Certificates.KB CertificateChecks.KernelYChain

theorem wordSub_ctil : wordSub (yGen 2 3 3)
    (([0, 1, 3, 4, 5, 6, 7, 8] : List ℕ).map fun c => [(c, true)]) = Ctil := by
  rw [wordSub, Ctil]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨c, ?_, by simp [sword]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    omega
  · rintro ⟨c, ⟨hc, hc2⟩, rfl⟩
    refine ⟨_, ⟨c, ?_, rfl⟩, by simp [sword]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

theorem ctil_index_le : Ctil.FiniteIndex ∧ Ctil.index ≤ 694980 := by
  have t := YCt233.t1
  unfold CFSG.KBRoute.YCt233.T1.ok at t
  have hw : CFSG.KBRoute.YCt233.T1.words =
      ([0, 1, 3, 4, 5, 6, 7, 8] : List ℕ).map fun c => [(c, true)] := by decide +kernel
  have h := index_le_of_table (p := 2) (q := 3) (r := 3) t (by decide +kernel) (by decide)
    CFSG.KBRoute.YCt233.top
  rw [hw, wordSub_ctil] at h
  exact h

theorem ctil_index_ge [Ctil.FiniteIndex] : 694980 ≤ Ctil.index := by
  set D := Ctil ⊔ rho233F.ker with hD
  have h1 := (Ctil.map rho233F).card_mul_index
  have h2 := rho233F.range.card_mul_index
  have h3 := Ctil.index_map rho233F
  rw [card_map_ctil_rho233F] at h1
  rw [card_range_rho233F] at h2
  have hR : rho233F.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hDidx : D.index = 694980 := by
    have h4 : (92897280 * D.index) * rho233F.range.index =
        64561751654400 * rho233F.range.index := by
      calc (92897280 * D.index) * rho233F.range.index
          = 92897280 * (D.index * rho233F.range.index) := by ring
        _ = 92897280 * (Ctil.map rho233F).index := by rw [h3]
        _ = Nat.card (Equiv.Perm (Fin 3510)) := h1
        _ = 64561751654400 * rho233F.range.index := h2.symm
    have h5 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hR) h4
    omega
  have h6 : D.index ≤ Ctil.index := Subgroup.index_antitone (le_sup_left : Ctil ≤ D)
  rw [hDidx] at h6
  exact h6

theorem certificate10095 : Ctil.index = 694980 := by
  obtain ⟨hfi, hle⟩ := ctil_index_le
  exact le_antisymm hle ctil_index_ge


end Certificates
