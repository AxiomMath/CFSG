
module

public import CFSG.YGroups.Model233F.RawChain
public import CFSG.YGroups.CosetAction233Base
public import Certificates.Data.CFSGNative.YGroups.Model233FData
public import CFSG.YGroups.Model233FInputs
public import Certificates.Certificate10101
public meta import CFSG.YGroups.Defs
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.Model233FData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Certificates.CosetTablePresented
public import CFSG.YGroups.Ctil233
public meta import Mathlib
public import Mathlib

@[expose] public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Certificates.CosetEnumeration (evalWord)

theorem y233F_check :
    y233FArrays.size = 9 ∧ ModelNative.permsOK 3510 y233FArrays = true ∧
    ModelNative.relatorsOK 3510 y233FArrays (yRels 2 3 3) = true ∧
    Nat.card (arrClosure 3510 y233FArrays) = 64561751654400 :=
  Certificates.certificate10101.1

theorem y233C_check :
    y233CArrays.size = 8 ∧ Nat.card (arrClosure 3510 y233CArrays) = 92897280 :=
  Certificates.certificate10101.2

noncomputable def y233FGen (c : ℕ) : Equiv.Perm (Fin 3510) := arrGen 3510 y233FArrays c

theorem y233F_relators :
    ∀ w ∈ yRels 2 3 3, evalWord y233FGen w = 1 :=
  evalWord_arrGen_eq_one y233F_check.2.1 y233F_check.2.2.1

theorem y233FGen_eq
    {c : ℕ} (hc : c < 9) : y233FGen c = permOfArr 3510 y233FArrays[c]! := by
  have hc' : c < y233FArrays.size := by rw [y233F_check.1]; exact hc
  rw [y233FGen, arrGen, ite_eq_left hc']

noncomputable def rho233F : YGroup 2 3 3 →* Equiv.Perm (Fin 3510) :=
  yModelHom y233FGen y233F_relators

theorem rho233F_yGen
    {c : ℕ} (hc : c < 9) : rho233F (yGen 2 3 3 c) = y233FGen c :=
  yModelHom_yGen hc

theorem rho233F_rep {c : ℕ} (hc : c < 9) :
    Rep 3510 y233FArrays[c]! (rho233F (yGen 2 3 3 c)) := by
  rw [rho233F_yGen hc]
  have h := rep_letterOf y233F_check.2.1 c
  rwa [ModelNative.letterOf, ite_eq_left (by have := y233F_check.1; omega)] at h

theorem range_rho233F :
    rho233F.range = arrClosure 3510 y233FArrays := by
  rw [rho233F, range_yModelHom, show y233FGen = arrGen 3510 y233FArrays from rfl,
    ← show y233FArrays.size = ngen 2 3 3 from y233F_check.1, arrGen_image_eq]
  rfl

theorem card_range_rho233F :
    Nat.card rho233F.range = 64561751654400 := by
  rw [range_rho233F]
  exact y233F_check.2.2.2

def y233CLetter (k : ℕ) : ℕ := if k < 2 then k else k + 1

theorem y233CArrays_getElem {k : ℕ} (hk : k < 8) :
    y233CArrays[k]! = y233FArrays[y233CLetter k]! := by
  interval_cases k <;> rfl

theorem map_ctil_rho233F :
    Ctil.map rho233F = arrClosure 3510 y233CArrays := by
  rw [Ctil, MonoidHom.map_closure, Set.image_image]
  unfold arrClosure
  congr 1
  ext g
  rw [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, ⟨hc, hc2⟩, rfl⟩
    have hk : (if c < 2 then c else c - 1) < 8 := by split_ifs <;> omega
    have hl : y233CLetter (if c < 2 then c else c - 1) = c := by
      unfold y233CLetter
      split_ifs <;> omega
    refine ⟨if c < 2 then c else c - 1, by rw [y233C_check.1]; exact hk, ?_⟩
    show permOfArr 3510 y233CArrays[if c < 2 then c else c - 1]! = rho233F (yGen 2 3 3 c)
    rw [y233CArrays_getElem hk, hl, rho233F_yGen hc, y233FGen_eq hc]
  · rintro ⟨k, hk, rfl⟩
    have hk8 : k < 8 := by rw [y233C_check.1] at hk; exact hk
    have h9 : y233CLetter k < 9 := by
      unfold y233CLetter
      split_ifs <;> omega
    have h2 : y233CLetter k ≠ 2 := by
      unfold y233CLetter
      split_ifs <;> omega
    refine ⟨y233CLetter k, ⟨h9, h2⟩, ?_⟩
    show rho233F (yGen 2 3 3 (y233CLetter k)) = permOfArr 3510 y233CArrays[k]!
    rw [rho233F_yGen h9, y233FGen_eq h9, y233CArrays_getElem hk8]

theorem card_map_ctil_rho233F :
    Nat.card (Ctil.map rho233F) = 92897280 := by
  rw [map_ctil_rho233F]
  exact y233C_check.2

theorem ker_rho233F_le_ctil_of_index
    (hidx : Ctil.index = 694980) : rho233F.ker ≤ Ctil := by
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
  have hle : Ctil ≤ D := le_sup_left
  have h6 := Subgroup.relIndex_mul_index hle
  rw [hidx, hDidx] at h6
  have h7 : Ctil.relIndex D = 1 := by omega
  exact le_sup_right.trans (Subgroup.relIndex_eq_one.1 h7)

end CFSG.YGroups
