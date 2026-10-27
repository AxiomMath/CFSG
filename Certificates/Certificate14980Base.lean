
module

public import CFSG.RankThree.PartOne.S11c.HNSevenInputs
public meta import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.NatCheckInputs
import CFSG.RankThree.PartOne.S11c.HNSevenFixBase
import CFSG.Sporadic.HNSchreier.Primitive
import Certificates.Kernel.SporSch.HN.Pt2094
import CFSG.Sporadic.HNSchreier.ChainCheckInputs
import CFSG.Sporadic.HNSchreier.LevelInputs
meta import CFSG.Sporadic.HNSchreier.OrbitCheck
meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
import CFSG.Sporadic.HNSchreier.LocalCheckInputs
meta import CFSG.Sporadic.HNSchreier.PrimCheck
meta import CFSG.Sporadic.HNSchreier.LocalData
meta import CFSG.Sporadic.HNSchreier.MaskCheck
import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
import CFSG.Sporadic.HNSchreier.PrimCheckInputs
meta import Certificates.Data.CFSGNative.Perm.Chain
import CFSG.Sporadic.HNSchreier.VectorData

namespace CertificateChecks.Batch14980

open Equiv Subgroup
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.He.Native
open CFSG.RankThree.PartOne.HNRed CFSG.RankThree.PartOne.HNRed.Native

theorem letters_ok : plettersOK 17 sevenWord = true := by decide +kernel

theorem sevenWord_ok : ∀ l ∈ sevenWord, l ≠ 0 ∧ l.natAbs ≤ 17 := by decide +kernel

theorem nat_pts : ∀ x < 12, sevenWord.foldr (CFSG.KS.TW.GZ CFSG.KS.HNNat.natF CFSG.KS.HNNat.natFI) x =
    (natArr cyc7)[x]! := by
  decide +kernel

theorem nat_ok : sevenNatCheck = true := by
  unfold sevenNatCheck natOK
  rw [letters_ok, Bool.true_and]
  exact CFSG.KS.HNNat.peq_maps fun x hx => by
    rw [CFSG.KS.HNNat.natWord_pt sevenWord_ok hx, nat_pts x hx]

theorem sizes_seven : ∀ j : Fin 12, j ≠ 0 → 7 ∣ Data.subgroupOrbitSizes[j.val]! := by
  decide +kernel

theorem orderOf_u0 : orderOf (hWordJ sevenWord) = 7 := by
  have hn := nat_ok
  unfold sevenNatCheck at hn
  rw [← natStrongArr_eq] at hn
  exact orderOf_coe_of_equiv thetaJ (hWordH sevenWord) (by
    rw [← Subgroup.orderOf_coe, thetaJ_hWordH, natWord_of_natOK prep_sigma7 hn, orderOf_sigma7])

theorem fix_root {g : JH} (hg : g ∈ HJ) (ho : orderOf g = 7) {x : X} (hx : g • x = x) :
    x = x0 := by
  by_contra hne
  have hp : permJ g ∈ HP := (mem_HJ_iff g).1 hg
  have hpo : orderOf (⟨permJ g, hp⟩ : HP) = 7 := by
    rw [Subgroup.orderOf_mk, orderOf_injective permJ permJ_injective, ho]
  have hpx : (⟨permJ g, hp⟩ : HP) ∈ MulAction.stabilizer HP x := by
    rw [MulAction.mem_stabilizer_iff]
    change permJ g x = x
    rw [permJ_apply, hx]
  have h7 : 7 ∣ Nat.card (MulAction.stabilizer HP x) := by
    have := orderOf_dvd_natCard (⟨_, hpx⟩ : MulAction.stabilizer HP x)
    rwa [Subgroup.orderOf_mk, hpo] at this
  have hj : hLab x ≠ 0 := by
    intro h0
    have hx0 := mem_orbit_hLab x
    have h00 := mem_orbit_hLab x0
    rw [hLab_zero] at h00
    rw [h0] at hx0
    have hc : Nat.card (MulAction.orbit HP (repX 0)) = 1 := by rw [card_orbit]; rfl
    have hs := (Nat.card_eq_one_iff_unique.1 hc).1
    exact hne (congrArg Subtype.val (Subsingleton.elim (⟨x, hx0⟩ : MulAction.orbit HP (repX 0))
      ⟨x0, h00⟩))
  have horb : MulAction.orbit HP x = MulAction.orbit HP (repX (hLab x)) :=
    MulAction.orbit_eq_iff.2 (mem_orbit_hLab x)
  have hco : 7 ∣ Nat.card (MulAction.orbit HP x) := by
    rw [horb, card_orbit]
    exact sizes_seven _ hj
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer HP x)
  rw [MulAction.index_stabilizer, rhoH_injective_card.2] at hcard
  have h49 : 7 * 7 ∣ Nat.factorial 12 / 2 := hcard ▸ Nat.mul_dvd_mul h7 hco
  norm_num [Nat.factorial] at h49

theorem seven_ok : sevenChecksO (hnsData.orbit ()) = true := by
  unfold sevenChecksO sevenChecksR
  rw [← hRegs_eq, ← hStrongArr_eq]
  unfold sevenChecksH
  rw [letters_ok, Bool.true_and, beq_iff_eq]
  refine KernelSporSch.HNPt2094.fixedSet_eq (by rw [hns_n]; norm_num) fun i hi => ?_
  have hp := prep_hWord letters_ok ⟨i, hi⟩
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [List.mem_toArray, List.mem_singleton, forall_eq, beq_iff_eq]
  rw [hp, permJ_apply]
  constructor
  · intro h
    exact congrArg Fin.val (fix_root (hWordJ_mem sevenWord) orderOf_u0 (Fin.ext h))
  · rintro rfl
    exact congrArg Fin.val ((mem_HJ_iff_fix _).1 (hWordJ_mem sevenWord))

end CertificateChecks.Batch14980

