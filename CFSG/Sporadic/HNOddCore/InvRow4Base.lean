
module

public import CFSG.Sporadic.HNOddCore.InvRow1bBase
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

theorem stabilizer_card_eq
    {K : Subgroup JH} :
    Nat.card (MulAction.stabilizer K x0) = Nat.card (K ⊓ HJ : Subgroup JH) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨g.1.1, Subgroup.mem_inf.2 ⟨g.1.2, (mem_HJ_iff_fix _).2 g.2⟩⟩
      invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩,
        (mem_HJ_iff_fix _).1 (Subgroup.mem_inf.1 g.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_eq_orbit_mul
    {K : Subgroup JH} :
    Nat.card K = (MulAction.orbit K x0).ncard * Nat.card (K ⊓ HJ : Subgroup JH) := by
  rw [← stabilizer_card_eq, ← MulAction.index_stabilizer, mul_comm,
    Subgroup.card_mul_index]

abbrev t4Tab : Array ℕ := pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.t4Word

abbrev x4Tab : Array ℕ :=
  pcomp hnsData.n (seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) InvData.x4Root)
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.x4H)

theorem prep_t4 :
    PRep hnsData.n t4Tab (permJ t4J) := by
  rw [t4J_eq]
  exact prep_hWord (letters_of_natOK nat_parts.2.1)

def c4G (j : ℕ) : JH := hWordJ InvData.c4Words[j]!

def x4J : JH := seedWordJ InvData.x4Root * hWordJ InvData.x4H

def g4 (s : ℕ) : JH := if s < 9 then c4G s else x4J

theorem c4G_mem_HJ (j : ℕ) : c4G j ∈ HJ := hWordJ_mem _

theorem c4_spec :
    InvData.c4Words.size = InvData.c4Nat.size ∧ ∀ j < InvData.c4Words.size,
    plettersOK 17 InvData.c4Words[j]! = true ∧
      PRep 12 (natArr InvData.c4Nat[j]!) (natWord InvData.c4Words[j]!) :=
  natAllOK_spec nat_parts.2.2.2.2.1

theorem t4J_mem_HJ :
    t4J ∈ HJ := t4H.2

theorem nat_t4 :
    PRep 12 (natArr InvData.nat4) (thetaJ ⟨t4J, t4J_mem_HJ⟩ : Perm (Fin 12)) := by
  have e : (⟨t4J, t4J_mem_HJ⟩ : HJ) = t4H := rfl
  rw [e, thetaJ_t4H]
  exact prep_sig4

theorem prep_x4 :
    PRep hnsData.n x4Tab (permJ x4J) := by
  rw [x4J, map_mul]
  exact prep_pcomp (prep_seedWordArr _ (by decide)) (prep_hWord (by decide))

theorem fix_t4_smul
    {g : JH} (hg : g * t4J = t4J * g) {y : X} (hy : jR t4J • y = y) :
    jR t4J • (g • y) = g • y := by
  rw [← jR_smul g, ← mul_smul, ← map_mul, ← hg, map_mul, mul_smul, hy]

abbrev S4 : Subgroup JH := Subgroup.closure (Set.range fun s : Fin s4J.size => g4 s)

end CFSG.Sporadic.HNOddCore
