
module

public import CFSG.Sporadic.HNOddCore.InvRow1bBase

public import CFSG.Sporadic.HNOddCore.InvRow1
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.SCheckInputs
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

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem thetaJ_mem_Z01
    {g : JH} (hg : g ∈ CJ cR) :
    (thetaJ ⟨g, CJc_le_HJ hg⟩ : Perm (Fin 12)) ∈ Z01 :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    (thetaJ_comm_of_comm (CJc_le_HJ hg) (mem_CJ.1 hg)), (thetaJ ⟨g, CJc_le_HJ hg⟩).2⟩

theorem card_K1 :
    Nat.card K1 = 3628800 := by
  rw [card_closure_eq_nat (fun s : Fin InvData.s1Perms.size => c1G s) (fun s => c1G_mem_HJ s)]
  have hO : ∀ k < (natArrs InvData.c1Nat).size,
      PRep 12 (natArrs InvData.c1Nat)[k]! (thetaJ ⟨c1G k, c1G_mem_HJ k⟩ : Perm (Fin 12)) := by
    intro k hk
    have hk' : k < 9 := by simpa [natArrs, c1Nat_size] using hk
    have := nat_c1G hk'
    rwa [natArrs, getElem!_pos _ k (by simpa [natArrs] using hk), Array.getElem_map,
      ← getElem!_pos InvData.c1Nat k (by rw [c1Nat_size]; exact hk')]
  have h1 := arrGen_eq hO
  have h2 : Set.range (fun s : Fin InvData.s1Perms.size =>
      (thetaJ ⟨c1G s, c1G_mem_HJ s⟩ : Perm (Fin 12))) =
      Set.range (fun k : Fin (natArrs InvData.c1Nat).size =>
        (thetaJ ⟨c1G k, c1G_mem_HJ k⟩ : Perm (Fin 12))) := by
    rw [range_fin_eq (fun k => (thetaJ ⟨c1G k, c1G_mem_HJ k⟩ : Perm (Fin 12))),
      range_fin_eq (fun k => (thetaJ ⟨c1G k, c1G_mem_HJ k⟩ : Perm (Fin 12)))]
    congr 2
    simp [natArrs, c1Nat_size, row1_parts.2.2.1]
  rw [h2, ← h1]
  have hc := natChain_cert
  unfold natChainChecks at hc
  simp only [Bool.and_eq_true] at hc
  rw [card_arrGen_of_chainCheck (by norm_num) (List.nodup_finRange 12) hc.1.1.1]
  decide

theorem K1_eq :
    K1 = CJ cR := by
  apply Subgroup.eq_of_le_of_card_ge K1_le_CJ
  rw [card_K1, ← card_altCentralizer_swap01]
  exact card_le_of_thetaJ CJc_le_HJ (fun g hg => thetaJ_mem_Z01 hg)

theorem card_CJc :
    Nat.card (CJ cR) = 3628800 := by rw [← K1_eq, card_K1]

@[expose] def thetaZ01 :
    CJ cR →* Z01 where
  toFun g := ⟨thetaJ ⟨g, CJc_le_HJ g.2⟩, thetaJ_mem_Z01 g.2⟩
  map_one' := Subtype.ext (by
    show (thetaJ ⟨1, _⟩ : Perm (Fin 12)) = 1
    exact thetaJ_one)
  map_mul' a b := Subtype.ext (by
    show (thetaJ ⟨(a : JH) * b, _⟩ : Perm (Fin 12)) = thetaJ ⟨a, _⟩ * thetaJ ⟨b, _⟩
    exact thetaJ_mul a b _ _)

theorem thetaZ01_injective :
    Function.Injective thetaZ01 := by
  intro a b h
  have := congrArg (fun x : Z01 => (x : Perm (Fin 12))) h
  exact Subtype.ext (Subtype.mk.inj (thetaHom_injective this))

theorem thetaZ01_bijective :
    Function.Bijective thetaZ01 := by
  rw [Nat.bijective_iff_injective_and_card]
  exact ⟨thetaZ01_injective, by rw [card_CJc, card_altCentralizer_swap01]⟩

@[expose] def cjcEquiv :
    CJ cR ≃* Perm (Fin 10) :=
  (MulEquiv.ofBijective thetaZ01 thetaZ01_bijective).trans s10Equiv.symm

theorem orbits_CJc :
    {x : X | cR • x = x} = MulAction.orbit (CJ cR) x0 ∪
      MulAction.orbit (CJ cR) (b1 1 (by norm_num)) ∪ MulAction.orbit (CJ cR) (b1 2 (by norm_num)) ∧
    (MulAction.orbit (CJ cR) x0).ncard = 1 ∧
    (MulAction.orbit (CJ cR) (b1 1 (by norm_num))).ncard = 945 ∧
    (MulAction.orbit (CJ cR) (b1 2 (by norm_num))).ncard = 210 := by
  rw [← K1_eq, ← b1_zero]
  refine ⟨Set.Subset.antisymm fix_t1_cover (Set.union_subset (Set.union_subset
    (orbit1_subset_fix _) (orbit1_subset_fix _)) (orbit1_subset_fix _)), ?_, ?_, ?_⟩ <;>
    rw [orbit1_ncard] <;> rfl

theorem b1_fix
    {i : ℕ} (hi : i < 3) : cR • b1 i hi = b1 i hi :=
  orbit1_subset_fix hi (MulAction.mem_orbit_self _)

end CFSG.Sporadic.HNOddCore
