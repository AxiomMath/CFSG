
module

public import CFSG.Sporadic.SuzOddCore.InvGraphBase

public import CFSG.Sporadic.SuzOddCore.InvPerms
public import CFSG.Certificates.NativeRefine
public import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
public import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Mathlib.Data.Fintype.Card
public import CFSG.Sporadic.SuzOddCore.InvGraphCheck

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem invNbr_facts :
    AdjFacts 1782 #[b0Arr, b1Arr] invNbr invNeighbors :=
  adjFacts_of_adjOK invGraph_check.1

theorem invNbr_inv_M
    {σ : Equiv.Perm (Fin 1782)} (hσ : σ ∈ suzM) : NbrInv invNbr σ :=
  invNbr_facts.inv_of_mem_closure (fun _ hk => rep_bPair hk) (suzM_eq_closure_gens ▸ hσ)

theorem invNbr_inv_v :
    NbrInv invNbr suzV := by
  intro x y
  rw [← rep_v x, invGraph_check.2.1 x x.2, mem_imgSorted]
  constructor
  · intro hy
    exact ⟨y, hy, rep_v y⟩
  · rintro ⟨p, hp, hpy⟩
    have hpn := (invNbr_facts.point x).lt p hp
    rw [rep_v.apply hpn] at hpy
    have : (⟨p, hpn⟩ : Fin 1782) = y := suzV.injective (Fin.ext hpy)
    rw [← this]
    exact hp

theorem invNbr_inv_T
    {σ : Equiv.Perm (Fin 1782)} (hσ : σ ∈ suzT) : NbrInv invNbr σ := by
  induction hσ using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | hg
    · exact invNbr_inv_v
    · exact invNbr_inv_M hg
  | one => exact fun x y => Iff.rfl
  | mul g h _ _ hg hh => exact AdjFacts.nbrInv_mul hg hh
  | inv g _ hg => exact AdjFacts.nbrInv_inv hg

theorem invNbr_zero
    (z : Fin 1782) : (z : ℕ) ∈ invNbr[((0 : Fin 1782) : ℕ)]! ↔ z ∈ invLambda := by
  rw [Fin.val_zero, invNbr_facts.root]
  rfl

theorem invNbr_symm
    {x y : Fin 1782} (h : (y : ℕ) ∈ invNbr[(x : ℕ)]!) :
    (x : ℕ) ∈ invNbr[(y : ℕ)]! := by
  obtain ⟨m, hm, hmx⟩ := suzM_transitive x
  have hinv := invNbr_inv_M (suzM.inv_mem hm)
  have h1 := (hinv x y).1 h
  have hx0 : m⁻¹ x = 0 := by rw [← hmx, perm_inv_apply']
  rw [hx0, Fin.val_zero] at h1
  have h2 := invNbr_facts.root_symm _ h1
  rw [hinv y x, hx0, Fin.val_zero]
  exact h2

theorem invNbr_adj
    (x y : Fin 1782) : (y : ℕ) ∈ invNbr[(x : ℕ)]! ↔ invGraph.Adj x y := by
  rw [invGraph_adj]
  constructor
  · intro h
    obtain ⟨m, hm, hmx⟩ := suzM_transitive x
    have hinv := invNbr_inv_M (suzM.inv_mem hm)
    have h1 := (hinv x y).1 h
    have hx0 : m⁻¹ x = 0 := by rw [← hmx, perm_inv_apply']
    rw [hx0, invNbr_zero] at h1
    exact ⟨m, hm, m⁻¹ y, h1, Or.inl ⟨hmx, perm_apply_inv' m y⟩⟩
  · rintro ⟨g, hg, z, hz, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ((invNbr_inv_M hg) 0 z).1 ((invNbr_zero z).2 hz)
    · exact invNbr_symm (((invNbr_inv_M hg) 0 z).1 ((invNbr_zero z).2 hz))

theorem suzT_adj
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzT) (x y : Fin 1782) :
    invGraph.Adj (g x) (g y) ↔ invGraph.Adj x y := by
  rw [← invNbr_adj, ← invNbr_adj, invNbr_inv_T hg x y]

theorem invGraph_regular
    (x : Fin 1782) : {y | invGraph.Adj x y}.ncard = 416 := by
  have hset : {y | invGraph.Adj x y} = finSet 1782 invNbr[(x : ℕ)]! := by
    ext y
    rw [Set.mem_ofPred_eq, ← invNbr_adj]
    rfl
  rw [hset, ← invGraph_check.2.2.1 x x.2]
  exact ncard_finSet (invNbr_facts.point x)

end CFSG.Sporadic.SuzOddCore
