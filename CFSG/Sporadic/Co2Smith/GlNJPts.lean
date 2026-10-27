module

public import CFSG.Sporadic.Co2Smith.GlNJCoord
public import CFSG.Sporadic.Co2Smith.GlNJCheck
public import CFSG.Sporadic.Co2Smith.GlC0Fix
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Matrix Pointwise

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Rows


theorem co2PermHom_eq_iff_maps {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    {x y : ℕ} (hx : x < 2300) (hy : y < 2300) :
    co2PermHom g ⟨x, hx⟩ = ⟨y, hy⟩ ↔ Native.glMaps R x y = true := by
  refine ⟨fun h => ?_, co2PermHom_apply_of_maps hg hx hy⟩
  have e := co2Vec_permEquiv g ⟨x, hx⟩
  rw [co2PermEquiv_apply, h] at e
  change co2Vec y = g.val.val *ᵥ co2Vec x at e
  rw [co2Vec_eq hy, co2Vec_eq hx, val_mulVec hg] at e
  rw [Native.glMaps, beq_iff_eq]
  exact toVecD_injective (colAct_lt R _) (co2Packed_facts hy).1 e.symm

theorem co2PermHom_fix_iff {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    {x : ℕ} (hx : x < 2300) :
    co2PermHom g ⟨x, hx⟩ = ⟨x, hx⟩ ↔ Native.colAct R co2PackedVecs[x]! = co2PackedVecs[x]! := by
  rw [co2PermHom_eq_iff_maps hg hx hx, Native.glMaps, beq_iff_eq]

theorem fixK_eq_glNJFixR {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R) :
    fixK g = Native.glNJFixR R := by
  set pts := (List.range 2300).filter fun i =>
    Native.colActT (transposeRows 22 R) co2PackedVecs[i]! == co2PackedVecs[i]!
  have hnd : pts.Nodup := List.nodup_range.filter _
  have hlt : ∀ x ∈ pts, x < 2300 := fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1
  have hset : {x : Fin 2300 | co2PermHom g x = x} = {y : Fin 2300 | (y : ℕ) ∈ pts} := by
    ext y
    simp only [Set.mem_ofPred_eq, pts, List.mem_filter, List.mem_range, y.2, true_and,
      beq_iff_eq]
    exact co2PermHom_fix_iff hg y.2
  have hcard : fixK g = {x : Fin 2300 | co2PermHom g x = x}.ncard :=
    Nat.card_coe_set_eq {x : Fin 2300 | co2PermHom g x = x}
  rw [hcard, hset, ncard_setOf_mem hnd hlt]
  rfl

end Rows

section Cent


@[expose] def ptP : Fin 2300 := ⟨1, by norm_num⟩

theorem jcElt_fix_ptP {m : ℕ} (hm : m < 1024) (h : co2PermHom (jcElt m) ptP = ptP) : m = 0 := by
  by_contra h0
  exact glNJPt_spec.2.1 m hm h0 ((co2PermHom_fix_iff (jcElt_val m) (by norm_num)).1 h)

theorem eq_one_of_fix_basis {d : K}
    (h : ∀ x (hx : x ∈ Native.glNJBasis), co2PermHom d ⟨x, (glNJPt_spec.2.2.2.2.1 x hx).1⟩ =
      ⟨x, (glNJPt_spec.2.2.2.2.1 x hx).1⟩) : d = 1 := by
  set Rb := Native.glNJBasis.toArray.map fun x => co2PackedVecs[x]!
  set B := rowsMatrix 22 Rb
  have hBs : Rb.size = 22 := by rw [Array.size_map, List.size_toArray, glNJPt_spec.2.2.2.1]
  have hrow : ∀ t : Fin 22, d.val.val *ᵥ (fun j => B t j) = fun j => B t j := by
    intro t
    have ht : (t : ℕ) < Native.glNJBasis.length := by rw [glNJPt_spec.2.2.2.1]; exact t.2
    set x := Native.glNJBasis[(t : ℕ)]
    have hx : x ∈ Native.glNJBasis := List.getElem_mem ht
    have hx2 := (glNJPt_spec.2.2.2.2.1 x hx).1
    have hBt : (fun j => B t j) = co2Vec x := by
      funext j
      rw [co2Vec_eq hx2]
      show rowsMatrix 22 Rb t j = _
      rw [rowsMatrix_apply]
      congr 2
      rw [Array.getElem?_map, List.getElem?_toArray, List.getElem?_eq_getElem ht]
      rfl
    have e := co2Vec_permEquiv d ⟨x, hx2⟩
    rw [co2PermEquiv_apply, h x hx] at e
    rw [hBt]
    exact e.symm
  have hdB : d.val.val * Bᵀ = Bᵀ := by
    ext i t
    have := congrFun (hrow t) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
  have hinv : B * rowsMatrix 22 Native.glNJBasisInv = 1 := by
    rw [← rowsMatrix_mulRows, glNJPt_spec.2.2.2.2.2, rowsMatrix_idRows]
  have hinvT : Bᵀ * (rowsMatrix 22 Native.glNJBasisInv)ᵀ = 1 := by
    rw [mul_eq_one_comm, ← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  apply eq_of_val_eq
  rw [val_val_one]
  calc d.val.val = d.val.val * (Bᵀ * (rowsMatrix 22 Native.glNJBasisInv)ᵀ) := by
        rw [hinvT, Matrix.mul_one]
    _ = Bᵀ * (rowsMatrix 22 Native.glNJBasisInv)ᵀ := by rw [← Matrix.mul_assoc, hdB]
    _ = 1 := hinvT

theorem centralizer_Jc_le : centralizer (Jc : Set K) ≤ Jc := by
  intro c hc
  have hcomm : ∀ m, jcElt m * c = c * jcElt m := fun m => mem_centralizer_iff.1 hc _ (jcElt_mem m)
  obtain ⟨x, hx⟩ : ∃ x, co2PermHom c ptP = x := ⟨_, rfl⟩
  obtain ⟨hm, hcase⟩ := glNJPt_spec.2.2.1 x x.2
  obtain ⟨m, hmdef⟩ : ∃ m, Native.glNJPtJ[(x : ℕ)]! = m := ⟨_, rfl⟩
  rw [hmdef] at hm hcase
  have key : co2PermHom (jcElt m) ptP = x := by
    rcases hcase with h1 | ⟨h0, h2⟩
    · exact co2PermHom_apply_of_maps (jcElt_val m) (by norm_num) x.2 h1
    · exfalso
      have hf : co2PermHom (jcElt m) x = x := co2PermHom_apply_of_maps (jcElt_val m) x.2 x.2 h2
      have e1 : co2PermHom c (co2PermHom (jcElt m) ptP) = co2PermHom c ptP := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, ← hcomm, map_mul, Equiv.Perm.mul_apply, hx]
        exact hf
      exact h0 (jcElt_fix_ptP hm ((co2PermHom c).injective e1))
  have hd1 : co2PermHom (jcElt m * c) ptP = ptP := by
    rw [map_mul, Equiv.Perm.mul_apply, hx, ← key, ← Equiv.Perm.mul_apply, ← map_mul,
      jcElt_mul_self, map_one, Equiv.Perm.one_apply]
  have hdc : ∀ m', jcElt m' * (jcElt m * c) = jcElt m * c * jcElt m' := by
    intro m'
    rw [← mul_assoc, jcElt_comm, mul_assoc, hcomm, mul_assoc]
  have hd : jcElt m * c = 1 := by
    refine eq_one_of_fix_basis fun y hy => ?_
    obtain ⟨hy2, hmaps⟩ := glNJPt_spec.2.2.2.2.1 y hy
    have e := co2PermHom_apply_of_maps (jcElt_val Native.glNJPtJ[y]!) (by norm_num) hy2 hmaps
    rw [← e, ← Equiv.Perm.mul_apply, ← map_mul, ← hdc, map_mul, Equiv.Perm.mul_apply]
    exact congrArg _ hd1
  have hc' : c = jcElt m := by
    calc c = jcElt m * (jcElt m * c) := by rw [← mul_assoc, jcElt_mul_self, one_mul]
      _ = jcElt m := by rw [hd, mul_one]
  rw [hc']
  exact jcElt_mem m

end Cent

end CFSG.Sporadic.Co2Smith
