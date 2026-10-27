module

public import CFSG.Monster.B.TwoA.Unitary.TwentyData
public import CFSG.Monster.Code.Bits
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import CFSG.Monster.B.TwoA.Unitary.TwentyAlgInputs
public import Certificates.Certificate3082

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster.Code

theorem recordsOK :
    ∀ j < 400, wordRows u20Words[j]! = u20RecRows[j]! :=
  Certificates.certificate3082.1

theorem certOK : ∀ c < 400, combRows unitCert[c]! = eRows c :=
  Certificates.certificate3082.2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (b : Module.Basis (Fin 20) (ZMod 2) V)

@[expose] noncomputable def decB (c : ℕ) : V := ∑ t : Fin 20, bvec 20 c t • b t

theorem decB_xor (x y : ℕ) : decB b (x ^^^ y) = decB b x + decB b y := by
  simp only [decB, bvec_xor, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem decB_zero : decB b 0 = 0 := by simp [decB, bvec_zero]

@[expose] noncomputable def endOf (rows : Array ℕ) : Module.End (ZMod 2) V :=
  b.constr (ZMod 2) fun t => decB b rows[(t : ℕ)]!

theorem endOf_basis (rows : Array ℕ) (t : Fin 20) : endOf b rows (b t) = decB b rows[(t : ℕ)]! :=
  b.constr_basis (ZMod 2) _ t

theorem actGoR_hom {M : Type*} [AddCommMonoid M] (F : ℕ → M)
    (hF : ∀ x y, F (x ^^^ y) = F x + F y) (h0 : F 0 = 0) (rows : Array ℕ) (c : ℕ) :
    ∀ n, F (actGoR rows c n) = ∑ i ∈ Finset.range n, if c.testBit i then F rows[i]! else 0
  | 0 => by simp [actGoR, h0]
  | n + 1 => by
    rw [actGoR, hF, actGoR_hom F hF h0 rows c n, Finset.sum_range_succ]
    congr 1
    split_ifs <;> simp [h0]

theorem decB_actR (rows : Array ℕ) (c : ℕ) :
    decB b (actR rows c) = ∑ t : Fin 20, bvec 20 c t • decB b rows[(t : ℕ)]! := by
  rw [actR, actGoR_hom (decB b) (decB_xor b) (decB_zero b),
    ← Fin.sum_univ_eq_sum_range (fun i => if c.testBit i then decB b rows[i]! else 0) 20]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

theorem endOf_decB (rows : Array ℕ) (c : ℕ) :
    endOf b rows (decB b c) = decB b (actR rows c) := by
  rw [decB_actR, decB, map_sum]
  simp only [map_smul, endOf_basis]

theorem getElem!_ofFn20 (f : ℕ → ℕ) (t : Fin 20) :
    (((List.range 20).map f).toArray)[(t : ℕ)]! = f t := by
  rw [getElem!_pos _ _ (by simp), List.getElem_toArray, List.getElem_map, List.getElem_range]

theorem endOf_rowsMul (A B : Array ℕ) : endOf b (rowsMul A B) = endOf b B * endOf b A := by
  refine b.ext fun t => ?_
  rw [endOf_basis, Module.End.mul_apply, endOf_basis, endOf_decB, rowsMul, getElem!_ofFn20]

theorem endOf_rowsXor (A B : Array ℕ) : endOf b (rowsXor A B) = endOf b A + endOf b B := by
  refine b.ext fun t => ?_
  rw [endOf_basis, LinearMap.add_apply, endOf_basis, endOf_basis, rowsXor, getElem!_ofFn20,
    decB_xor]

theorem endOf_zeroRows : endOf b zeroRows = 0 := by
  refine b.ext fun t => ?_
  rw [endOf_basis, zeroRows, getElem!_ofFn20, decB_zero, LinearMap.zero_apply]

theorem bvec_one_shiftLeft' (k : ℕ) (i : Fin 20) :
    bvec 20 (1 <<< k) i = if (i : ℕ) = k then 1 else 0 := by
  rw [bvec_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : (i : ℕ) = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem decB_one_shiftLeft (t : Fin 20) : decB b (1 <<< (t : ℕ)) = b t := by
  rw [decB, Finset.sum_eq_single t]
  · rw [bvec_one_shiftLeft', ite_eq_left rfl, one_smul]
  · intro i _ hit
    rw [bvec_one_shiftLeft', ite_eq_right (fun h => hit (Fin.ext h)), zero_smul]
  · simp

theorem endOf_idRows : endOf b idRows = 1 := by
  refine b.ext fun t => ?_
  rw [endOf_basis, idRows, getElem!_ofFn20, decB_one_shiftLeft, Module.End.one_apply]

theorem endOf_foldl (s : ℕ) (l : List ℕ) (acc : Array ℕ) :
    endOf b (l.foldl (fun acc j => if s.testBit j then rowsXor acc u20RecRows[j]! else acc) acc) =
      endOf b acc + (l.map fun j => if s.testBit j then endOf b u20RecRows[j]! else 0).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    split_ifs
    · rw [endOf_rowsXor]
    · rw [add_zero]

theorem endOf_combRows (s : ℕ) :
    endOf b (combRows s) =
      ((List.range 400).map fun j => if s.testBit j then endOf b u20RecRows[j]! else 0).sum := by
  rw [combRows, endOf_foldl, endOf_zeroRows, zero_add]

@[expose] noncomputable def matUnit (a a' : Fin 20) : Module.End (ZMod 2) V :=
  b.constr (ZMod 2) fun t => if t = a then b a' else 0

theorem endOf_eRows (a a' : Fin 20) : endOf b (eRows (20 * a + a')) = matUnit b a a' := by
  refine b.ext fun t => ?_
  rw [endOf_basis, matUnit, b.constr_basis, eRows, getElem!_ofFn20]
  have h1 : (20 * (a : ℕ) + a') / 20 = a := by omega
  have h2 : (20 * (a : ℕ) + a') % 20 = a' := by omega
  rw [h1, h2]
  by_cases h : t = a
  · rw [ite_eq_left (congrArg Fin.val h), ite_eq_left h, decB_one_shiftLeft]
  · rw [ite_eq_right (fun h' => h (Fin.ext h')), ite_eq_right h, decB_zero]

theorem matUnit_mem_span (a a' : Fin 20) :
    matUnit b a a' ∈
      Submodule.span (ZMod 2) (Set.range fun j : Fin 400 => endOf b u20RecRows[(j : ℕ)]!) := by
  rw [← endOf_eRows, ← certOK _ (by omega), endOf_combRows]
  refine list_sum_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  split_ifs
  · exact Submodule.subset_span ⟨⟨j, List.mem_range.1 hj⟩, rfl⟩
  · exact Submodule.zero_mem _

theorem eq_sum_matUnit (f : Module.End (ZMod 2) V) :
    f = ∑ a : Fin 20, ∑ a' : Fin 20, b.repr (f (b a)) a' • matUnit b a a' := by
  refine b.ext fun t => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single t]
  · rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, matUnit, Module.Basis.constr_basis, ite_true]
    exact (b.sum_repr (f (b t))).symm
  · intro a _ hat
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [LinearMap.smul_apply, matUnit, Module.Basis.constr_basis, ite_eq_right (Ne.symm hat),
      smul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem span_endOf_records :
    Submodule.span (ZMod 2) (Set.range fun j : Fin 400 => endOf b u20RecRows[(j : ℕ)]!) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [eq_sum_matUnit b f]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun a' _ =>
    Submodule.smul_mem _ _ (matUnit_mem_span b a a')

open scoped TensorProduct in
theorem isAbsolutelyIrreducible_of_adjoin {F G W : Type*} [Field F] [Monoid G] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] [Nontrivial W] (ρ : Representation F G W)
    (h : Algebra.adjoin F (Set.range ρ) = ⊤) :
    CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ := by
  refine ⟨?_⟩
  have : Nontrivial (AlgebraicClosure F ⊗[F] W) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := F)
      (M := AlgebraicClosure F) (N := W)).2 inferInstance
  apply CFSG.Theory.Representation.irreducible_of_jacobson_density_surjective
  rw [← CFSG.Theory.Representation.extendScalars_surj_iff]
  exact h

end CFSG.Monster.B.TwoA.Unitary
