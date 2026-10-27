
module

public import CFSG.Monster.B.TwoA.Unitary.TwentyBase

public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Monster.B.TwoA.Unitary.TwentyAlg
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyData
public import Certificates.Certificate3083
public import CFSG.Monster.B.TwoA.Unitary.TwentyAlgInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisCert CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA

attribute [local irreducible] decW u20RecRows u20Gens u20Words u20Basis

open scoped TensorProduct

theorem w20End_genU
    (k : Fin 17) : w20End (genU k) = endOf b20
    u20Gens[(k : ℕ)]! := by
  refine b20.ext fun t => ?_
  have hmem : decW (Native.actD 22 n6RowArr[(k : ℕ)]! u20Basis[(t : ℕ)]!) ∈ sigmaPerp :=
    (wAct_genK_decW k _) ▸ wAct_mem_sigmaPerp (genU k) (u20Basis_mem t)
  have e : perpEnd (genU k) (q20P t) = ⟨_, hmem⟩ :=
    Subtype.ext ((perpEnd_apply _ _).trans (wAct_genK_decW k _))
  calc w20End (genU k) (b20 t) = Submodule.Quotient.mk ⟨_, hmem⟩ :=
        (congrArg (w20End (genU k)) (b20_apply t)).trans (congrArg Submodule.Quotient.mk e)
    _ = Submodule.Quotient.mk (comb20 _) := mk_eq_of_xor hmem (coe_comb20 _) (genRows20_ok k t)
    _ = decB b20 _ := (decB_b20 _).symm
    _ = endOf b20 u20Gens[(k : ℕ)]! (b20 t) := (endOf_basis b20 _ t).symm

@[expose] def wordU :
    List ℕ → Usig
  | [] => 1
  | k :: w => (if h : k < 17 then genU ⟨k, h⟩ else 1) * wordU w

theorem w20End_wordU :
    ∀ w : List ℕ, (∀ k ∈ w, k < 17) →
    w20End (wordU w) = endOf b20 (wordRows w)
  | [], _ => by rw [wordU, wordRows, w20End_one, endOf_idRows]
  | k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have ih := w20End_wordU w (fun k' h => hw k' (List.mem_cons_of_mem _ h))
    have hw' : wordU (k :: w) = genU ⟨k, hk⟩ * wordU w := by
      change (if h : k < 17 then genU ⟨k, h⟩ else 1) * wordU w = _
      rw [dite_eq_left hk]
    calc w20End (wordU (k :: w)) = w20End (wordU w) * w20End (genU ⟨k, hk⟩) :=
          (congrArg w20End hw').trans (w20End_mul _ _)
      _ = endOf b20 (wordRows w) * endOf b20 u20Gens[k]! := congrArg₂ (· * ·) ih (w20End_genU _)
      _ = endOf b20 (wordRows (k :: w)) := (endOf_rowsMul b20 _ _).symm

theorem w20End_record
    (j : Fin 400) :
    w20End (wordU u20Words[(j : ℕ)]!) = endOf b20 u20RecRows[(j : ℕ)]! :=
  (w20End_wordU _ (u20Words_lt j j.2)).trans (congrArg (endOf b20) (recordsOK j j.2))

theorem span_rep20 :
    Submodule.span
    (ZMod 2) (Set.range rep20) = ⊤ :=
    by
  refine eq_top_iff.2 ((span_endOf_records b20).symm.le.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span ⟨(wordU u20Words[(j : ℕ)]!)⁻¹,
    (rep20_apply _).trans ((congrArg w20End (inv_inv _)).trans (w20End_record j))⟩

theorem adjoin_rep20 :
    Algebra.adjoin
    (ZMod 2) (Set.range rep20) = ⊤
    :=
  Algebra.toSubmodule_eq_top.1 (eq_top_iff.2 (span_rep20.symm.le.trans
    (Submodule.span_le.2 Algebra.subset_adjoin)))

theorem adjoin_w20End :
    Algebra.adjoin
    (ZMod 2) (Set.range w20End) =
    ⊤ :=
  (congrArg (Algebra.adjoin (ZMod 2)) range_rep20).symm.trans adjoin_rep20

theorem isIrreducible_rep20 :
    rep20.IsIrreducible :=
  CFSG.Theory.Representation.irreducible_of_jacobson_density_surjective rep20 adjoin_rep20

theorem adjoin_extendScalars
    (F' : Type) [Field F']
    [Algebra (ZMod 2) F'] :
    Algebra.adjoin F' (Set.range (CFSG.Theory.Representation.extendScalars F' rep20)) = ⊤ :=
  (CFSG.Theory.Representation.extendScalars_surj_iff F' rep20).1 adjoin_rep20

theorem isAbsolutelyIrreducible_rep20
    :
    CFSG.Theory.Representation.IsAbsolutelyIrreducible rep20 :=
  isAbsolutelyIrreducible_of_adjoin rep20 adjoin_rep20

theorem native_unitary_twenty_full_matrix_algebra :
    sigmaW ∈ sigmaPerp ∧ Module.finrank (ZMod 2) W20 = 20 ∧
    (∀ t : Fin 20, ∃ h : decW u20Basis[(t : ℕ)]! ∈ sigmaPerp,
      b20 t = Submodule.Quotient.mk ⟨_, h⟩) ∧
    (∀ k : Fin 17, w20End (genU k) = endOf b20 u20Gens[(k : ℕ)]!) ∧
    (∀ j : Fin 400, w20End (wordU u20Words[(j : ℕ)]!) = endOf b20 u20RecRows[(j : ℕ)]!) ∧
    Algebra.adjoin (ZMod 2) (Set.range w20End) = ⊤ ∧
    Algebra.adjoin (ZMod 2) (Set.range rep20) = ⊤ ∧
    (∀ (F' : Type) [Field F'] [Algebra (ZMod 2) F'],
      Algebra.adjoin F' (Set.range (CFSG.Theory.Representation.extendScalars F' rep20)) = ⊤) ∧
    rep20.IsIrreducible ∧ CFSG.Theory.Representation.IsAbsolutelyIrreducible rep20 :=
  ⟨sigmaW_mem_sigmaPerp, finrank_W20, b20_eq_mk, w20End_genU, w20End_record, adjoin_w20End,
    adjoin_rep20, fun F' _ _ => adjoin_extendScalars F', isIrreducible_rep20,
    isAbsolutelyIrreducible_rep20⟩

end CFSG.Monster.B.TwoA.Unitary
