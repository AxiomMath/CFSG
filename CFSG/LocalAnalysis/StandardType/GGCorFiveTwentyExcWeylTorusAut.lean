module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenRefl
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  Multiplicative

namespace ExcWeylOuter

section TorusAut

variable {τ : Tag} {p : ℕ}

variable (τ p) in
@[expose] noncomputable def torusMulAut [NeZero p] :
    WeylGroup τ →* MulAut (Multiplicative (Fin τ.rank → ZMod p)) where
  toFun w := AddEquiv.toMultiplicative
    { toFun := TableBExc.torusAct τ p w
      invFun := TableBExc.torusAct τ p w⁻¹
      left_inv := fun x => by
        rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]
      right_inv := fun x => by
        rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]
      map_add' := NoTvAut.torusAct_add w }
  map_one' := MulEquiv.ext fun x => congrArg ofAdd (TableBExc.torusAct_one (toAdd x))
  map_mul' w w' := MulEquiv.ext fun x =>
    congrArg ofAdd (TableBExc.torusAct_mul w w' (toAdd x))

theorem torusMulAut_apply [NeZero p] (w : WeylGroup τ) (v : Fin τ.rank → ZMod p) :
    torusMulAut τ p w (ofAdd v) = ofAdd (TableBExc.torusAct τ p w v) :=
  rfl

theorem torusMulAut_injective [Fact p.Prime] (hp2 : p ≠ 2) :
    Function.Injective (torusMulAut τ p) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  refine NoOffExc.eq_one_of_torusAct hp2 fun x => ?_
  have h1 := congrArg (fun u => toAdd (u (ofAdd x))) hw
  simpa [torusMulAut_apply] using h1

theorem torusMulAut_simple [NeZero p] (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (i : Fin τ.rank) :
    torusMulAut τ p (simple τ i) =
      torusReflAut (cartanFunctional τ p i) (Pi.single i 1) (cartanFunctional_single i) := by
  refine MulEquiv.ext fun x => ?_
  rw [← ofAdd_toAdd x, torusMulAut_apply, torusReflAut_apply, ← TableBExc.torusRefl_eq_torusAct
    hsymm, TableBExc.torusRefl_eq]

theorem range_torusMulAut [NeZero p] (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) :
    (torusMulAut τ p).range = Subgroup.closure (Set.range fun i : Fin τ.rank =>
      torusReflAut (cartanFunctional τ p i) (Pi.single i 1) (cartanFunctional_single i)) := by
  rw [MonoidHom.range_eq_map, ← (coxeterSystem τ).subgroup_closure_range_simple,
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (torusMulAut_simple hsymm i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨simple τ i, ⟨i, rfl⟩, torusMulAut_simple hsymm i⟩

end TorusAut

end ExcWeylOuter

end CFSG.StandardType

end
