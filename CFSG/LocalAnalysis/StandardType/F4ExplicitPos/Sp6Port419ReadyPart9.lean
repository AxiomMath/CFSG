module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreToral
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart7

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section
open CFSG.Open
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Chevalley

public section

public section

public section
open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.TitsSimplicity CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section

public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.RankThree.PartOne.KF4

namespace CFSG.StandardType.F4ExplicitPos.ProductTrace

private theorem mapRange_smul_aux {τ : Tag} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (r • x) = f r • Finsupp.mapRange f f.map_zero x := by
  ext a
  simp

theorem bc_apply_aux {τ : Tag} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (A x) = B (Finsupp.mapRange f f.map_zero x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.mapRange_add (map_add f), hx, hy, Finsupp.mapRange_add (map_add f),
      map_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, mapRange_smul_aux, h b, mapRange_smul_aux, map_smul]
    simp

private theorem bc_zero_aux {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    BaseChange f (0 : Module.End R (RootModule τ R)) (0 : Module.End S (RootModule τ S)) :=
  fun _ => by simp

theorem bc_mul_aux {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A' B') :
    BaseChange f (A * A') (B * B') := fun b => by
  rw [Module.End.mul_apply, bc_apply_aux f h, h' b, Module.End.mul_apply]

private theorem bc_add_aux {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {A A' : Module.End R (RootModule τ R)} {B B' : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (h' : BaseChange f A' B') :
    BaseChange f (A + A') (B + B') := fun b => by
  rw [LinearMap.add_apply, Finsupp.mapRange_add (map_add f), h b, h' b, LinearMap.add_apply]

theorem bc_smul_aux {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) (r : R) : BaseChange f (r • A) (f r • B) := fun b => by
  rw [LinearMap.smul_apply, mapRange_smul_aux, h b, LinearMap.smul_apply]

theorem bc_sum_aux {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type*} (s : Finset ι) {A : ι → Module.End R (RootModule τ R)}
    {B : ι → Module.End S (RootModule τ S)} (h : ∀ i ∈ s, BaseChange f (A i) (B i)) :
    BaseChange f (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bc_zero_aux (τ := τ) f)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact bc_add_aux f (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem bc_xCoeff_aux
    {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin τ.rank) (k : ℕ) : BaseChange f (xCoeff τ R i k) (xCoeff τ S i k) :=
  fun b => mapRange_xCoeff_single f i k b

theorem bc_yCoeff_aux
    {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin τ.rank) (k : ℕ) : BaseChange f (yCoeff τ R i k) (yCoeff τ S i k) :=
  fun b => mapRange_yCoeff_single f i k b

theorem bc_xOp_aux
    {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin τ.rank) (c : R) : BaseChange f (xOp τ R i c) (xOp τ S i (f c)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
  refine bc_sum_aux f _ fun k _ => ?_
  rw [← map_pow]
  exact bc_smul_aux f (bc_xCoeff_aux f i k) _

end CFSG.StandardType.F4ExplicitPos.ProductTrace
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end
