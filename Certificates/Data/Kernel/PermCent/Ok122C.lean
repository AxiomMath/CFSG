module

public import Certificates.Data.Kernel.PermCent.AllPermsC
public import CFSG.GH74.GLS.C3.Layer2.NumMoved

public section

namespace CFSG.Certificates.Kernel.PkCV

@[expose] def ok122G {G : Type*} [Group G] [DecidableEq G] (I O S : List G) (nm : G → Nat) : Bool :=
  I.all fun a => I.all fun b =>
    !(decide (a * b = b * a) && !decide (a = b)) ||
    !((O.filter fun ρ => decide (ρ * a = a * ρ)).any fun ρ => decide (ρ * b = b * ρ)) ||
    O.all fun σ =>
      !((decide (σ * a * σ⁻¹ = b) || decide (σ * a * σ⁻¹ = a * b)) &&
        (decide (σ * b * σ⁻¹ = a) || decide (σ * b * σ⁻¹ = b) || decide (σ * b * σ⁻¹ = a * b))) ||
      !(((S.filter fun s => decide (s * a = a * s)).filter fun s => decide (s * b = b * s)).all
        fun s => decide (σ * s * σ⁻¹ * s = 1 ∨ σ * s * σ⁻¹ * s = a ∨ σ * s * σ⁻¹ * s = b ∨
          σ * s * σ⁻¹ * s = a * b)) ||
      decide (nm σ = 3)

@[expose] noncomputable def cmC {n : Nat} [Small n] (a b : CV n) : Bool := eq22C a b b a

@[expose] noncomputable def inVC {n : Nat} [Small n] (a b ab t : CV n) : Bool :=
  powOneC t 1 || Nat.beq t.1 a.1 || Nat.beq t.1 b.1 || Nat.beq t.1 ab.1

@[expose] noncomputable def ok122B (I O S : List (CV 7)) : Bool :=
  I.all fun a =>
    forceCL (O.filter fun ρ => cmC ρ a) fun Ca => forceCL (S.filter fun s => cmC s a) fun Sa =>
    I.all fun b =>
      !(cmC a b && !Nat.beq a.1 b.1) ||
      !(Ca.any fun ρ => cmC ρ b) ||
      forceC (a * b) fun ab => forceCL (Sa.filter fun s => cmC s b) fun Sab =>
      O.all fun σ =>
        !((eq22C σ a b σ || eq22C σ a ab σ) &&
          (eq22C σ b a σ || eq22C σ b b σ || eq22C σ b ab σ)) ||
        forceC σ⁻¹ fun σi =>
        !(Sab.all fun s => forceC (σ * s * σi * s) fun t => inVC a b ab t) ||
        decide (CFSG.GH74.GLS.C3.Layer2.numMoved (ev σ) = 3)

@[expose] noncomputable def inv7P : List (CV 7) :=
  ((allPermsP 7 inferInstance).filter fun x => !x.2 && powOneC x.1 2 && !powOneC x.1 1).map
    Prod.fst

@[expose] noncomputable def ord3P : List (CV 7) :=
  ((allPermsP 7 inferInstance).filter fun x => powOneC x.1 3 && !powOneC x.1 1).map Prod.fst

@[expose] def swaps7 : List (Equiv.Perm (Fin 7)) :=
  (List.finRange 7).flatMap fun i =>
    ((List.finRange 7).filter fun j => !decide (i = j)).map fun j => Equiv.swap i j

@[expose] noncomputable def swapsP : List (CV 7) := swaps7.map cOf

@[expose] noncomputable def ok122F : Bool :=
  forceCL inv7P fun I => forceCL ord3P fun O => forceCL swapsP fun S => ok122B I O S

@[expose] noncomputable def comm3F : Bool :=
  forceCL inv7P fun I => forceCL ord3P fun O => I.all fun a => O.any fun ρ => cmC ρ a

end CFSG.Certificates.Kernel.PkCV

end
