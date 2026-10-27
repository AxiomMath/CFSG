module

public import CFSG.Sporadic.Recognition.M22Multiplier
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Certificates.Data.Kernel.TwoM22.Data

public section

namespace CFSG.Quasithin.TwoM22.Gens

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

@[expose] noncomputable def pkPerm (n w P Q : Nat) : Equiv.Perm (Fin n) :=
  if h : permOK n w (mask w) (n * w) P Q = true then
    Equiv.ofBijective
      (fun i : Fin n => (⟨pg w (mask w) P i, ((permOK_facts h).2.2 i i.2).1⟩ : Fin n))
      (Finite.injective_iff_bijective.mp fun i j hij => Fin.ext (by
        have hi := ((permOK_facts h).2.2 i i.2).2
        have hj := ((permOK_facts h).2.2 j j.2).2
        have e : pg w (mask w) P i = pg w (mask w) P j := congrArg Fin.val hij
        rw [← hi, ← hj, e]))
  else 1

theorem pkPerm_apply {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) (i : Fin n) :
    ((pkPerm n w P Q i : Fin n) : Nat) = pg w (mask w) P i := by
  simp [pkPerm, h]

abbrev TwoM22W : Type := Equiv.Perm (Fin 660) × Equiv.Perm (Fin 22)

@[expose] noncomputable def a660P : Equiv.Perm (Fin 660) := pkPerm 660 10 CFSG.KD.TwoM22.a CFSG.KD.TwoM22.ai

@[expose] noncomputable def b660P : Equiv.Perm (Fin 660) := pkPerm 660 10 CFSG.KD.TwoM22.b CFSG.KD.TwoM22.bi

@[expose] noncomputable def t660P : Equiv.Perm (Fin 660) := pkPerm 660 10 CFSG.KD.TwoM22.t CFSG.KD.TwoM22.t

@[expose] def t22P : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 5] * List.formPerm [2, 3] * List.formPerm [8, 20] * List.formPerm [10, 21] *
    List.formPerm [11, 17] * List.formPerm [14, 15] * List.formPerm [16, 19]

@[expose] noncomputable def twoM22Gen : Fin 2 → TwoM22W
  | 0 => (a660P, (CFSG.Sporadic.Recognition.M22Multiplier.m22Gen 0 :
      CFSG.Blueprint.NativeSporadic.M22))
  | 1 => (b660P, (CFSG.Sporadic.Recognition.M22Multiplier.m22Gen 1 :
      CFSG.Blueprint.NativeSporadic.M22))

@[expose] noncomputable def twoM22T :TwoM22W := (t660P, t22P)

noncomputable abbrev twoM22M : Subgroup TwoM22W := Subgroup.closure (Set.range twoM22Gen)

@[expose] def letterOf {G : Type*} [Group G] (g : Fin 2 → G) (c : Nat) : G :=
  if c = 0 then g 0 else if c = 1 then g 1 else if c = 2 then (g 0)⁻¹ else (g 1)⁻¹

@[expose] def wordOf {G : Type*} [Group G] (g : Fin 2 → G) (d : Nat × Nat) : G :=
  ((List.range d.2).map fun k => letterOf g (Nat.land (Nat.shiftRight d.1 (2 * k)) 3)).prod

@[expose] noncomputable def twoM22SGen (j : Fin 4) : TwoM22W :=
  wordOf twoM22Gen (CFSG.KD.TwoM22.sw.getD j.val (0, 0))

@[expose] noncomputable def twoM22T0 : TwoM22W := wordOf twoM22Gen CFSG.KD.TwoM22.t0w * twoM22T

@[expose] noncomputable def twoM22S : Subgroup TwoM22W :=
  Subgroup.closure (Set.range twoM22SGen ∪ {twoM22T0})

end CFSG.Quasithin.TwoM22.Gens

end
