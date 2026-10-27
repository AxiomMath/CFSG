module

public import Certificates.Data.Kernel.Card7H3.Gen
public import Certificates.Data.Kernel.PermCent.KGrpC3
public import Certificates.Data.Kernel.PermCent.ForceCV
public import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs

public section

namespace CFSG.Certificates.Kernel.Card7H3

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Prop121.Card7.HC

@[expose] noncomputable def hlC : List (CV 11) :=
  ((flipsL.map fun f => (cOf f, decide (Equiv.Perm.sign f = 1))).flatMap fun f =>
    (s4L.map cOf).flatMap fun s =>
      (((s3L.map fun t => (cOf t, decide (Equiv.Perm.sign t = 1))).filter fun t => f.2 == t.2).map
        fun t => f.1 * s * t.1))

@[expose] def t1P : P11 := Equiv.swap 8 9 * Equiv.swap 9 10

@[expose] noncomputable def clF (B0 IL : List (CV 11)) (m : Nat) : List (CV 11) :=
  IL.filter fun σ => decide ((B0.countP fun c => eq22C c σ σ c) = m)

@[expose] def forceCls {β : Sort _} : List (CV 11 × List (CV 11)) → (List (CV 11 × List (CV 11)) → β) → β
  | [], k => k []
  | c :: l, k => forceC c.1 fun a => forceCL c.2 fun m => forceCls l fun l => k ((a, m) :: l)

@[expose] noncomputable def withLists {β : Sort _}
    (k : List (CV 11) → List (CV 11) → List (CV 11) → List (CV 11 × List (CV 11)) → β) : β :=
  forceCL hlC fun HL => forceCL (b0G HL (cOf t1P)) fun B0 => forceCL (ilG B0) fun IL =>
    forceCls (classesAuxG B0 43 IL) fun C => k HL B0 IL C

@[expose] noncomputable def k5082a : Bool :=
  withLists fun _ B0 IL C => classesCheckG B0 IL C (cOf Y11)

@[expose] noncomputable def k5082b : Bool :=
  withLists fun _ _ IL _ => powCheckG IL

@[expose] noncomputable def k5082c : Bool :=
  withLists fun _ B0 IL C => forceCL (clF B0 IL 96) fun L96 => forceCL (clF B0 IL 48) fun L48 =>
    ryCheckG IL C L96 L48 (cOf Y11)

end CFSG.Certificates.Kernel.Card7H3

end
