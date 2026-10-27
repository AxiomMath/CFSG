module

public import Certificates.Data.Kernel.ThCent.List

public section

namespace CFSG.KC.ThFive

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.SectionRank.Native

universe u

@[expose] noncomputable def opOf (l : List Nat) : Op :=
  Bool.rec (motive := fun _ => Op) (Op.pow (l.getD 1 0) (l.getD 2 0) (l.getD 3 0))
    (Op.mul (l.getD 1 0) (l.getD 2 0) (l.getD 3 0)) (Nat.beq (l.getD 0 0) 0)

@[expose] noncomputable def runK {α : Sort u} (c rm ONE : Nat) (prog : List Op) (k : (Nat → Nat) → α) :
    (Nat → Nat) → α :=
  List.rec (motive := fun _ => (Nat → Nat) → α) (fun R => k R)
    (fun op _ ih R => Op.rec (motive := fun _ => α)
      (fun i j k' => strictF (mulB c rm (R i) (R j)) fun v => ih (updN R k' v))
      (fun e i k' => strictF (powB c rm ONE (R i) e (nat_lit 6)) fun v => ih (updN R k' v)) op) prog

@[expose] noncomputable def eqB (c rm ONE X Y : Nat) : Bool :=
  Nat.beq (mulB c rm X ONE) (mulB c rm Y ONE)

@[expose] noncomputable def file5 (ONE X₀ X₁ X₂ X₃ X₄ : Nat) : Nat → Nat :=
  updN (updN (updN (initPk X₀ X₁ ONE) 2 X₂) 3 X₃) 4 X₄

@[expose] noncomputable def pgOK (c rm ONE Q₁ Q₂ : Nat) : Bool :=
  strictF (mulB c rm (mulB c rm (mulB c rm Q₁ Q₂) (powB c rm ONE Q₁ 4 (nat_lit 3)))
      (powB c rm ONE Q₂ 4 (nat_lit 3))) fun C =>
    andB (cubeOK5 c rm ONE Q₁ Q₂ C) (Nat.beq (powB c rm ONE C 5 (nat_lit 3)) ONE)

@[expose] noncomputable def entOK (c rm ONE A B r h c₁ z y₁ y₂ w : Nat) : Bool :=
  andB (neB c rm ONE r ONE) (andB (eqB c rm ONE r y₁)
    (andB (Nat.beq (mulB c rm A r) (mulB c rm r A)) (andB (Nat.beq (mulB c rm c₁ r) (mulB c rm r c₁))
      (andB (Nat.beq (mulB c rm r h) (mulB c rm h y₂)) (andB (Nat.beq (mulB c rm z y₂) (mulB c rm y₂ z))
        (eqB c rm ONE w B))))))

@[expose] noncomputable def chk (c rm ONE A B : Nat) (P1 P2 P3 : List (List Nat)) (O1 O2 O3 : List Nat) :
    Bool :=
  andB (powsOK (P1.map opOf)) (andB (powsOK (P2.map opOf)) (andB (powsOK (P3.map opOf))
    (runK c rm ONE (P1.map opOf) (fun R =>
      strictF (R (O1.getD 0 0)) fun q₁ => strictF (R (O1.getD 1 0)) fun q₂ =>
      strictF (R (O1.getD 2 0)) fun r => strictF (R (O1.getD 3 0)) fun h =>
      strictF (R (O1.getD 4 0)) fun c₁ => strictF (R (O1.getD 5 0)) fun z =>
      andB (pgOK c rm ONE q₁ q₂)
        (runK c rm ONE (P2.map opOf) (fun S =>
          strictF (S (O2.getD 0 0)) fun y₁ => strictF (S (O2.getD 1 0)) fun y₂ =>
          runK c rm ONE (P3.map opOf) (fun T =>
            entOK c rm ONE A B r h c₁ z y₁ y₂ (T (O3.getD 0 0)))
            (file5 ONE q₁ q₂ A c₁ z))
          (initPk q₁ q₂ ONE)))
      (initPk A B ONE))))

end CFSG.KC.ThFive

end
