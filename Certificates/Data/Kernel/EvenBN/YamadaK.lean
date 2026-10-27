module

public import Certificates.Data.Kernel.EvenBN.F4Mat
public import Certificates.Data.U52Yamada

public section

namespace CFSG.KC.YamadaK

open CFSG.KC.Enum CFSG.KC.F4Mat CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open Certificates.U52Yamada

@[expose] def g4 (c : Nat) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def all4 (f : Nat → Bool) : Bool := f 0 && f 1 && f 2 && f 3

@[expose] noncomputable def vpK (a b : Nat) : Bool :=
  Nat.beq (ent MT (Nat.add (Nat.mul 4 a) (ent BT a))) (Nat.xor b (ent BT b))

@[expose] noncomputable def nfK (a₁ b₁ a₂ a₃ a₄ b₄ : Nat) : Nat :=
  mulK (mulK (mulK (enc (x₁Mat (g4 a₁) (g4 b₁))) (enc (x₂Mat (g4 a₂)))) (enc (x₃Mat (g4 a₃))))
    (enc (x₄Mat (g4 a₄) (g4 b₄)))

@[expose] noncomputable def wordK (w : List (Fin 10)) : Nat :=
  List.rec (motive := fun _ => Nat) (enc 1) (fun i _ acc => mulK (enc (genMat i)) acc) w

@[expose] noncomputable def conjK (k : Fin 8) (S : Nat) : Nat :=
  mulK (mulK (wordK (conjWord k)) S) (invK (wordK (conjWord k)))

@[expose] def idL : List (Nat × Nat) :=
  [(0, 1), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 1), (7, 0), (8, 0), (9, 0),
   (10, 0), (11, 0), (12, 1), (13, 0), (14, 0), (15, 0), (16, 0), (17, 0), (18, 1), (19, 0),
   (20, 0), (21, 0), (22, 0), (23, 0), (24, 1)]

@[expose] noncomputable def barK (A : Nat) : Nat :=
  strictN A fun a => encF (fun t => ent BT (ent a t)) 25 0

@[expose] noncomputable def t39 (a₁ b₁ a₂ a₃ a₄ b₄ : Nat) : Bool :=
  !vpK a₁ b₁ || !vpK a₄ b₄ ||
    strictB (nfK a₁ b₁ a₂ a₃ a₄ b₄) fun S =>
      !chkL (mulK S S) idL || chkL S fShapeL || chkL (conjK 0 S) fShapeL ||
        chkL (conjK 1 S) fShapeL || chkL (conjK 2 S) fShapeL || chkL (conjK 3 S) fShapeL ||
        chkL (conjK 4 S) fShapeL || chkL (conjK 5 S) fShapeL || chkL (conjK 6 S) fShapeL ||
        chkL (conjK 7 S) fShapeL

@[expose] def lk (H : List (Nat × Nat)) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ ih => Prod.rec (motive := fun _ => Nat) (fun a b => Bool.rec ih b (Nat.beq a k)) p) H

@[expose] def dg (m i : Nat) : Nat := Nat.mod (Nat.div m (Nat.pow 4 i)) 4

@[expose] def key (a₁ b₁ a₂ a₃ a₄ b₄ : Nat) : Nat :=
  ((((a₁ * 4 + b₁) * 4 + a₂) * 4 + a₃) * 4 + a₄) * 4 + b₄

@[expose] noncomputable def w3101 (m S : Nat) : Bool :=
  vpK (dg m 5) (dg m 4) && vpK (dg m 1) (dg m 0) &&
    strictB (nfK (dg m 5) (dg m 4) (dg m 3) (dg m 2) (dg m 1) (dg m 0)) fun M =>
      Nat.beq (mulK M S) (barK M)

@[expose] noncomputable def t3101 (H : List (Nat × Nat)) (a₁ b₁ a₂ a₃ a₄ b₄ : Nat) : Bool :=
  !vpK a₁ b₁ || !vpK a₄ b₄ ||
    strictB (nfK a₁ b₁ a₂ a₃ a₄ b₄) fun S =>
      !chkL (mulK S (barK S)) idL || w3101 (lk H (key a₁ b₁ a₂ a₃ a₄ b₄)) S

@[expose] def hint3101 : List (Nat × Nat) :=
  [(0, 0), (1, 6), (6, 10), (7, 14), (16, 32), (17, 38), (22, 42), (23, 46), (64, 128), (65, 134),
   (70, 138), (71, 142), (80, 166), (81, 160), (86, 174), (87, 170), (256, 1536), (257, 1542),
   (262, 1546), (263, 1550), (272, 1568), (273, 1574), (278, 1578), (279, 1582), (352, 1664),
   (353, 1670), (358, 1674), (359, 1678), (368, 1702), (369, 1696), (374, 1710), (375, 1706),
   (1536, 2560), (1537, 2598), (1552, 2592), (1553, 2566), (1574, 2570), (1575, 2606),
   (1590, 2602), (1591, 2574), (1610, 2694), (1611, 2720), (1626, 2688), (1627, 2726),
   (1646, 2702), (1647, 2730), (1662, 2698), (1663, 2734), (1792, 3584), (1793, 3622),
   (1808, 3616), (1809, 3590), (1830, 3594), (1831, 3630), (1846, 3626), (1847, 3598),
   (1870, 3726), (1871, 3754), (1886, 3722), (1887, 3758), (1898, 3718), (1899, 3744),
   (1914, 3712), (1915, 3750)]

@[expose] noncomputable def c39 (a₁ : Nat) : Bool :=
  all4 fun b₁ => all4 fun a₂ => all4 fun a₃ => all4 fun a₄ => all4 fun b₄ => t39 a₁ b₁ a₂ a₃ a₄ b₄

@[expose] noncomputable def c3101 (a₁ : Nat) : Bool :=
  all4 fun b₁ => all4 fun a₂ => all4 fun a₃ => all4 fun a₄ => all4 fun b₄ =>
    t3101 hint3101 a₁ b₁ a₂ a₃ a₄ b₄

end CFSG.KC.YamadaK
