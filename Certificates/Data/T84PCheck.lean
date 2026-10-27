module

public import Certificates.Data.T84P

public section

namespace Certificates.T84PCheck

open Certificates.T84P
open Certificates.A5GL42 (ofCode vecOfCode)

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

set_option synthInstance.maxSize 4096

def yE : Elt := (vecOfCode 0, ofCode 5097)

def sE : Elt := (vecOfCode 0, ofCode 4680)

def rankIdx : List (ℕ × ℕ × ℕ) :=
  [(16, 95, 125), (11, 55, 126), (7, 75, 127), (17, 85, 135), (13, 45, 136), (6, 76, 137),
   (5, 76, 137), (2, 75, 127), (15, 65, 155), (14, 46, 156), (12, 56, 157), (1, 55, 126),
   (10, 56, 157), (4, 45, 136), (9, 46, 156), (8, 65, 155), (0, 95, 125), (3, 85, 135),
   (21, 59, 87), (22, 49, 97), (24, 67, 79), (18, 59, 87), (19, 49, 97), (18, 59, 87),
   (20, 67, 79), (19, 49, 97), (20, 67, 79), (40, 98, 115), (10, 56, 157), (5, 76, 137),
   (38, 88, 115), (9, 46, 156), (2, 75, 127), (35, 67, 115), (8, 65, 155), (33, 67, 115),
   (4, 45, 136), (1, 55, 126), (30, 88, 115), (3, 85, 135), (27, 98, 115), (0, 95, 125),
   (30, 88, 115), (27, 98, 115), (33, 67, 115), (4, 13, 136), (9, 14, 156), (4, 13, 136),
   (9, 14, 156), (19, 22, 97), (4, 13, 136), (19, 22, 97), (19, 22, 97), (9, 14, 156),
   (4, 13, 136), (1, 11, 126), (10, 12, 157), (1, 11, 126), (10, 12, 157), (18, 21, 87),
   (1, 11, 126), (18, 21, 87), (18, 21, 87), (10, 12, 157), (1, 11, 126), (8, 15, 155),
   (8, 15, 155), (8, 15, 155), (20, 24, 79), (20, 24, 79), (20, 24, 79), (33, 35, 115),
   (8, 15, 155), (33, 35, 115), (33, 35, 115), (2, 7, 127), (5, 6, 137), (5, 6, 137), (2, 7, 127),
   (2, 7, 127), (20, 24, 67), (20, 24, 67), (20, 24, 67), (5, 6, 137), (2, 7, 127), (3, 17, 135),
   (3, 17, 135), (18, 21, 59), (3, 17, 135), (18, 21, 59), (18, 21, 59), (30, 38, 115),
   (30, 38, 115), (3, 17, 135), (30, 38, 115), (0, 16, 125), (0, 16, 125), (19, 22, 49),
   (0, 16, 125), (19, 22, 49), (19, 22, 49), (27, 40, 115), (27, 40, 115), (0, 16, 125),
   (27, 40, 115), (18, 21, 59), (19, 22, 49), (18, 21, 59), (20, 24, 67), (18, 21, 59),
   (19, 22, 49), (18, 21, 59), (20, 24, 67), (19, 22, 49), (20, 24, 67), (27, 40, 98),
   (27, 40, 98), (30, 38, 88), (33, 35, 67), (33, 35, 67), (30, 38, 88), (27, 40, 98),
   (30, 38, 88), (27, 40, 98), (33, 35, 67), (0, 16, 95), (1, 11, 55), (2, 7, 75), (2, 7, 75),
   (1, 11, 55), (0, 16, 95), (0, 16, 95), (2, 7, 75), (1, 11, 55), (0, 16, 95), (3, 17, 85),
   (4, 13, 45), (5, 6, 76), (5, 6, 76), (4, 13, 45), (3, 17, 85), (3, 17, 85), (5, 6, 76),
   (4, 13, 45), (3, 17, 85), (1, 11, 55), (4, 13, 45), (1, 11, 55), (4, 13, 45), (1, 11, 55),
   (33, 35, 67), (33, 35, 67), (4, 13, 45), (1, 11, 55), (33, 35, 67), (8, 15, 65), (9, 14, 46),
   (10, 12, 56), (10, 12, 56), (9, 14, 46), (8, 15, 65), (8, 15, 65), (10, 12, 56), (9, 14, 46),
   (8, 15, 65), (2, 7, 75), (2, 7, 75), (9, 14, 46), (9, 14, 46), (2, 7, 75), (30, 38, 88),
   (9, 14, 46), (2, 7, 75), (30, 38, 88), (30, 38, 88), (5, 6, 76), (5, 6, 76), (10, 12, 56),
   (10, 12, 56), (5, 6, 76), (27, 40, 98), (10, 12, 56), (5, 6, 76), (27, 40, 98), (27, 40, 98),
   (0, 16, 95), (3, 17, 85), (8, 15, 65), (8, 15, 65), (0, 16, 95), (3, 17, 85), (0, 16, 95),
   (8, 15, 65), (3, 17, 85), (0, 16, 95)]

@[expose] def P0GroupOn (P M : List Elt) : Prop :=
  P.Nodup ∧ P.length = 128 ∧ oneE ∈ P ∧ (∀ x ∈ P, x ∈ M) ∧ ∀ x ∈ P, ∀ y ∈ P, mulE x y ∈ P

@[expose] def NormalE16On (P A : List Elt) : Prop :=
  A.Nodup ∧ A.length = 16 ∧ (∀ x ∈ A, x ∈ P) ∧ (∀ x ∈ A, ∀ y ∈ A, mulE x y ∈ A) ∧
    (∀ x ∈ A, mulE x x = oneE) ∧ (∀ x ∈ A, ∀ y ∈ A, commE x y) ∧
    ∀ p ∈ P, ∀ q ∈ P, mulE p q = oneE → ∀ x ∈ A, mulE (mulE p x) q ∈ A

@[expose] def VFGroupsOn (P V F : List Elt) : Prop :=
  NormalE16On P V ∧ NormalE16On P F ∧ (∃ x ∈ F, x ∉ V) ∧ (V.filter fun x => x ∈ F).length = 4

@[expose] def OnlyPOn (IP V F : List Elt) : Prop :=
  ∀ a ∈ IP, a ∉ V → ∀ b ∈ IP, commE a b → ∀ c ∈ IP, commE a c → commE b c →
    ∀ d ∈ IP, commE a d → commE b d → commE c d → (span4 a b c d).Nodup →
      ∀ x ∈ span4 a b c d, x ∈ F

@[expose] def JGroupOn (P J : List Elt) : Prop :=
  J.Nodup ∧ J.length = 64 ∧ (∀ x ∈ J, x ∈ P) ∧ ∀ x ∈ J, ∀ y ∈ J, mulE x y ∈ J

@[expose] def CentPOn (P V F : List Elt) : Prop :=
  (∀ p ∈ P, (∀ x ∈ V, commE p x) → p ∈ V) ∧ ∀ p ∈ P, (∀ x ∈ F, commE p x) → p ∈ F

@[expose] def YChkOn (M P J : List Elt) : Prop :=
  yE ∈ M ∧ yE ≠ oneE ∧ mulE yE (mulE yE yE) = oneE ∧
    (∀ j ∈ J, mulE (mulE yE j) (mulE yE yE) ∈ J) ∧ (∀ j ∈ J, commE yE j → j = oneE) ∧
    sE ∈ P ∧ sE ∉ J ∧ mulE sE sE = oneE ∧ mulE (mulE sE yE) sE = mulE yE yE ∧
    ∀ p ∈ P, p ∈ J ∨ mulE sE p ∈ J

@[expose] def RankChkOn (IM : List Elt) (W : List (Elt × Elt × Elt × Elt)) : Prop :=
  (∀ s ∈ IM, ∃ w ∈ W, w.1 = s) ∧
    ∀ w ∈ W, w.2.1 ∈ IM ∧ w.2.2.1 ∈ IM ∧ w.2.2.2 ∈ IM ∧ commE w.1 w.2.1 ∧
      commE w.1 w.2.2.1 ∧ commE w.1 w.2.2.2 ∧ commE w.2.1 w.2.2.1 ∧ commE w.2.1 w.2.2.2 ∧
      commE w.2.2.1 w.2.2.2 ∧ (span4 w.1 w.2.1 w.2.2.1 w.2.2.2).Nodup

instance (P M : List Elt) : Decidable (P0GroupOn P M) := by unfold P0GroupOn; infer_instance
instance (P A : List Elt) : Decidable (NormalE16On P A) := by unfold NormalE16On; infer_instance
instance (P V F : List Elt) : Decidable (VFGroupsOn P V F) := by unfold VFGroupsOn; infer_instance
instance (IP V F : List Elt) : Decidable (OnlyPOn IP V F) := by unfold OnlyPOn; infer_instance
instance (P J : List Elt) : Decidable (JGroupOn P J) := by unfold JGroupOn; infer_instance
instance (P V F : List Elt) : Decidable (CentPOn P V F) := by unfold CentPOn; infer_instance
instance (M P J : List Elt) : Decidable (YChkOn M P J) := by unfold YChkOn; infer_instance
instance (IM : List Elt) (W : List (Elt × Elt × Elt × Elt)) : Decidable (RankChkOn IM W) := by
  unfold RankChkOn; infer_instance

end Certificates.T84PCheck
