module

public import CFSG.Walter.J1Recog.Pres
public import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
public import CFSG.Sporadic.Bridge.J1

public section

namespace CFSG.Walter.J1Recog

open Word CFSG.ProperTwoGeneratedCore

@[expose] def matT : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![10, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 10, 0, 0, 0, 0;
     0, 0, 0, 10, 0, 0, 0;
     0, 0, 0, 0, 10, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

@[expose] def matN : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0]

@[expose] def matNi : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0]

@[expose] def matM : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, 0]

@[expose] def matMi : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0]

@[expose] def matL : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![3, 9, 1, 1, 3, 1, 3;
     9, 1, 1, 3, 1, 3, 3;
     1, 1, 3, 1, 3, 3, 9;
     1, 3, 1, 3, 3, 9, 1;
     3, 1, 3, 3, 9, 1, 1;
     1, 3, 3, 9, 1, 1, 3;
     3, 3, 9, 1, 1, 3, 1]

@[expose] def matU : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![8, 0, 8, 9, 1, 0, 0;
     0, 5, 0, 0, 0, 9, 7;
     8, 0, 9, 8, 1, 0, 0;
     9, 0, 8, 8, 1, 0, 0;
     1, 0, 1, 1, 8, 0, 0;
     0, 9, 0, 0, 0, 7, 5;
     0, 7, 0, 0, 0, 5, 9]

@[expose] def mat : Fin 5 → Matrix (Fin 7) (Fin 7) (ZMod 11) := ![matT, matN, matM, matL, matU]

@[expose] def matInv : Fin 5 → Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  ![matT, matNi, matMi, matL, matU]

theorem mat_mul_matInv : ∀ i, mat i * matInv i = 1 := by decide +kernel

theorem matInv_mul_mat : ∀ i, matInv i * mat i = 1 := by decide +kernel

@[expose] def unit (i : Fin 5) : GL (Fin 7) (ZMod 11) :=
  ⟨mat i, matInv i, mat_mul_matInv i, matInv_mul_mat i⟩

@[expose] def matWord (w : Word 5) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  (w.map fun l => if l.2 then mat l.1 else matInv l.1).prod

theorem val_ev_unit (w : Word 5) :
    ((ev unit w : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)) = matWord w := by
  induction w with
  | nil => simp [matWord]
  | cons l w ih =>
    have hm : matWord (l :: w) = (if l.2 then mat l.1 else matInv l.1) * matWord w := by
      simp only [matWord, List.map_cons, List.prod_cons]
    rw [hm, show l :: w = [l] ++ w from rfl, ev_append, Units.val_mul, ih]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b with
    | true =>
      rw [show ([(i, true)] : Word 5) = gen i from rfl, ev_gen]
      rfl
    | false =>
      rw [show ([(i, false)] : Word 5) = Word.inv (gen i) from rfl, ev_inv, ev_gen]
      rfl

set_option maxRecDepth 4000 in
theorem matWord_rels : ∀ w ∈ rels .O1a, matWord w = 1 := by
  decide +kernel

theorem ev_unit_rels : ∀ w ∈ rels .O1a, ev unit w = 1 := fun w hw =>
  Units.ext (by rw [val_ev_unit, matWord_rels w hw, Units.val_one])

noncomputable def toMat : Pres .O1a →* GL (Fin 7) (ZMod 11) :=
  lift (rels .O1a) unit ev_unit_rels

@[expose] def wordA : Word 5 :=
  Word.inv wn ++ wm ++ Word.inv wn ++ Word.inv wt ++ Word.pow (wn ++ Word.inv wu) 2 ++
    Word.inv ws ++ Word.inv wn ++ wt ++ Word.inv wn ++ wu

@[expose] def wordB : Word 5 :=
  Word.inv wu ++ Word.inv ws ++ wn ++ Word.inv wt ++ Word.inv ws ++ Word.inv wt ++
    Word.inv wu ++ Word.inv wn ++ wt ++ Word.inv wm ++ ws ++ wt ++ wu ++ wn ++ wu

theorem matWord_wordA : matWord wordA = CFSG.Open.walterJ1GenA := by
  decide +kernel

theorem matWord_wordB : matWord wordB = CFSG.Open.walterJ1GenB := by
  decide +kernel

theorem toMat_ev (w : Word 5) : toMat (ev PresentedGroup.of w) = ev unit w := by
  rw [map_ev]
  congr 1
  funext i
  exact lift_of _ _ _ i

theorem walterJ1_le_range : CFSG.Open.walterJ1 ≤ toMat.range := by
  rw [CFSG.Open.walterJ1, Subgroup.closure_le]
  rintro g (hg | hg)
  · refine ⟨ev PresentedGroup.of wordA, ?_⟩
    rw [toMat_ev]
    exact Units.ext (by rw [val_ev_unit, matWord_wordA, hg])
  · refine ⟨ev PresentedGroup.of wordB, ?_⟩
    rw [toMat_ev]
    exact Units.ext (by rw [val_ev_unit, matWord_wordB, hg])

theorem walterJ1GenA_eq : CFSG.Open.walterJ1GenA = j1_first_matrix := by
  decide +kernel

theorem walterJ1GenB_eq : CFSG.Open.walterJ1GenB = j1_second_matrix := by
  decide +kernel

theorem walterJ1_eq : CFSG.Open.walterJ1 = CFSG.Sporadic.Bridge.J1.seedGroup := by
  rw [CFSG.Open.walterJ1, CFSG.Sporadic.Bridge.J1.seedGroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, walterJ1GenA_eq,
    walterJ1GenB_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem le_card_walterJ1 : 175560 ≤ Nat.card CFSG.Open.walterJ1 := by
  rw [walterJ1_eq]
  exact CFSG.Sporadic.Bridge.J1.le_card_native

end CFSG.Walter.J1Recog
