module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelComm

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))

theorem card_frobFixSub (hF : Fintype.card F = 2 ^ (2 * l)) :
    Nat.card ↥(frobFixSub (F := F) l) = 2 ^ l := by
  have hl : 1 ≤ l := one_le_of_card hF
  have e : ↥(frobFixSub (F := F) l) ≃ {x : F // x ^ 2 ^ l = x} :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_frob_fixed (F := F) hl hF)

theorem card_herm1101 (hF : Fintype.card F = 2 ^ (2 * l)) :
    Nat.card ↥(herm1101 l F) = 2 ^ l := by
  have e : ↥(herm1101 l F) ≃ ↥(frobFixSub (F := F) l) :=
    { toFun := fun X => ⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, (hermA_00 (a := l) X.1)⟩
      invFun := fun a => ⟨hermDiag l hF a a.2, hermDiag_mem_herm1101 (hF := hF) a a.2⟩
      left_inv := fun X => by
        apply Subtype.ext
        exact (eq_hermDiag_of_mem_herm1101 (hF := hF) X.1 X.2).symm
      right_inv := fun a => by
        apply Subtype.ext
        change (hermDiag l hF (a : F) (show (a : F) ^ 2 ^ l = a from a.2) :
          Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F)
        rw [hermDiag_coe]
        rfl }
  rw [Nat.card_congr e, card_frobFixSub (hF := hF)]

theorem card_herm11 (hF : Fintype.card F = 2 ^ (2 * l)) :
    Nat.card ↥(herm11 l F) = 2 ^ (3 * l) := by
  have e : ↥(herm11 l F) ≃ ↥(frobFixSub (F := F) l) × F :=
    { toFun := fun X => (⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, (hermA_00 (a := l) X.1)⟩,
        (X : Matrix (Fin 2) (Fin 2) F) 0 1)
      invFun := fun p => ⟨hermDiag l hF p.1 (show (p.1 : F) ^ 2 ^ l = p.1 from p.1.2) + hermOff l hF p.2,
        (by rw [AddSubgroup.coe_add, Matrix.add_apply, hermDiag_coe, hermOff_coe]; simp :
          ((hermDiag l hF p.1 (show (p.1 : F) ^ 2 ^ l = p.1 from p.1.2) + hermOff l hF p.2 : ↥(hermA l F)) :
            Matrix (Fin 2) (Fin 2) F) 1 1 = 0)⟩
      left_inv := fun X => by
        apply Subtype.ext
        exact (eq_hermDiag_add_offdiag_of_herm11 (hF := hF) X.1 X.2).symm
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          change ((hermDiag l hF p.1 (show (p.1 : F) ^ 2 ^ l = p.1 from p.1.2) +
              hermOff l hF p.2 : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = (p.1 : F)
          rw [AddSubgroup.coe_add, Matrix.add_apply, hermDiag_coe, hermOff_coe]
          simp
        · change ((hermDiag l hF p.1 (show (p.1 : F) ^ 2 ^ l = p.1 from p.1.2) +
              hermOff l hF p.2 : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = p.2
          rw [AddSubgroup.coe_add, Matrix.add_apply, hermDiag_coe, hermOff_coe]
          simp }
  rw [Nat.card_congr e, Nat.card_prod, card_frobFixSub (hF := hF),
    Nat.card_eq_fintype_card, hF]
  rw [show 2 ^ l * 2 ^ (2 * l) = 2 ^ (3 * l) by rw [← pow_add]; ring_nf]

theorem card_fixedSub_upperSylow :
    Nat.card ↥(fixedSub (hermRep l hF) upperSylow) = 2 ^ l := by
  rw [fixedSub_upperSylow (hF := hF)]
  exact card_herm1101 (hF := hF)

theorem card_commSub_upperSylow :
    Nat.card ↥(commSub (hermRep l hF) upperSylow) = 2 ^ (3 * l) := by
  rw [commSub_upperSylow (hF := hF)]
  exact card_herm11 (hF := hF)

end CFSG.RankThree.GF2n.Tim81.Sec2
