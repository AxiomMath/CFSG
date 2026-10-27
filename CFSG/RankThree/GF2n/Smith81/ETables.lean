module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

@[expose] def EPosEq (Z B' C' : Subgroup G) : Prop := C' ⊔ Z = B' ⊔ Z

@[expose] def EPosQ (Z B' C' : Subgroup G) : Prop := C' ⊔ Z ≠ B' ⊔ Z ∧ C' ≤ QB B'

@[expose] def EPosM (B' C' : Subgroup G) : Prop :=
  C' ≤ Subgroup.normalizer (B' : Set G) ∧ ¬ C' ≤ QB B'

@[expose] def EPosOpp (B' C' : Subgroup G) : Prop := ¬ C' ≤ Subgroup.normalizer (B' : Set G)

section Positions

variable [Finite G] {M Q Z B' C' : Subgroup G}

theorem EPosEq.le_QB (hB : Ctx M Q Z B') (h : EPosEq Z B' C') : C' ≤ QB B' := by
  have hZ : Z ≤ QB B' := hB.Z_le_QB.1
  have hB' : B' ≤ QB B' := (IsZConjugate.le_QB_self hB.hyp hB.conj).trans le_rfl
  calc C' ≤ C' ⊔ Z := le_sup_left
    _ = B' ⊔ Z := h
    _ ≤ QB B' := sup_le hB' hZ

end Positions

section Orders

variable [Finite G]

theorem card_LB_of_ctx (h34 : Stroth34Statement) {M Q Z B' : Subgroup G} (hB' : Ctx M Q Z B')
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B')) (hgen : GenByB M Q B') :
    Nat.card ↥(LB M Q B') = Nat.card Q * Nat.card Z ^ (n - 1) ∧
      Nat.card ↥(Q ⊓ QB B') = Nat.card Z ^ (n + 1) :=
  (stroth_3_5 h34 hB' hw hn hno hgen).2.2

end Orders

end CFSG.RankThree.GF2n.Smith81
