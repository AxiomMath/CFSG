module

public import CFSG.RankThree.PartOne.KF.F128Lie

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix

theorem center_fixRes_eq_bot {T : Type} [Group T] {p : ℕ} {α : MulAut T} (hF : FixedFacts p α) :
    Subgroup.center ↥(fixRes α) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  apply Subtype.ext
  refine fixRes_centralizer_trivial hF (g := (z : T)) fun x hx => ?_
  have := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
  exact congrArg Subtype.val this

noncomputable def fixResEquivQuotient {T : Type} [Group T] {p : ℕ} {α : MulAut T}
    (hF : FixedFacts p α) : ↥(fixRes α) ≃* ↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α) :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_fixRes_eq_bot hF).symm)

end CFSG.RankThree.PartOne.K128
