module

public import CFSG.RankThree.GF2n.Stroth80.Sec115Count
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Quasithin.EmptyFaithful.S146xB2Aut
import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddU3Rank

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.sixteen_le_card_xbarModConjAct_range (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {y : G}
    (hy : IsLBTorus M Q Z B y) : 16 ≤ Nat.card (xbarModConjAct hc).range :=
  calc 16 = 4 ^ 2 := by norm_num
    _ ≤ Nat.card Z ^ 2 := Nat.pow_le_pow_left hc.hyp.q4 2
    _ ≤ _ := hc.card_Z_sq_le_card_xbarModConjAct_range hw hn ha2 hy

theorem Ctx.isEmpty_xbarMod_mulEquiv_alt_six (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {y : G} (hy : IsLBTorus M Q Z B y) :
    IsEmpty (XbarMod M Q Z B ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  have h8 := CFSG.Quasithin.card_le_eight_of_alt_six e hc.isElemAbelian_xbarModConjAct_range
  have h16 := hc.sixteen_le_card_xbarModConjAct_range hw hn ha2 hy
  omega

open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent in
theorem Ctx.not_lieModel_xbarMod_psu_three_three (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {y : G}
    (hy : IsLBTorus M Q Z B y) : ¬ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 3 1 := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := hc.isElemAbelian_xbarModConjAct_range
  have h8 := card_elemAbelian_mulAut_of_model_U3 (p := 3) (by norm_num)
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
    (xbarModConjAct hc).range (fun _ ha _ hb => hA.comm ha hb) (fun _ ha => hA.mul_self_eq_one ha)
  have h16 := hc.sixteen_le_card_xbarModConjAct_range hw hn ha2 hy
  omega

end CFSG.RankThree.GF2n.Stroth80
