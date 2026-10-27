module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryCfg
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryOdd
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryU4Arith
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryU4Outer
public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace HeringUnitary

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
  {haN : a ∈ Subgroup.normalizer (L : Set G)} {m : ℕ}

theorem false_of_projSU_four
    (c : UCfg L a haN m) {n : ℕ} (hn : 1 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 n) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := thetaQuotMulAut L (compAction L ⟨a, haN⟩) with hαdef
  set β : MulAut (projSU 4 2 n) := MulAut.congr φ α with hβdef
  have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, c.cube, map_one]
  have hβ1 : β ≠ 1 := fun h => c.ne_one ((MulAut.congr φ).injective (h.trans (map_one _).symm))
  set J : Subgroup (projSU 4 2 n) := c.ι.range.map φ.toMonoidHom with hJdef
  have hfixeq : Item426.fixSub β = (Item426.fixSub α).map φ.toMonoidHom :=
    (Item426.map_fixSub_eq φ α).symm
  have hιfix : c.ι.range ≤ Item426.fixSub α := by
    rintro _ ⟨u, rfl⟩
    exact c.fix u
  have hJC : J ≤ Item426.fixSub β := by
    rw [hfixeq]
    exact Subgroup.map_mono hιfix
  have hJ : IsComponent (J.subgroupOf (Item426.fixSub β)) := by
    refine Item419Res3.isComponent_subgroupOf_of_mulEquiv
      (A := Item426.fixSub α) (K := c.ι.range) (B := Item426.fixSub β) (K' := J)
      ((φ.subgroupMap (Item426.fixSub α)).trans (MulEquiv.subgroupCongr hfixeq.symm)) ?_ c.comp
    intro x
    change (x : L ⧸ aschbacherSolvableCore 3 L) ∈ c.ι.range ↔ φ x ∈ c.ι.range.map φ.toMonoidHom
    exact (Subgroup.mem_map_iff_mem φ.injective).symm
  have hcardJ : Nat.card J = Nat.card (projSU 3 2 m) := by
    rw [hJdef, Subgroup.card_map_of_injective φ.injective]
    exact (Nat.card_congr (MonoidHom.ofInjective c.ι_inj).toEquiv).symm
  have hZJ : Subgroup.center J = ⊥ := by
    refine Sec21.Item223RankResProof.center_eq_bot_of_mulEquiv
      (((Subgroup.equivMapOfInjective c.ι.range φ.toMonoidHom φ.injective).symm).trans
        (MonoidHom.ofInjective c.ι_inj).symm) c.center_eq
  by_cases hin : IsInnerAut β
  · obtain ⟨x, hx⟩ := hin
    rcases Nat.even_or_odd n with hne | hno
    ·
      have hαin : α ∈ (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range :=
        (isInnerAut_congr φ α).mp ⟨x, hx⟩
      exact c.false_of_inner hαin (Sec4.quotientCenterCongr φ)
        (pRank_projSU_four_le_two (by norm_num) hn (Sec21.two_pow_mod_three_of_even hne))
    ·
      have hx3 : x ^ 3 = 1 := by
        have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow, hx, hβ3]
        have h2 : x ^ 3 ∈ Subgroup.center (projSU 4 2 n) := by
          rw [Subgroup.mem_center_iff]
          intro y
          have := congrArg (fun γ : MulAut (projSU 4 2 n) => γ y) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc y * x ^ 3 = x ^ 3 * y * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
            _ = x ^ 3 * y := by group
        rwa [Item419Res3.center_projSU_four_eq_bot hn, Subgroup.mem_bot] at h2
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hβ1 (by rw [← hx, map_one])
      have hfix : Item426.fixSub β = Subgroup.centralizer ({x} : Set (projSU 4 2 n)) := by
        rw [← hx]
        exact Item419Res3.fixSub_conj_eq_centralizer x
      rw [hfix] at hJC hJ
      rcases Item419Res3.inner_case hno hx3 hx1 hJC hJ with hZ | hc
      · exact hZ hZJ
      · exact card_projSU_three_two_ne_sl_two c.odd hn (hcardJ ▸ hc)
  · obtain ⟨k, hk, hc⟩ := outer_case_any hn hβ3 hin hJC hJ
    exact card_projSU_three_two_ne_unitarySU_four c.odd hk (hcardJ ▸ hc)

end HeringUnitary

end CFSG.RankThree.PartTwo.Sec4
