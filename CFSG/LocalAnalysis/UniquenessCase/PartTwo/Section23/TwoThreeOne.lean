module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneStatement
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneWeak
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rHpEqMul
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace S231

theorem eq_mul_normalizers {V S X : Subgroup G} (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S X)
    (hF : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 X ∨ Group.IsSolvable ↥X)
    (h1 : 1 < E3.sParam hV) :
    (X : Set G) = ((normalizer ((E3.wClos V 1 S ⊓ centralizer (E3.wClos V 1 S : Set G) :
        Subgroup G) : Set G) ⊓ X : Subgroup G) : Set G) *
      ((normalizer (E3.wClos V 0 S : Set G) ⊓ X : Subgroup G) : Set G) := by
  have hlt : 0 + 1 < E3.sParam hV := by simpa using h1
  have h := uc22s21rhp_eq_mul_of_or hV hS (i := 0) (j := 1) le_rfl hF hlt
  have hZW : E3.wClos V 1 S ⊓ centralizer (E3.wClos V 1 S : Set G) ≤
      E3.cClos V (0 + 1) S := by
    rw [E3.cClos]
    exact le_inf (inf_le_left.trans (uc22p22ta_wClos_le V 1 S)) inf_le_right
  apply Set.Subset.antisymm
  · intro x hx
    rw [h] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a, ⟨?_, ha.1⟩, b, ⟨hb.2, hb.1⟩, rfl⟩
    exact Subgroup.centralizer_le_normalizer _
      ((Subgroup.centralizer_le hZW) ha.2)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact X.mul_mem ha.2 hb.2

theorem mBar_le_aBar_add_one {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h111 : W3Thm111 G) (h2122 : S21_22Use D Ch) (h1930 : H1930 D) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVle : V ≤ c.V) (hVeq : V = conjClosure c.N (V ⊓ D.Z))
    (hVne : V ≠ ⊥) (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z))) :
    mBar c.N ⊥ V hV ≤ aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hle
  push Not at hle
  have ha : 1 ≤ aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW :=
    S231.one_le_aBar c hVle hVeq hVne hW
  have hm : 2 < mBar c.N ⊥ V hV := by omega
  have hs : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + 1 < E3.sParam hV :=
    S231.lt_sParam c h111 hV hVle hVeq hVne hm hle
  have hs0 : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW < E3.sParam hV := by
    omega
  have h1 : 1 < E3.sParam hV := by omega
  have hrk : 1 < rk ↥V := by
    have h2 := S231.two_lt_rk c hV hVeq hm
    omega
  have hH₁ : normalizer ((E3.wClos V 1 D.T ⊓ centralizer (E3.wClos V 1 D.T : Set G) :
      Subgroup G) : Set G) ∈ hSet D.T D.M :=
    S231.normalizer_center_wClos_one_mem_hSet c hV hVle hVeq hVne hW hs hrk
  have hH₂ : normalizer (E3.wClos V 0 D.T : Set G) ∈ hSet D.T D.M :=
    S231.normalizer_wClos_zero_mem_hSet c hV hVle hVeq hVne hW hs0
  have hL0 : c.L0 ≤ normalizer ((E3.wClos V 1 D.T ⊓ centralizer
      (E3.wClos V 1 D.T : Set G) : Subgroup G) : Set G) ⊓
        normalizer (E3.wClos V 0 D.T : Set G) := by
    refine le_inf ?_ ?_
    · exact le_sup_left.trans (S231.sup_le_normalizer_center_wClos c hV hVeq hVne hW
        (i := 1) hs)
    · exact le_sup_left.trans (S231.sup_le_normalizer_wClos c hV hVeq hVne hW
        (i := 0) (by simpa using hs0))
  have hle' : normalizer ((E3.wClos V 1 D.T ⊓ centralizer (E3.wClos V 1 D.T : Set G) :
      Subgroup G) : Set G) ⊓ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    h2122 h1930 c.toCtx21 _ hH₁ _ hH₂ hL0 fun X _ hTX hF =>
      S231.eq_mul_normalizers hV (PartTwo.TwelveShort.isSylowIn_of_le D hTX) hF h1
  exact Ctx23L.L0_not_le_M c (hL0.trans hle')

end S231

theorem s23_1A_of (D : Data G) (Ch : Choice2011 G) (hB : S23_1ABound D Ch) (h111 : W3Thm111 G)
    (h2122 : S21_22Use D Ch) : S23_1A D Ch := by
  intro h1930 c V hV hVle hVeq hVne
  exact ⟨S231.isElemAbelian_W c hV hVeq,
    S231.mBar_le_aBar_add_one c h111 h2122 h1930 hV hVle hVeq hVne _,
    hB h1930 c V hVle hVeq hVne _⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
