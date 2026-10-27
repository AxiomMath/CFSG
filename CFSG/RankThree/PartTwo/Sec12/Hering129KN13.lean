module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KN12
public import CFSG.RankThree.PartTwo.Sec12.Hering129KD1
public import CFSG.RankThree.PartTwo.Sec12.Hering129LD42
import CFSG.RankThree.PartTwo.Sec12.Hering129LRank
import CFSG.RankThree.PartTwo.Sec12.Hering129LTypEight
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEi
public import CFSG.RankThree.PartTwo.Sec12.Hering129KFix
public import CFSG.RankThree.PartTwo.Sec12.Hering129KSub
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY5
public import CFSG.RankThree.PartTwo.Sec12.Hering129KYa
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


theorem gap129EndENotD42_of (hN : Sec11.Item1134E27N) (hST : Sec21.Item1134E27ST)
    (h1 : Sec4.Item4_1LargePrime) (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus) :
    Gap129EndENotD42 := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb hxL Y hY hXY hNo h3 hD _ _ _ _ _ _ _ J _ _ hJ
    hbJ r hr hrm hqm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hst : PartTwoStanding G := hstd.toPartTwoStanding
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hFE : partTwoF G = partTwoE G := hstd.partTwoF_eq
  have hAF : A ∈ partTwoF G := hFE ▸ cfg.mem_E
  obtain ⟨hbA, haA, -⟩ := cfg.point_facts
  have hxA : x ∈ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA) hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  have hYle : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  obtain ⟨hcX, -, δ, -, hδ13, F, hFf, hFfin, hFcard, φK, hφK, hkerK⟩ :=
    exists_sl2_quotient_of_fix hTL hCen G A c L b a K S cfg q hq x hxD hxb
  obtain ⟨hq4, -, -⟩ := hCen.2 G A c L b a K S cfg q hq
  haveI : Finite F := Finite.of_fintype F
  haveI hqp : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hFcard]
    refine hq4.trans (Nat.le_self_pow ?_ _)
    rcases hδ13 with rfl | rfl <;> norm_num
  have hFpow : Nat.card F = q.p ^ (q.exponent * δ) := by
    rw [Nat.card_eq_fintype_card, hFcard, TauCeti.PrimePower.card_def, ← pow_mul]
  obtain ⟨eX⟩ := Hering129KYa.nonempty_quotTheta_equiv_projSL (p := q.p) (n := q.exponent * δ)
    hFpow hF4 φK hφK hkerK
  have hcY : c ∈ Y := hXY hcX
  have hYq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYx
  have hθ := theta_eq_pCore_of_typ129IIIcType hYq h3
  have hxY : x ∉ Y := not_mem_of_center_pCore_eq_bot hx3 hx1 hYle h3.2.2
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK
  have hXb : resCent K x ≤ Subgroup.centralizer ({b} : Set G) :=
    ((resCent_le K x).trans inf_le_left).trans hKb
  have hX : ∃ X : Subgroup G, X ≤ Y ∧ X ≤ Subgroup.centralizer ({b} : Set G) ∧
      Group.IsPerfect X ∧ (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set G))).IsSubnormal ∧
      c ∈ X ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n)) :=
    ⟨resCent K x, hXY, hXb, isPerfect_resCent K x,
      resCent_isSubnormal cfg.hK (M := Y ⊓ Subgroup.centralizer ({b} : Set G)) inf_le_right
        (inf_le_left.trans hYle) (le_inf hXY hXb),
      hcX, q.p, q.exponent * δ, hqp, hFpow ▸ hF4, ⟨eX⟩⟩
  have hkind : ∀ e ∈ A, ¬ KFacts.InducesStdKind Y e .field ∧
      ¬ KFacts.InducesStdKind Y e .graphField := by
    intro e heA
    obtain ⟨h8a, h8b⟩ := notEight_of_typ129IIIcType hθ h3
    exact not_stdKind_of_notEight hN hST hst hAF cfg.mem_S hFE hA27 hxA hx1 hYx hAN hAC
      h8a h8b heA
  have hR2 : IsPGroup 2 (aschbacherSolvableCore 3 Y) := by
    rw [hθ]
    exact CFSG.pCore_isPGroup
  have ePC := QuotientGroup.quotientMulEquivOfEq hθ
  have hty : ∃ (p e : ℕ) (_ : Fact p.Prime),
      Sec4.IsoLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) p e := by
    obtain ⟨-, hty3, -⟩ := h3
    rcases hty3 with ⟨p, e, hp, hiso⟩ | ⟨r₀, hr₀, ⟨ee⟩⟩
    · refine ⟨p, e, hp, ?_⟩
      rcases hiso with ⟨hm1, ⟨f⟩⟩ | ⟨hm2, ⟨f⟩⟩
      · exact Or.inl ⟨hm1, ⟨ePC.trans f⟩⟩
      · exact Or.inr ⟨hm2, ⟨ePC.trans f⟩⟩
    · exfalso
      have hS4 : SectionFourHyp (Y ⧸ aschbacherSolvableCore 3 Y) :=
        sectionFourHyp_quot_of_mem_thetaComponentsAt h1 hstd.toTheoremFourHyp hx1 hYx
      have hp2 : r₀.p = 2 :=
        p_eq_two_of_sectionFourHyp_d4 hS4 (Or.inr ⟨rfl, hr₀, ⟨ePC.trans ee⟩⟩)
      have hlt : ¬ 4 ≤ r₀.card := fun h4 =>
        hNo r₀ 3 (Or.inr ⟨rfl, hr₀, ⟨ee⟩⟩) ⟨h4, by omega, fun _ => hp2⟩
      have hr₀2 : r₀.card = 2 := by
        have he := r₀.exponent_pos
        rw [TauCeti.PrimePower.card_def, hp2] at hlt ⊢
        rcases Nat.lt_or_ge r₀.exponent 2 with h | h
        · rw [show r₀.exponent = 1 by omega, pow_one]
        · exact absurd ((show 4 ≤ 2 ^ 2 by norm_num).trans
            (Nat.pow_le_pow_right (by norm_num) h)) hlt
      exact hD r₀ hr₀ hr₀2 ⟨ee⟩
  exact end_L3_of_config gap129HessL3Deg_holds cfg hq.1 hqm hxD hxb hxL hY hxY hcY hX hkind
    hty hR2 hJ hbJ hr hrm

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
