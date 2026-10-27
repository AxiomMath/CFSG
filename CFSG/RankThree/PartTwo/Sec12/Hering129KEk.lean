module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KEg
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEi
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEj
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY8
import CFSG.RankThree.PartTwo.Sec12.Hering129LRank
import CFSG.RankThree.PartTwo.Sec12.Hering129LTypEight
public import CFSG.RankThree.PartTwo.Sec12.Hering129KFix
public import CFSG.RankThree.PartTwo.Sec12.Hering129KSub
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY5
public import CFSG.RankThree.PartTwo.Sec12.Hering129KYa
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


theorem gap129ClaimEX_of_hess (hN : Sec11.Item1134E27N) (hST : Sec21.Item1134E27ST)
    (h1 : Sec4.Item4_1LargePrime) (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus)
    (hL3 : Gap129HessL3) (hD4 : Gap129HessD4) :
    Gap129ClaimEX := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb Y hY hXY h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hst : PartTwoStanding G := hstd.toPartTwoStanding
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hFE : partTwoF G = partTwoE G := hstd.partTwoF_eq
  have hAF : A ∈ partTwoF G := hFE ▸ cfg.mem_E
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  have hYle : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  have hAle : A ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy x hxA)
  have hKK := gap129KFKStrong_of_fix hTL hCen
  obtain ⟨hcX, -, -, -⟩ := hKK G A c L b a K S cfg ⟨q, hq⟩ x hxD hxb
  obtain ⟨-, -, δ, -, hδ13, F, hFf, hFfin, hFcard, φK, hφK, hkerK⟩ :=
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
  have hX4 : 4 ≤ q.p ^ (q.exponent * δ) := hFpow ▸ hF4
  have hcY : c ∈ Y := hXY hcX
  have hYp : Group.IsPerfect ↥Y := Sec6.isPerfect_of_mem_thetaComponentsAt hYx
  have hYq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYx
  have hθ := theta_eq_pCore_of_typ129IIIcType hYq h3
  have hxY : x ∉ Y := not_mem_of_center_pCore_eq_bot hx3 hx1 hYle h3.2.2
  obtain ⟨hgen, hbxc⟩ := cfg.gen_facts hxD hxb
  have hxc : ∀ w ∈ Y ⊔ A, x * w = w * x := fun w hw =>
    (Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hYle hAle) hw)).symm
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
      hcX, q.p, q.exponent * δ, hqp, hX4, ⟨eX⟩⟩
  have hkind : ∀ e ∈ A, ¬ KFacts.InducesStdKind Y e .field ∧
      ¬ KFacts.InducesStdKind Y e .graphField := by
    intro e heA
    obtain ⟨h8a, h8b⟩ := Hering129L.notEight_of_typ129IIIcType hθ h3
    exact not_stdKind_of_notEight hN hST hst hAF cfg.mem_S hFE hA27 hxA hx1 hYx hAN hAC
      h8a h8b heA
  have ePC := QuotientGroup.quotientMulEquivOfEq hθ
  have hty : (∃ (p e : ℕ) (_ : Fact p.Prime),
        Sec4.IsoLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) p e) ∨
      ∃ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid), r.p = 2 ∧
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) := by
    obtain ⟨-, hty3, -⟩ := h3
    rcases hty3 with ⟨p, e, hp, hiso⟩ | ⟨r, hr, ⟨ee⟩⟩
    · left
      refine ⟨p, e, hp, ?_⟩
      rcases hiso with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
      · exact Or.inl ⟨h1, ⟨ePC.trans f⟩⟩
      · exact Or.inr ⟨h2, ⟨ePC.trans f⟩⟩
    · right
      have hS4 : SectionFourHyp (Y ⧸ aschbacherSolvableCore 3 Y) :=
        Hering129L.sectionFourHyp_quot_of_mem_thetaComponentsAt h1 hstd.toTheoremFourHyp hx1 hYx
      have hGD : IsG2D4 (Y ⧸ aschbacherSolvableCore 3 Y) r 3 :=
        Or.inr ⟨rfl, hr, ⟨ePC.trans ee⟩⟩
      exact ⟨r, hr, Hering129L.p_eq_two_of_sectionFourHyp_d4 hS4 hGD, ⟨ePC.trans ee⟩⟩
  exact exists_E_of_hess_sub hL3 hD4 hAN hYp hYq hAe hA27 hgen hx1 hxc hxY hcY hbxc hAC hX
    hkind hty

end CFSG.RankThree.PartTwo.Sec12
