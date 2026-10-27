module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iHull
public import CFSG.RankThree.PartTwo.Sec21.Hering233iExc
public import CFSG.RankThree.PartTwo.Sec21.Hering233iExcModel
public import CFSG.RankThree.PartTwo.Sec21.Hering233iComp
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartTwo.Sec21.Item233Skeleton
public import CFSG.RankThree.PartTwo.Sec21.Hering233iExcCent
public import CFSG.RankThree.PartTwo.Sec21.Hering233iStatements
public import CFSG.RankThree.PartTwo.Sec21.HeringHullChain4
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofHull
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open Hering233i Item233One

variable {G : Type} [Group G]

theorem item233One_at_of_quasisimple [Finite G] (h223 : Item223Print) (h228 : Item228)
    (h231 : Item231) (h222 : Item222) (hKW : KOfWellDefinedAll) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hK : Item233KLeComponent) (hZ : Item233ZGen) {A E U : Subgroup G}
    {c : G} {L : Subgroup G} (hpair : Sec21Pair G A E U c L) {B : Subgroup G} (hBA : B ≤ A)
    (hB3 : Nat.card B = 3)
    (X : Subgroup (iGroup A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G))
    (hX : CFSG.IsComponent X)
    (hq : ∀ X₀ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)),
      X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype ≤ X₀ →
        CFSG.IsQuasisimple X₀) :
    X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype ∈
      thetaComponentsIn (Subgroup.centralizer (B : Set G)) := by
  have hG : TheoremFourHyp G := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAn := Sec6.exists_card_eq_of_mem_partTwoF hpair.mem_S.1
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB3
    omega
  obtain ⟨φ, hφ, hKX⟩ := hK G A E U c L hpair B hBA hB3 X hX
  have hX'H : X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype ≤
      Subgroup.centralizer (B : Set G) :=
    (Subgroup.map_subtype_le X).trans inf_le_right
  have hKB : kOf A φ ≤ Subgroup.centralizer (B : Set G) := hKX.trans hX'H
  obtain ⟨X₀, hX₀, hKX₀⟩ := exists_mem_thetaComponentsIn_kOf_le h48 h222 hpair
    (hKW G A E U c L hpair) hBA hB1 hφ hKB
  obtain ⟨n, hn, ⟨eK⟩⟩ := exists_two_le_mulEquiv_kOf h222 hpair hφ
  have hXX₀ : X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype ≤ X₀ := by
    by_contra hle
    have hcomm := (le_or_commute_inf hX hX₀).resolve_left hle
    exact not_forall_commute_of_mulEquiv ⟨eK⟩ (fun x hx y hy =>
      hcomm x (hKX hx) y ⟨hKX₀ hy, kOf_le_iGroup hφ hy⟩)
  have hq' : CFSG.IsQuasisimple X₀ := hq X₀ hX₀ hXX₀
  obtain ⟨b, hbA, hb1, hXb⟩ : ∃ b ∈ A, b ≠ 1 ∧ X₀ ∈ thetaComponentsAt 3 b := by
    obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
    have hb1 : b ≠ 1 := fun h => hb' (Subtype.ext h)
    refine ⟨b, hBA hbB, hb1, ?_⟩
    rw [thetaComponentsAt_eq_thetaComponentsIn, ← Sec6.centralizer_zpowers_eq,
      ← eq_zpowers_of_card_three hB3 hbB hb1]
    exact hX₀
  have hX₀A : X₀ ∈ thetaComponentFamily 3 A := mem_thetaComponentFamily_iff.mpr ⟨b, hbA, hb1, hXb⟩
  obtain ⟨Z, hZ', hX₀Z⟩ := HeringHull.exists_mem_lStar_le h45 h48 hG hAe hAn {X₀}
    (fun P hP => by
      rw [Set.mem_singleton_iff] at hP
      subst hP
      exact ⟨hq', Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hbA hb1 P hXb⟩)
    hX₀A (fun P hP => by rw [Set.mem_singleton_iff] at hP; exact hP ▸ le_rfl)
  have hX₀Z' : X₀ ≤ Z := hX₀Z X₀ rfl
  have hconc := h231 G A E U c L hpair
  have hKZ : kOf A φ ≤ Z := hKX₀.trans hX₀Z'
  have h4 : Nat.card A = 3 ^ 4 → Item223OneConcl A φ Z := fun hA =>
    (h223 G A E U c L hpair hA φ hφ φ hφ).1 Z hZ' hKZ
  have h3 : Nat.card A = 3 ^ 3 → ∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z :=
    fun hA ψ hψ hne => (h228 G A E U c L hpair hA φ hφ ψ hψ hne).1 Z hZ' hKZ
  have hZI : Z ≤ iGroup A :=
    (hZ G A E U c L hpair hconc φ hφ Z hZ' hKZ h4 h3).trans (iSup_dStar_starOf_le_iGroup A Z)
  exact mem_thetaComponentsIn_of_le hX hX₀ (hX₀Z'.trans hZI) hXX₀

theorem quasisimple_of_e16_at [Finite G] (h222 : Item222)
    (hKW : KOfWellDefinedAll) (h45 : Sec4.Item4_5) (h44 : Sec4.Item4_4)
    (hK : Item233KLeComponent) {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (hpair : Sec21Pair G A E U c L) {B : Subgroup G} (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (X : Subgroup (iGroup A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G))
    (hX : CFSG.IsComponent X) {E₁ : Subgroup G} (hE₁ab : IsElemAbelian 2 E₁)
    (hE₁card : Nat.card E₁ = 2 ^ 4) (hE₁B : E₁ ≤ Subgroup.normalizer (B : Set G))
    (hE₁X : E₁ ≤ Subgroup.normalizer
      ((X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype : Subgroup G) : Set G))
    {X₀ : Subgroup G} (hX₀ : X₀ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hXX₀ : X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype ≤ X₀) :
    CFSG.IsQuasisimple X₀ := by
  have hG : TheoremFourHyp G := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB3
    omega
  obtain ⟨φ, hφ, hKX⟩ := hK G A E U c L hpair B hBA hB3 X hX
  have hKX₀ : kOf A φ ≤ X₀ := hKX.trans hXX₀
  obtain ⟨n, hn, ⟨eK⟩⟩ := exists_two_le_mulEquiv_kOf h222 hpair hφ
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1 : b ≠ 1 := fun h => hb' (Subtype.ext h)
  have hBb : B = Subgroup.zpowers b := eq_zpowers_of_card_three hB3 hbB hb1
  have hbA : b ∈ A := hBA hbB
  have hX₀b : X₀ ∈ thetaComponentsAt 3 b := by
    rw [thetaComponentsAt_eq_thetaComponentsIn, ← Sec6.centralizer_zpowers_eq, ← hBb]
    exact hX₀
  have hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hbA hb1 X₀ hX₀b
  have hE₁X₀ : E₁ ≤ Subgroup.normalizer (X₀ : Set G) := by
    intro g hg
    have hX₀g := map_conj_mem_thetaComponentsIn_of_mem_normalizer hB3 (hE₁B hg) hX₀
    have hKbot : kOf A φ ≠ ⊥ := by
      intro h
      obtain ⟨a, b', hab⟩ := exists_not_commute_of_mulEquiv_projSL eK
      apply hab
      have ha : (a : G) = 1 := Subgroup.mem_bot.mp (h ▸ a.2)
      have hb : (b' : G) = 1 := Subgroup.mem_bot.mp (h ▸ b'.2)
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb])
    have heq : X₀.map (MulAut.conj g).toMonoidHom = X₀ := by
      refine Sec6.eq_of_mem_thetaComponentsIn_of_le hX₀g hX₀
        (isPerfect_of_mulEquiv_projSL hn eK) hKbot ?_ hKX₀
      intro p hp
      refine ⟨g⁻¹ * p * g, hXX₀ ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (hE₁X (E₁.inv_mem hg)) p).mp (hKX hp)
      simpa using this
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  haveI : IsSimpleGroup (kOf A φ) := by
    haveI := isSimpleGroup_projSL_two hn
    exact eK.isSimpleGroup
  obtain ⟨u, v, hu1, hv1, huv, hu2, hv2⟩ := exists_two_involutions_projSL n (by omega)
  obtain ⟨-, z, -, hzK, hz3⟩ := exists_commOf_eq_zpowers_mem_kOf h222 hpair
    (hKW G A E U c L hpair) hφ
  have hz1 : (z : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz3
    omega
  obtain ⟨x, y, hxy⟩ := exists_not_commute_of_mulEquiv_projSL eK
  exact Hering233i.isQuasisimple_of_e16 h44 hG hpair.mem_S hbA hb1 hX₀b hAX₀ hKX₀
    ⟨x, x.2, y, y.2, fun h => hxy (Subtype.ext h)⟩ (u := (eK.symm u : G))
    (v := (eK.symm v : G)) (eK.symm u).2 (eK.symm v).2
    (fun h => hu1 (by simpa using congrArg eK (Subtype.ext h : eK.symm u = 1)))
    (fun h => hv1 (by simpa using congrArg eK (Subtype.ext h : eK.symm v = 1)))
    (fun h => huv (eK.symm.injective (Subtype.ext h)))
    (by rw [← Subgroup.coe_mul, ← map_mul, hu2, map_one, Subgroup.coe_one])
    (by rw [← Subgroup.coe_mul, ← map_mul, hv2, map_one, Subgroup.coe_one])
    z.2 hzK hz1 (fun a b => (hE₁ab.1.is_comm.comm a b)) hE₁ab.2 hE₁card hE₁X₀

theorem item233ComponentsOne_of_e16' (h223 : Item223Print)
    (h228 : Item228) (h231 : Item231) (h232 : Item232) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h44 : Sec4.Item4_4)
    (hK : Item233KLeComponent) (hZ : Item233ZGen) (hE16 : TerminalE16)
    (hL44 : L44ExceptionModel) : Item233ComponentsOne := by
  intro G _ _ A E U c L hpair B hBA hB3 X hX
  have hG : TheoremFourHyp G := hpair.standing.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAI : A ≤ iGroup A := (h232 G A E U c L hpair).1
  have hterm := terminal_of_item231Concl (h231 G A E U c L hpair)
  have key : ∀ B' : Subgroup G, B' ≤ A → Nat.card B' = 3 → ExcFree (iGroup A) B' →
      ∀ X' : Subgroup (iGroup A ⊓ Subgroup.centralizer (B' : Set G) : Subgroup G),
        CFSG.IsComponent X' → X'.map (iGroup A ⊓ Subgroup.centralizer (B' : Set G)).subtype ∈
          thetaComponentsIn (Subgroup.centralizer (B' : Set G)) := by
    intro B' hB'A hB'3 hfree X' hX'
    refine item233One_at_of_quasisimple h223 h228 h231 h222 hKW h45 h48 hK hZ hpair hB'A hB'3 X'
      hX' ?_
    rcases hE16 G (iGroup A) A hAI hAe hterm B' hB'A hB'3 X' hX' with
      ⟨E₁, -, hE₁ab, hE₁card, hE₁B, hE₁X⟩ | ⟨-, -, hu, h60⟩
    · exact fun X₀ hX₀ hXX₀ => quasisimple_of_e16_at h222 hKW h45 h44 hK hpair hB'A hB'3 X' hX'
        hE₁ab hE₁card hE₁B hE₁X hX₀ hXX₀
    · exact absurd ⟨hu, h60⟩ (hfree X' hX')
  rcases hE16 G (iGroup A) A hAI hAe hterm B hBA hB3 X hX with
    ⟨E₁, -, hE₁ab, hE₁card, hE₁B, hE₁X⟩ | ⟨hI44, hA27, hu, h60⟩
  · exact item233One_at_of_quasisimple h223 h228 h231 h222 hKW h45 h48 hK hZ hpair hBA hB3 X hX
      (fun X₀ hX₀ hXX₀ => quasisimple_of_e16_at h222 hKW h45 h44 hK hpair hBA hB3 X hX hE₁ab
        hE₁card hE₁B hE₁X hX₀ hXX₀)
  ·
    obtain ⟨b, a, b', c₃, c₄, w, X', hP⟩ := hL44 G (iGroup A) A hAI hAe hI44 hA27 B hBA hB3 X
      hX hu h60
    have hA27' : Nat.card A = 27 := by rw [hA27]; norm_num
    have hii : ∀ h : G, h ∈ A → h ≠ 1 → ExcFree (iGroup A) (Subgroup.zpowers h) →
        Subgroup.centralizer ((Subgroup.zpowers h : Subgroup G) : Set G) ≤
          Subgroup.normalizer (layerCent (iGroup A) (Subgroup.zpowers h) : Set G) := by
      intro h hhA hh1 hfree
      have hh3 : Nat.card (Subgroup.zpowers h) = 3 := by
        rw [Nat.card_zpowers]
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact orderOf_eq_prime (by simpa using hAe.2 h hhA) hh1
      exact item233Components_at h45 h232 hpair (Subgroup.zpowers_le.mpr hhA) hh3
        (key _ (Subgroup.zpowers_le.mpr hhA) hh3 hfree)
    have hBb := hP.hBb
    have hX₀b : ∀ X₀ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)),
        X₀ ∈ thetaComponentsAt 3 b := by
      intro X₀ hX₀
      rw [thetaComponentsAt_eq_thetaComponentsIn, ← Sec6.centralizer_zpowers_eq, ← hBb]
      exact hX₀
    refine item233One_at_of_quasisimple h223 h228 h231 h222 hKW h45 h48 hK hZ hpair hBA hB3 X hX
      (fun X₀ hX₀ hXX₀ => ?_)
    have hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set G) :=
      Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hP.hbA hP.hb1 X₀ (hX₀b X₀ hX₀)
    have hX₀C : X₀ ≤ Subgroup.centralizer ({b} : Set G) :=
      Sec6.le_centralizer_of_mem_thetaComponentsAt (hX₀b X₀ hX₀)
    have hdb : ∀ d ∈ X₀, d * b = b * d := fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.mp (hX₀C hd)
    have hw2' : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rw [hP.hw2] at this
      simpa [sq] using this
    have hq4 : ∀ q : ℕ, q.Prime → 3 < q → 4 < q := fun q hq hq3 => by
      rcases Nat.lt_or_ge 4 q with h | h
      · exact h
      · have : q = 4 := by omega
        subst this
        norm_num at hq
    haveI := hP.hX'simple
    exact isQuasisimple_of_exception h44 hG hpair.mem_S hBA hB3 hBb hP.hbA hP.hb1 (hX₀b X₀ hX₀)
      hAX₀ hA27' hXX₀ hP.eX hP.hXw hP.hw2 hP.haA hP.haX hP.ha1 hP.hcover
      (fun q hq hq3 d hd hdq hdb' => by
        have hdY := hii b' hP.hb'A hP.hb'1 hP.hfree₁ (mem_centralizer_zpowers_of_mul_eq hdb')
        have hdX' := mem_normalizer_of_normalClosure hP.hX'Y₁ hP.hX'N hP.hbX' hP.hb1 hdY
          (hdb d hd)
        exact commute_of_invSet hdX' (hdb d hd) hq (hq4 q hq hq3) hdq hP.hcount'
          ⟨hP.hwX', hw2', hP.hwb⟩)
      (fun q hq hq3 d hd hdq hdc₃ => by
        have hdY := hii c₃ hP.hc₃A hP.hc₃1 hP.hfree₃ (mem_centralizer_zpowers_of_mul_eq hdc₃)
        exact commute_of_invSet hdY (hdb d hd) hq (hq4 q hq hq3) hdq hP.hcount₃
          ⟨hP.hX'Y₃ hP.hwX', hw2', hP.hwb⟩)
      (fun q hq hq3 d hd hdq hdc₄ => by
        have hdY := hii c₄ hP.hc₄A hP.hc₄1 hP.hfree₄ (mem_centralizer_zpowers_of_mul_eq hdc₄)
        exact commute_of_invSet hdY (hdb d hd) hq (hq4 q hq hq3) hdq hP.hcount₄
          ⟨hP.hX'Y₄ hP.hwX', hw2', hP.hwb⟩)

end CFSG.RankThree.PartTwo.Sec21
