module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

@[expose] def Item2130ChoiceNotU4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 →
      ¬ ∃ n : ℕ, Odd n ∧ Nonempty (L ≃* projSU 4 2 n)

@[expose] def Item2130ChoiceY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L U₀ : Subgroup G) (b : G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → U₀ ∈ fourGroupsMinus E →
      U₀ ≤ L → b ∈ A ⊓ L → b ≠ 1 → U₀ ≤ Subgroup.centralizer ({b} : Set G) →
        ∃ Y ∈ thetaComponentsAt 3 b, Y ∈ lZeroUnion A ∧
          U₀ ≤ Subgroup.normalizer (Y : Set G) ∧ ⁅Y, U₀⁆ = Y

namespace Item211Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isPGroup (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G) {b : G}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) {S : Subgroup G} (hS : IsPGroup 3 S)
    (hSC : S ≤ Subgroup.centralizer ({b} : Set G)) :
    ∀ Y ∈ thetaComponentsAt 3 b, S ≤ Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  have hC4 : SectionFourHyp C := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hb1)
  have hS' : IsPGroup 3 (S.subgroupOf C) := hS.comap_subtype
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcore : CFSG.pCore 3 C ≠ ⊥ := by
    set b' : C := ⟨b, hbC⟩
    have hb'3 : orderOf b' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hb3 hb1
    have hZn : (Subgroup.zpowers b').Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hgb : g * b' = b' * g := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have : g * b' ^ k * g⁻¹ = b' ^ k := by
        rw [(Commute.zpow_right hgb k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.zpow_mem_zpowers b' k
    have hZ3 : IsPGroup 3 (Subgroup.zpowers b') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb'3, pow_one])
    have hZle : Subgroup.zpowers b' ≤ CFSG.pCore 3 C := le_sSup ⟨hZn, hZ3⟩
    intro hbot
    have hb'1 : b' = 1 := by
      have := hZle (Subgroup.mem_zpowers b')
      rwa [hbot, Subgroup.mem_bot] at this
    exact hb1 (congrArg Subtype.val hb'1)
  intro Y hY
  obtain ⟨Y', hY', rfl⟩ := hY
  have hN := Sec6.item45_of_item4_5 h45 C hC4 (S.subgroupOf C) hS' (Or.inl hcore) Y' hY'
  intro a ha
  have haN : (⟨a, hSC ha⟩ : C) ∈ Subgroup.normalizer (Y' : Set C) :=
    hN (Subgroup.mem_subgroupOf.mpr ha)
  rw [Subgroup.mem_normalizer_iff] at haN ⊢
  intro x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨_, (haN x').mp hx', rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : G) = a * x * a⁻¹ := hyx
    have hxC : x ∈ C := by
      have hx' : x = a⁻¹ * (y : G) * a := by
        rw [hyx']
        group
      rw [hx']
      exact C.mul_mem (C.mul_mem (C.inv_mem (hSC ha)) y.2) (hSC ha)
    refine ⟨⟨x, hxC⟩, (haN ⟨x, hxC⟩).mpr ?_, rfl⟩
    have : (⟨a, hSC ha⟩ : C) * ⟨x, hxC⟩ * (⟨a, hSC ha⟩ : C)⁻¹ = y := Subtype.ext hyx'.symm
    rw [this]
    exact hy

theorem mem_thetaQuotCentralizer_of_le_centralizer {Y : Subgroup G} {b : G}
    (hYC : Y ≤ Subgroup.centralizer ({b} : Set G)) :
    b ∈ Sec4.thetaQuotCentralizer Y := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨?_, fun l hl => ?_⟩
  · refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYC hy)
  · have hbl : b * l = l * b := (Subgroup.mem_centralizer_singleton_iff.mp (hYC hl)).symm
    rw [hbl, mul_inv_cancel_right, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem barImage_eq_bot_of_le {Y X : Subgroup G} (hX : X ≤ Sec4.thetaQuotCentralizer Y) :
    Item211Res2Proof.barImage Y X = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨x, hxN⟩, hxX, rfl⟩
  obtain ⟨n, hn, hnx⟩ := hX (Subgroup.mem_subgroupOf.mp hxX)
  have e : n = ⟨x, hxN⟩ := Subtype.ext hnx
  rw [Subgroup.mem_bot, ← e]
  exact hn

end Item211Res3Proof

open Item211Res3Proof Item211Res2Proof

theorem item2130LocalChoice_of (h45 : Sec4.Item4_5) (h214 : Item214)
    (hU4 : Item2130ChoiceNotU4) (hY : Item2130ChoiceY) : Item2130LocalChoice := by
  intro G _ _ A E U c L hcfg h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair := hcfg.pair
  have hG := hpair.standing.toTheoremFourHyp
  obtain ⟨⟨hcE, -⟩, hc1, hLs, -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEA : E ≤ A := hpair.mem_E.2
  have hcA : c ∈ A := hEA hcE
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hLs
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hA27 : Nat.card A = 27 := by rw [hcfg.card_eq, h9]
  have hEeq : E = A :=
    Subgroup.eq_of_le_of_card_ge hEA (by rw [hA27, hpair.mem_E.1.2.1])
  have hcB : c ∉ A ⊓ L := fun h => hcfg.not_mem h.2
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Item2130Proof.eq_zpowers_sup hcA inf_le_left hcB hcfg.card_eq
  obtain ⟨U₀, hU₀, hU₀L⟩ := (h214 G A E U c L hpair).mpr (hU4 G A E U c L hcfg h9)
  obtain ⟨hU₀E, -, -⟩ := mem_fourGroups_iff.mp hU₀.1
  have hCE9 := Sec6.card_inf_centralizer_of_mem_fourGroupsMinus
    (Late.isE27_of_mem_partTwoE hpair.mem_E.1) hU₀
  obtain ⟨b, hbU, hbB, hb1⟩ : ∃ b, b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G) ∧
      b ∈ A ⊓ L ∧ b ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : (E ⊓ Subgroup.centralizer (U₀ : Set G)) ⊓ (A ⊓ L) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      rw [Subgroup.mem_bot]
      exact hno x hx1 hx2
    have h := Item2130Proof.card_mul_card_le (inf_le_left.trans hEA) inf_le_left hbot
    rw [hCE9, h9, hA27] at h
    norm_num at h
  have hbA : b ∈ A := hbB.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hU₀b : U₀ ≤ Subgroup.centralizer ({b} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hbU.2) u hu
  obtain ⟨Y, hYb, hY0, hU₀Y, hYU₀⟩ := hY G A E U c L U₀ b hcfg h9 hU₀ hU₀L hbB hb1 hU₀b
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hbA hb1 Y hYb
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have hYp := Sec6.isPerfect_of_mem_thetaComponentsAt hYb
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have h3n : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer ({b} : Set G) →
      S ≤ Subgroup.normalizer (Y : Set G) := fun S hS hSC =>
    le_normalizer_of_isPGroup h45 hG hb3 hb1 hS hSC Y hYb
  have hQ : ∀ b' ∈ A ⊓ L, ∃ w, w ∈ Subgroup.normalizer (Y : Set G) ∧
      w ∈ Subgroup.normalizer (A : Set G) ∧ (∀ x ∈ A ⊓ L, w * x * w⁻¹ = x) ∧
        w * c * w⁻¹ = c * b' := by
    intro b' hb'
    have hBe : ∀ x ∈ A ⊓ L, x ^ 3 = 1 := fun x hx => hAe.2 x hx.1
    obtain ⟨w, hwW, hwB, hwc⟩ := hcfg.full b' hb'
    obtain ⟨k, hk3, hkc⟩ := exists_pow_conj_of_isPGroup hBe hb' hwB hwc
    have hwkB := pow_conj_eq_of_conj_eq hwB k
    have hle : Subgroup.zpowers (w ^ k) ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have h1 := hwkB b hbB
      calc w ^ k * b = w ^ k * b * (w ^ k)⁻¹ * w ^ k := by group
        _ = b * w ^ k := by rw [h1]
    exact ⟨w ^ k, h3n _ hk3 hle (Subgroup.mem_zpowers _), Subgroup.pow_mem _ hwW k, hwkB, hkc⟩
  set D := A ⊓ Sec4.thetaQuotCentralizer Y with hD
  have hbD : b ∈ D := ⟨hbA, mem_thetaQuotCentralizer_of_le_centralizer hYC⟩
  have hAD : ¬ A ≤ D := by
    intro hle
    obtain ⟨E', hE', hE'A, hYE'⟩ := mem_lZeroUnion_iff.mp hY0
    obtain ⟨-, U', hU', hU'E'⟩ := mem_lZero_iff.mp hYE'
    apply hU'E'
    obtain ⟨hU'Y, -, -⟩ := mem_invariantPiSubgroups_iff.mp hU'
    have hE'N : E' ≤ Subgroup.normalizer (Y : Set G) := hE'A.trans hAY
    have h1 : ⁅Y, E'⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y :=
      (Sec6.commutator_le_theta_iff hE'N).mpr fun x hx => (hle (hE'A hx)).2
    exact (Subgroup.commutator_mono hU'Y le_rfl).trans h1
  have hDQ : ∀ w, w ∈ Subgroup.normalizer (Y : Set G) → w ∈ Subgroup.normalizer (A : Set G) →
      ∀ x ∈ D, w * x * w⁻¹ ∈ D := fun w hwY hwA x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp hwA x).mp hx.1,
      Sec6.conj_mem_thetaQuotCentralizer hx.2 hwY⟩
  have hDB : D ≤ A ⊓ L := by
    intro x hxD
    obtain ⟨i, hi, b₁, hb₁, rfl⟩ := Sec13.exists_pow_mul_of_mem hAe hcA hAB hxD.1
    have hb₁A : b₁ ∈ A := hb₁.1
    interval_cases i
    · rwa [pow_zero, one_mul]
    ·
      exfalso
      have hBD : A ⊓ L ≤ D := by
        intro b'' hb''
        obtain ⟨w, hwY, hwA, hwB, hwc⟩ := hQ b'' hb''
        have h1 := hDQ w hwY hwA _ hxD
        have e : w * (c ^ 1 * b₁) * w⁻¹ * (c ^ 1 * b₁)⁻¹ = b'' := by
          have e1 : w * (c ^ 1 * b₁) * w⁻¹ = (w * c * w⁻¹) * (w * b₁ * w⁻¹) := by group
          rw [e1, hwc, hwB b₁ hb₁, pow_one, mul_inv_rev,
            hcomm c hcA b'' hb''.1]
          group
        rw [← e]
        exact D.mul_mem h1 (D.inv_mem hxD)
      have hcD : c ∈ D := by
        have := D.mul_mem hxD (D.inv_mem (hBD hb₁))
        rwa [pow_one, mul_inv_cancel_right] at this
      exact hAD (hAB ▸ sup_le (Subgroup.zpowers_le.mpr hcD) hBD)
    ·
      exfalso
      have hBD : A ⊓ L ≤ D := by
        intro b'' hb''
        have hb''3 : b'' ^ 3 = 1 := hAe.2 b'' hb''.1
        obtain ⟨w, hwY, hwA, hwB, hwc⟩ := hQ (b'' ^ 2) ((A ⊓ L).pow_mem hb'' 2)
        have h1 := hDQ w hwY hwA _ hxD
        have hcb : c * b'' = b'' * c := hcomm c hcA b'' hb''.1
        have e : w * (c ^ 2 * b₁) * w⁻¹ * (c ^ 2 * b₁)⁻¹ = b'' := by
          have e1 : w * (c ^ 2 * b₁) * w⁻¹ =
              (w * c * w⁻¹) * (w * c * w⁻¹) * (w * b₁ * w⁻¹) := by
            rw [pow_two]
            group
          rw [e1, hwc, hwB b₁ hb₁]
          have hc2 : c * b'' ^ 2 = b'' ^ 2 * c := (Commute.pow_right hcb 2).eq
          have hc4 : c ^ 2 * b'' ^ 4 = b'' ^ 4 * c ^ 2 := ((Commute.pow_right hcb 4).pow_left 2).eq
          have e2 : c * b'' ^ 2 * (c * b'' ^ 2) = c ^ 2 * b'' ^ 4 := by
            calc c * b'' ^ 2 * (c * b'' ^ 2) = c * (b'' ^ 2 * c) * b'' ^ 2 := by
                  simp only [mul_assoc]
              _ = c * (c * b'' ^ 2) * b'' ^ 2 := by rw [hc2]
              _ = (c * c) * (b'' ^ 2 * b'' ^ 2) := by simp only [mul_assoc]
              _ = c ^ 2 * b'' ^ 4 := by rw [← pow_two, ← pow_add]
          have e3 : c ^ 2 * b'' ^ 4 * b₁ * (c ^ 2 * b₁)⁻¹ = b'' ^ 4 := by
            rw [mul_inv_rev, mul_assoc (c ^ 2 * b'' ^ 4) b₁, mul_inv_cancel_left, hc4,
              mul_inv_cancel_right]
          rw [e2, e3, show 4 = 3 + 1 by norm_num, pow_succ, hb''3, one_mul]
        rw [← e]
        exact D.mul_mem h1 (D.inv_mem hxD)
      have hc2D : c ^ 2 ∈ D := by
        have := D.mul_mem hxD (D.inv_mem (hBD hb₁))
        rwa [mul_inv_cancel_right] at this
      have hcD : c ∈ D := by
        have := D.pow_mem hc2D 2
        rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul] at this
      exact hAD (hAB ▸ sup_le (Subgroup.zpowers_le.mpr hcD) hBD)
  have hBD : ¬ A ⊓ L ≤ D := by
    intro hle
    have hBN : A ⊓ L ≤ Subgroup.normalizer (Y : Set G) := inf_le_left.trans hAY
    have hBU : A ⊓ L ≤ Subgroup.normalizer (U₀ : Set G) := (inf_le_left.trans hEeq.ge).trans hU₀E
    have hU₀B : ⁅U₀, A ⊓ L⁆ = U₀ := by
      refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hBU) ?_
      calc U₀ = ⁅U₀, E⁆ := hU₀.2
        _ ≤ ⁅U₀, A ⊓ L⁆ := by
          rw [Subgroup.commutator_le]
          intro u hu e he
          rw [hEeq] at he
          obtain ⟨i, -, b₁, hb₁, rfl⟩ := Sec13.exists_pow_mul_of_mem hAe hcA hAB he
          have hcu : Commute c u :=
            (Subgroup.mem_centralizer_singleton_iff.mp (hLC (hU₀L hu))).symm
          have hcb₁ : Commute c b₁ := hcomm c hcA b₁ hb₁.1
          have hm := Subgroup.commutator_mem_commutator hu hb₁
          have e1 : ⁅u, c ^ i * b₁⁆ = c ^ i * ⁅u, b₁⁆ * (c ^ i)⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def]
            have h1 : u * c ^ i = c ^ i * u := ((hcu.pow_left i).eq).symm
            calc u * (c ^ i * b₁) * u⁻¹ * (c ^ i * b₁)⁻¹
                = (u * c ^ i) * b₁ * u⁻¹ * b₁⁻¹ * (c ^ i)⁻¹ := by group
              _ = c ^ i * u * b₁ * u⁻¹ * b₁⁻¹ * (c ^ i)⁻¹ := by rw [h1]
              _ = c ^ i * (u * b₁ * u⁻¹ * b₁⁻¹) * (c ^ i)⁻¹ := by group
          have e2 : c ^ i * ⁅u, b₁⁆ * (c ^ i)⁻¹ = ⁅u, b₁⁆ := by
            have hcc : Commute (c ^ i) ⁅u, b₁⁆ := by
              rw [commutatorElement_def]
              exact ((((hcu.mul_right (hcb₁)).mul_right hcu.inv_right).mul_right
                hcb₁.inv_right).pow_left i)
            rw [hcc.eq, mul_inv_cancel_right]
          rw [e1, e2]
          exact hm
    have hbot : barImage Y (A ⊓ L) = ⊥ := barImage_eq_bot_of_le fun x hx => (hle hx).2
    apply barImage_ne_bot hU₀Y hYU₀ hq
    rw [← hU₀B, barImage_commutator hU₀Y hBN, hbot, Subgroup.commutator_bot_right]
  have hDb : D = Subgroup.zpowers b := by
    have hdvd : Nat.card D ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact Subgroup.card_dvd_of_le hDB
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exfalso
      rw [pow_zero] at hkeq
      have h1 : D = ⊥ := Subgroup.eq_bot_of_card_eq _ hkeq
      rw [h1, Subgroup.mem_bot] at hbD
      exact hb1 hbD
    · refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbD) ?_).symm
      rw [hkeq, pow_one, Sec13.card_zpowers_of_pow_three hb3 hb1]
    · exfalso
      exact hBD (Subgroup.eq_of_le_of_card_ge hDB (by rw [hkeq, h9]; norm_num) ▸ le_rfl)
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hAY hcA
  have hYc : ⁅Y, Subgroup.zpowers c⁆ = Y := by
    by_contra hne
    have hle : ⁅Y, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
      by_contra hnle
      exact hne (Sec6.commutator_eq_of_not_le_theta hYp hq (Subgroup.zpowers_le.mpr hcN) hnle)
    have hcD : c ∈ D :=
      ⟨hcA, (Sec6.commutator_le_theta_iff (Subgroup.zpowers_le.mpr hcN)).mp hle
        (Subgroup.mem_zpowers c)⟩
    exact hcB (hDB hcD)
  have hYstar : Y ∈ lStar A :=
    Sec6.mem_lStar_of_inf_le_zpowers hAe hbA hb1 hYb hAY (le_of_eq hDb)
  refine ⟨b, U₀, Y, hbB, hb1, hU₀, hU₀L, hU₀b, ⟨hYb, hY0, hYstar⟩, hU₀Y, hYU₀, hcN, hYc, h3n, ?_⟩
  rw [Sec13.sectionCentralizer_eq_inf hAY, ← hD, hDb]

end CFSG.RankThree.PartTwo.Sec21
