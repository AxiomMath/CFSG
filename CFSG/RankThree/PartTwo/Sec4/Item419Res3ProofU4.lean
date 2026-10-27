module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOrders
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Outer
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofCensus
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
import CFSG.RankThree.PartTwo.Sec21.Item22Tools
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)
open CFSG.Assembly.RankThreeEven (projSU)

namespace Item419Res3

theorem fixSub_normalizerMonoidHom {G : Type} [Group G] (L : Subgroup G) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    Item426.fixSub (L.normalizerMonoidHom ⟨a, ha⟩) =
      (L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf L := by
  ext l
  rw [Item426.mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : a * (l : G) * a⁻¹ = l := congrArg Subtype.val h
    refine ⟨l.2, ?_⟩
    calc (l : G) * a = a * (l : G) * a⁻¹ * a := by rw [h1]
      _ = a * l := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    change a * (l : G) * a⁻¹ = l
    rw [← h, mul_inv_cancel_right]

theorem fixSub_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    Item426.fixSub (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext y
  rw [Item426.mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem center_projSU_four_eq_bot {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (projSU 4 2 n) = ⊥ := by
  have := Sec21.isSimpleGroup_projSU (m := 4) (n := n) le_rfl hn
  refine Res419Two.center_eq_bot_of_simple ?_
  rw [Sec19.Step1911Proof.card_projSU_four hn]
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine Nat.not_prime_mul ?_ ?_
  · have : 2 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hq 6
    omega
  · have h2 : 3 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 2 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 1 ≤ (2 ^ n) ^ 3 + 1 := by omega
    have h4 : 1 ≤ (2 ^ n) ^ 4 - 1 := by
      have : 2 ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    have : 3 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) :=
      calc 3 ≤ (2 ^ n) ^ 2 - 1 := h2
        _ ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := Nat.le_mul_of_pos_right _ h3
        _ ≤ _ := Nat.le_mul_of_pos_right _ h4
    omega

theorem isComponent_map_subgroupOf {G X : Type*} [Group G] [Group X] {L H K : Subgroup G}
    (hHL : H ≤ L) (e : L ≃* X) (hK : IsComponent (K.subgroupOf H)) :
    IsComponent (((K.subgroupOf L).map e.toMonoidHom).subgroupOf
      ((H.subgroupOf L).map e.toMonoidHom)) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine isComponent_subgroupOf_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hHL).symm.trans
      ((H.subgroupOf L).equivMapOfInjective e.toMonoidHom hinj)) (fun x => ?_) hK
  rw [MulEquiv.trans_apply, Subgroup.coe_equivMapOfInjective_apply,
    Subgroup.mem_map_iff_mem hinj, Subgroup.mem_subgroupOf,
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe]

end Item419Res3

open Item419Res3

theorem k419U4Odd_holds :
    K419U4Odd := by
  intro G _ _ L n hn hLe a haL ha3 haC K hK hKc ht
  obtain ⟨e⟩ := hLe
  have hn1 : 1 ≤ n := hn.pos
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  set β : MulAut L := L.normalizerMonoidHom ⟨a, haL⟩ with hβ
  set α : MulAut (projSU 4 2 n) := MulAut.congr e β with hα
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow]
    have : (⟨a, haL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext ha3'
    rw [this, map_one]
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hβ3, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    apply haC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 := congrArg (fun γ : MulAut L => ((γ ⟨l, hl⟩ : L) : G)) h1
    simp only [MulAut.one_apply] at h2
    change a * l * a⁻¹ = l at h2
    calc l * a = a * l * a⁻¹ * a := by rw [h2]
      _ = a * l := by group
  have hα1 : α ≠ 1 := by
    intro h1
    apply hβ1
    rw [hα] at h1
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  set M := L ⊓ Subgroup.centralizer ({a} : Set G) with hM
  have hfixβ := fixSub_normalizerMonoidHom L haL
  have hfixα : (M.subgroupOf L).map e.toMonoidHom = Item426.fixSub α := by
    rw [← hfixβ]
    exact Item426.map_fixSub_eq e β
  set K₀ : Subgroup (projSU 4 2 n) := (K.subgroupOf L).map e.toMonoidHom with hK₀
  have hK₀c : IsComponent (K₀.subgroupOf (Item426.fixSub α)) := by
    rw [← hfixα]
    exact isComponent_map_subgroupOf inf_le_left e hKc
  have hK₀le : K₀ ≤ Item426.fixSub α := by
    rw [← hfixα]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hK)
  have hKL : K ≤ L := hK.trans inf_le_left
  set eK : K ≃* K₀ := (Subgroup.subgroupOfEquivOfLe hKL).symm.trans
    ((K.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
  have hZ : Subgroup.center K₀ = ⊥ := by
    rw [← Subgroup.map_center_eq eK, Res419Two.center_eq_bot_of_isType419 ht, Subgroup.map_bot]
  have hcard : Nat.card K₀ = Nat.card K := (Nat.card_congr eK.toEquiv).symm
  by_cases hin : IsInnerAut α
  · obtain ⟨x, hx⟩ := hin
    have hx3 : x ^ 3 = 1 := by
      have h1 : MulAut.conj (x ^ 3) = 1 := by
        rw [map_pow, hx, hα3]
      have h2 : x ^ 3 ∈ Subgroup.center (projSU 4 2 n) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := congrArg (fun γ : MulAut (projSU 4 2 n) => γ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc y * x ^ 3 = x ^ 3 * y * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
          _ = x ^ 3 * y := by group
      rwa [center_projSU_four_eq_bot hn1, Subgroup.mem_bot] at h2
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hα1
      rw [← hx, map_one]
    have hfix : Item426.fixSub α = Subgroup.centralizer ({x} : Set (projSU 4 2 n)) := by
      rw [← hx]
      exact fixSub_conj_eq_centralizer x
    rw [hfix] at hK₀c hK₀le
    rcases inner_case hn hx3 hx1 hK₀le hK₀c with hZ' | hc
    · exact hZ' hZ
    · exact card_ne_sl2_of_isType419 ht hn (hcard ▸ hc)
  · obtain ⟨k, hk, hc⟩ := outer_case hn hα3 hin hK₀le hK₀c
    exact card_ne_u4_of_isType419 ht hk (hcard ▸ hc)

end CFSG.RankThree.PartTwo.Sec4
