module

public import CFSG.Quasithin.H13.A6S13825a
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace L13825

variable {G : Type} [Group G]

theorem card_modO2Image {H B : Subgroup G} (hBH : B ≤ H) :
    Nat.card (modO2Image H B) = (B ⊓ pCoreOf 2 H).relIndex B := by
  let φ : ↥B →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hBH)
  have hrange : φ.range = modO2Image H B := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, hBH b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hker : φ.ker = (B ⊓ pCoreOf 2 H).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨b.2, ⟨Subgroup.inclusion hBH b, h, rfl⟩⟩
    · rintro ⟨-, ⟨y, hy, hyb⟩⟩
      have : (Subgroup.inclusion hBH b : ↥H) = y := Subtype.ext hyb.symm
      rw [this]
      exact hy
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

theorem inf_pCoreOf_le [Finite G] {M H : Subgroup G} (hHM : H ≤ M) :
    H ⊓ pCoreOf 2 M ≤ pCoreOf 2 H :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _j hj => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hHM hj)⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)

theorem card_of_isPSL_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (h : IsPSL n 2 1 X) :
    Nat.card X = 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hn, hK]
  simp

theorem card_of_isAlt {X : Type} [Group X] {n : ℕ} (h : IsAlt n X) :
    Nat.card X = Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr e.toEquiv

theorem card_of_isPSU33 {X : Type} [Group X] (h : IsPSU 3 3 1 X) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

end L13825

open L13825 in
theorem lem13825G1_of (h37 : A37ForSQTK) (h39 : A39ForSQTK) (h16 : Lem13816) (h21 : Lem13821) :
    Lem13825G1 := by
  intro G _ _ T L V S hS hno5 H hH K hK hK4
  have hG1 := hS.hG1
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHG : H ≤ S.G1 := hH.2.1
  have hTG : T ≤ S.G1 := hTH.trans hHG
  have hsylG : IsSylowTwoOf T S.G1 := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTG
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hTH.trans (h16 G T L V S hS H hH K hK).1.1
  obtain ⟨K₁, hK₁, hKK₁⟩ := lemma_1_2_4_exists S.h13.qtke S.h13.simple S.h13.nonabelian h37 h39
    hG1.1.2 hsylG (hKH.trans hHG) (cComp_subset_lFamily hTH hK)
  have hK₁G : K₁ ≤ S.G1 := le_of_mem_cComp hK₁
  have hcK : Nat.card ↥(S.KSt H K) = (K ⊓ pCoreOf 2 H).relIndex K :=
    (hS.hF H hH).toHypF91.card_autOn_tilde hKH
  have hcK₁ : Nat.card ↥(S.KSt S.G1 K₁) = (K₁ ⊓ pCoreOf 2 S.G1).relIndex K₁ :=
    (hS.hF _ hG1).toHypF91.card_autOn_tilde hK₁G
  have h20160 : Nat.card ↥(S.KSt H K) = 20160 := by
    rw [card_of_isPSL_two (by norm_num) hK4]
    decide
  have hdvd1 : (K ⊓ pCoreOf 2 H).relIndex K ∣ (K ⊓ pCoreOf 2 S.G1).relIndex K := by
    refine Subgroup.relIndex_dvd_of_le_left K (le_inf inf_le_left fun x hx => ?_)
    have hxH : x ∈ H := hKH hx.1
    exact inf_pCoreOf_le hHG ⟨hxH, hx.2⟩
  have hc := card_modO2Image (hKH.trans hHG)
  have hc₁ := card_modO2Image hK₁G
  have hle : modO2Image S.G1 K ≤ modO2Image S.G1 K₁ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hKK₁ (Subgroup.mem_subgroupOf.mp hx))
  have hdvd2 := Subgroup.card_dvd_of_le hle
  have h21G := h21 G T L V S hS S.G1 hG1 K₁ hK₁
  have hc₁le : Nat.card ↥(S.KSt S.G1 K₁) ≤ 20160 := by
    rcases h21G.2.1 with h | h | h | h | h | h
    · rw [card_of_isPSL_two (by norm_num) h]
      decide
    · rw [card_of_isPSL_two (by norm_num) h]
      decide
    · exact absurd h (hno5 _ hG1 K₁ hK₁)
    · rw [card_of_isAlt h, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    · rw [card_of_isAlt h, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    · rw [card_of_isPSU33 h]
      decide
  have hpos : 0 < Nat.card (modO2Image S.G1 K₁) := Nat.card_pos
  have hpos' : 0 < Nat.card (modO2Image S.G1 K) := Nat.card_pos
  have hA : 20160 ∣ Nat.card (modO2Image S.G1 K) := by
    rw [hc, ← h20160, hcK]
    exact hdvd1
  have hB : Nat.card (modO2Image S.G1 K₁) ≤ 20160 := by
    rw [hc₁, ← hcK₁]
    exact hc₁le
  have h1 := Nat.le_of_dvd hpos hdvd2
  have h2 := Nat.le_of_dvd hpos' hA
  have heqI : modO2Image S.G1 K = modO2Image S.G1 K₁ :=
    Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hKeq : K = K₁ := Vol2.Ch11.SecA.eq_of_modO2Image_eq hsylG hK₁G hKK₁
    (perfect_of_mem_cComp hK₁) hTK heqI
  rw [← (h21 G T L V S hS H hH K hK).2.2.1.1, ← h21G.2.2.1.1, hKeq]

end CFSG.Quasithin.H13.A6
