module

public import CFSG.RankThree.PartOne.TAIL.SylAux
public import CFSG.RankThree.PartOne.S11d.InnerBasic
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open scoped commutatorElement

section Aux

variable {G : Type} [Group G]

theorem isQuasisimple_of_simple_of_center_bot {Q : Type*} [Group Q] [Nontrivial Q]
    (hs : IsSimpleGroup Q) (hZ : Subgroup.center Q = ⊥) : CFSG.IsQuasisimple Q := by
  have hsQ : IsSimpleGroup Q := hs
  have eQ : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hno
    push Not at hno
    have hc : Subgroup.center Q = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      rw [Subgroup.mem_center_iff]
      intro h
      exact hno h g
    rw [hZ] at hc
    obtain ⟨g, hg⟩ := exists_ne (1 : Q)
    have : g ∈ (⊤ : Subgroup Q) := Subgroup.mem_top g
    rw [← hc, Subgroup.mem_bot] at this
    exact hg this
  have hperf : Group.IsPerfect Q := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator Q) with h0 | h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← _root_.commutator_def, h0, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exact ⟨h0⟩
  refine ⟨hperf, ?_, ?_⟩
  · exact eQ.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eQ.symm a, eQ.symm b, fun h => hab (by simpa using congrArg eQ h)⟩

theorem eq_one_of_mem_inf_centralizer {L : Subgroup G} (hZ : Subgroup.center ↥L = ⊥) {y : G}
    (hyL : y ∈ L) (hyC : y ∈ Subgroup.centralizer (L : Set G)) : y = 1 := by
  have hmem : (⟨y, hyL⟩ : L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC g g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem exists_decomp_sup_centralizer {L : Subgroup G} {x : G}
    (hx : x ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    ∃ l ∈ L, ∃ z ∈ Subgroup.centralizer (L : Set G), x = l * z := by
  rw [sup_comm] at hx
  have hx' : x ∈ ((Subgroup.centralizer (L : Set G) ⊔ L : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (Subgroup.centralizer_le_normalizer (L : Set G))] at hx'
  obtain ⟨z, hz, l, hl, rfl⟩ := hx'
  refine ⟨l, hl, z, hz, ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp hz l hl).symm

theorem normalizer_of_conj_mem_of_finite [Finite G] {B : Subgroup G} {w : G}
    (h : ∀ b ∈ B, w * b * w⁻¹ ∈ B) : w ∈ Subgroup.normalizer (B : Set G) := by
  have hle : B.map (MulAut.conj w).toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  have hcard : Nat.card B ≤ Nat.card (B.map (MulAut.conj w).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
  have heq : B.map (MulAut.conj w).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have hx' : w * x * w⁻¹ ∈ B.map (MulAut.conj w).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨b, hb, hbx⟩ := hx'
  have : b = x := by
    have h1 : w * b * w⁻¹ = w * x * w⁻¹ := hbx
    simpa using h1
  exact this ▸ hb

theorem mem_zpowers_of_pRank [Finite G] {L : Subgroup G} {c y : G} (hc7 : orderOf c = 7)
    (hy7 : orderOf y = 7) (hcC : c ∈ Subgroup.centralizer (L : Set G))
    (hyC : y ∈ Subgroup.centralizer (L : Set G)) (hcomm : y * c = c * y)
    (hC1 : CFSG.pRank 7 ↥(Subgroup.centralizer (L : Set G)) ≤ 1) : y ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_contra hy
  have hcy : c ^ 7 = 1 := by rw [← hc7]; exact pow_orderOf_eq_one c
  have hyy : y ^ 7 = 1 := by rw [← hy7]; exact pow_orderOf_eq_one y
  have : IsElementaryAbelian 7 ↥(Subgroup.zpowers y) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hyy
  have : IsElementaryAbelian 7 ↥(Subgroup.zpowers c) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hcy
  have hCE : Subgroup.zpowers c ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute y c from hcomm) j).eq
  have : IsElementaryAbelian 7 ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers c) :=
    IsElementaryAbelian.sup_of_le_centralizer hCE
  have hEC : Subgroup.zpowers y ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hyC) (Subgroup.zpowers_le.mpr hcC)
  have : IsElementaryAbelian 7 ↥((Subgroup.zpowers y ⊔ Subgroup.zpowers c).subgroupOf
      (Subgroup.centralizer (L : Set G))) := IsElementaryAbelian.subgroupOf hEC
  obtain ⟨m, hm⟩ :=
    (IsElementaryAbelian.isPGroup 7 ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers c)).exists_card_eq
  have hcard' : Nat.card ↥((Subgroup.zpowers y ⊔ Subgroup.zpowers c).subgroupOf
      (Subgroup.centralizer (L : Set G))) = 7 ^ m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hm]
  have h1 := CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num : 1 < 7) _ inferInstance hcard'
  have hm1 : m ≤ 1 := h1.trans hC1
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers c := le_sup_left
  have hcardy : Nat.card ↥(Subgroup.zpowers y) = 7 := by rw [Nat.card_zpowers, hy7]
  have hcardE : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers c) ≤ 7 := by
    rw [hm]
    calc 7 ^ m ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      _ = 7 := by norm_num
  have hEy : Subgroup.zpowers y = Subgroup.zpowers y ⊔ Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardy]; exact hcardE)
  have hcE : c ∈ Subgroup.zpowers y := by
    rw [hEy]
    exact (le_sup_right : Subgroup.zpowers c ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers c)
      (Subgroup.mem_zpowers c)
  have hcard_c : Nat.card ↥(Subgroup.zpowers c) = 7 := by rw [Nat.card_zpowers, hc7]
  have hcy' : Subgroup.zpowers c ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hcE
  have hyc : Subgroup.zpowers y = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge hcy' (by rw [hcard_c, hcardy])).symm
  exact hy (by rw [← hyc]; exact Subgroup.mem_zpowers y)

end Aux

section ConfigPart

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ}

theorem mem_normalizer_zpowers_of_comm {x c : G} (h : x * c = c * x) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  refine normalizer_of_conj_mem_of_finite fun b hb => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h1 : x * c * x⁻¹ = c := by rw [h]; group
  have h2 : x * c ^ j * x⁻¹ = c ^ j := by rw [← conj_zpow, h1]
  rw [h2]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) j

theorem config_isQuasisimple (cfg : Sec109.Config 7 A c L B n) : CFSG.IsQuasisimple ↥L := by
  have hZ : Subgroup.center ↥L = ⊥ := (Sec109.lnTwoOuter ↥L n cfg.model).1
  obtain ⟨hnt, hs⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L n 2 1 cfg.model
  exact isQuasisimple_of_simple_of_center_bot hs hZ

theorem mem_normalizer_L_of_inf (cfg : Sec109.Config 7 A c L B n) {b y : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hy : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hbL' : b ∈ L.map (MulAut.conj y).toMonoidHom) : y ∈ Subgroup.normalizer (L : Set G) := by
  have hp : Nat.Prime 7 := by norm_num
  by_contra hyL
  set L' : Subgroup G := L.map (MulAut.conj y).toMonoidHom with hL'
  have hL'c : L' ∈ thetaComponentsAt 7 c :=
    Sec12TwoAssembly.conj_mem_thetaComponentsAt hp hy cfg.L_mem.2
  have hne : L' ≠ L := fun heq => hyL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  have hbL : b ∈ L := cfg.B_le_L hbB
  have hcent := Sec12TwoAssembly.le_centralizer_of_mem_thetaComponentsAt_ne hp hL'c cfg.L_mem.2
    (config_isQuasisimple cfg) hne (B := Subgroup.zpowers b) (Subgroup.zpowers_le.mpr hbL')
    (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hbL))
  have hbc : b ∈ Subgroup.centralizer (L : Set G) := hcent (Subgroup.mem_zpowers b)
  exact hb1 (eq_one_of_mem_inf_centralizer (Sec109.lnTwoOuter ↥L n cfg.model).1 hbL hbc)

theorem mem_normalizer_L_of_normalizer_A (cfg : Sec109.Config 7 A c L B n) {x : G}
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) (hxA : x ∈ Subgroup.normalizer (A : Set G)) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have hxz : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hxc)
  have hA3 : Nat.card A = 343 := by rw [cfg.A_card]; norm_num
  have hB' : Nat.card (B.map (MulAut.conj x).toMonoidHom) = 49 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact cfg.B_card
  have hB'A : B.map (MulAut.conj x).toMonoidHom ≤ A := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hxA b).mp (cfg.B_le_A hb)
  obtain ⟨b, hb, hb1⟩ := exists_ne_one_mem_inf_of_card hA3 cfg.B_card hB' cfg.B_le_A hB'A
  have hbL' : b ∈ L.map (MulAut.conj x).toMonoidHom :=
    Subgroup.map_mono cfg.B_le_L hb.2
  exact mem_normalizer_L_of_inf cfg hb.1 hb1 hxz hbL'

end ConfigPart

end CFSG.RankThree.PartOne.TAIL
