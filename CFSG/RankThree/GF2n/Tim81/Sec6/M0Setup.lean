module

public import CFSG.RankThree.GF2n.Tim81.Sec6.RootSetup
public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs
import CFSG.RankThree.GF2n.Tim81.Sec6.S61
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Rec
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

theorem Sec6Hyp.exists_card_V (hS : Sec6Hyp M V) : ∃ f, 2 ≤ f ∧ Nat.card V = 2 ^ f := by
  obtain ⟨U, hU⟩ := hS.ne
  obtain ⟨g, rfl, hH⟩ := hU
  have hg : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hH⟩
  obtain ⟨F, hF, hFintype, hCharP, l, hl, ψ, hw⟩ := (hS.sec5.shape hg).shape
  have h2 : 2 ≤ l := by
    rw [← Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)]
    calc 2 ^ 2 = 4 := by norm_num
      _ ≤ Nat.card V := hS.sec5.toRootHyp.four_le_card
      _ = 2 ^ l := hw.card_V
  exact ⟨l, h2, hw.card_V⟩

theorem Sec5Hyp.imgQ_m0Of_eq_iSup (hS : Sec5Hyp M V) :
    imgQ M (m0Of M V) = ⨆ A ∈ imgQ M '' sigmaSet M V, A := by
  rw [iSup_image]
  have hm0 : (⨆ U ∈ sigmaSet M V, U) ≤ M := hS.m0Of_le_M
  have hsub : (m0Of M V).subgroupOf M = ⨆ U ∈ sigmaSet M V, (U.subgroupOf M) := by
    unfold m0Of
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hm0]
    rw [Subgroup.map_iSup]
    refine iSup_congr fun U => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun hU =>
      (Subgroup.map_subgroupOf_eq_of_le (hS.le_M_of_mem_sigmaSet hU).1).symm
  unfold imgQ
  rw [hsub, Subgroup.map_iSup]
  refine iSup_congr fun U => ?_
  rw [Subgroup.map_iSup]

theorem Sec6Hyp.isL2Gen_imgQ (hS : Sec6Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V) (hl : IsL2Gen U U') :
    IsL2Gen (imgQ M U) (imgQ M U') := by
  have hUM : U ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hU).1
  have hU'M : U' ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hU').1
  have h4U : 4 ≤ Nat.card U := by
    obtain ⟨g, rfl, -⟩ := hU
    rw [card_conjSubgroup]
    exact hS.sec5.toRootHyp.four_le_card
  have h4 : 4 ≤ Nat.card (U.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
    exact h4U
  have hnot : ¬ U.subgroupOf M ≤ (QuotientGroup.mk' (pCore 2 ↥M)).ker := by
    rw [QuotientGroup.ker_mk', ← hS.sec5.Pc_subgroupOf hS.ne]
    intro hle
    have hUP : U ≤ Pc M V := by
      intro x hx
      have hxM : x ∈ M := hUM hx
      have hxsub : (⟨x, hxM⟩ : ↥M) ∈ U.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp (hle hxsub)
    have hbot : U = ⊥ := by
      rw [← hS.sec5.inf_Pc_eq_bot hU, inf_eq_left.mpr hUP]
    rw [hbot, Subgroup.card_bot] at h4U
    omega
  have hker := (hl.subgroupOf hUM hU'M).ker_inf_eq_bot h4
    (QuotientGroup.mk' (pCore 2 ↥M)) hnot
  exact (hl.subgroupOf hUM hU'M).map (QuotientGroup.mk' (pCore 2 ↥M)) hker

theorem Sec6Hyp.rootSetup (hS : Sec6Hyp M V) {f : ℕ} (hf : 2 ≤ f)
    (hV : Nat.card V = 2 ^ f) :
    RootSetup (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f where
  normal := hS.sec5.imgQ_m0Of_normal
  two_le := hf
  nonempty := hS.ne.image (imgQ M)
  le := by
    rintro A ⟨U, hU, rfl⟩
    exact imgQ_mono (le_m0Of_of_mem_sigmaSet hU)
  gen := hS.sec5.imgQ_m0Of_eq_iSup
  conj := by
    rintro A ⟨U, hU, rfl⟩ B ⟨U', hU', rfl⟩
    obtain ⟨y, hy, rfl⟩ := hS.sigma_conj_m0 hU hU'
    have hyM : y ∈ M := hS.sec5.m0Of_le_M hy
    exact ⟨QuotientGroup.mk' _ ⟨y, hyM⟩, mk_mem_imgQ hy,
      by rw [imgQ_conjSubgroup ⟨y, hyM⟩ U]⟩
  conj_mem := by
    rintro A ⟨U, hU, rfl⟩ z hz
    obtain ⟨y, hy, rfl⟩ := mem_imgQ_iff.mp hz
    exact ⟨conjSubgroup (y : G) U, hS.sec5.conj_mem_sigmaSet y.2 hU,
      by rw [imgQ_conjSubgroup y U]⟩
  card := by
    rintro A ⟨U, hU, rfl⟩
    rw [hS.card_imgQ_of_inf_Pc_eq_bot (hS.sec5.le_M_of_mem_sigmaSet hU).1
      (hS.sec5.inf_Pc_eq_bot hU)]
    obtain ⟨g, rfl, -⟩ := hU
    rw [card_conjSubgroup]
    exact hV
  pair := by
    rintro A ⟨U, hU, rfl⟩ B ⟨U', hU', rfl⟩ hAB
    rcases hS.res.s513 M V hS.sec5 U hU U' hU' with ⟨hcomm, -⟩ | ⟨hl2, -⟩
    · left
      change ⁅(U.subgroupOf M).map (QuotientGroup.mk' (pCore 2 ↥M)),
        (U'.subgroupOf M).map (QuotientGroup.mk' (pCore 2 ↥M))⁆ = ⊥
      rw [← Subgroup.map_commutator]
      have hcomm' : ⁅U.subgroupOf M, U'.subgroupOf M⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
            (Subgroup.mem_subgroupOf.mp hx)) (y : G) (Subgroup.mem_subgroupOf.mp hy))
      rw [hcomm', Subgroup.map_bot]
    · exact Or.inr (hS.isL2Gen_imgQ hU hU' hl2)
  partner := by
    rintro A ⟨U, hU, rfl⟩
    obtain ⟨U', hU', hl2⟩ := hS.exists_isL2Gen hU
    exact ⟨imgQ M U', ⟨U', hU', rfl⟩, hS.isL2Gen_imgQ hU hU' hl2⟩
  pCore_eq_bot := hS.pCore_imgQ_m0
  oddCore_le := hS.oddCore_imgQ_m0_le_center

theorem isPGroup_imgQ_lOf (g : G) :
    IsPGroup 2 (imgQ M (lOf M V g)) := by
  unfold imgQ lOf
  rw [Subgroup.inf_subgroupOf_right]
  exact ((isPGroup_conj_Pc M V g).comap_subtype).map _

theorem Sec5Hyp.imgQ_le_imgQ_lOf (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    imgQ M (conjSubgroup g V) ≤ imgQ M (lOf M V g) :=
  imgQ_mono (hS.conjSubgroup_le_lOf hg)

theorem imgQ_lOf_le_cenOf (M V : Subgroup G) (g : G) :
    imgQ M (lOf M V g) ≤ cenOf (imgQ M (conjSubgroup g V)) := by
  intro z hz
  obtain ⟨l, hl, rfl⟩ := mem_imgQ_iff.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_imgQ_iff.mp hy
  have hcent : (l : G) ∈ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    conjSubgroup_Pc_le_centralizer M V g hl.1
  have hcomm : (x : G) * (l : G) = (l : G) * (x : G) :=
    Subgroup.mem_centralizer_iff.mp hcent (x : G) hx
  rw [← map_mul, ← map_mul]
  rw [show (x : ↥M) * l = l * x from Subtype.ext hcomm]

theorem Sec6Hyp.normalizer_imgQ_le (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    Subgroup.normalizer (imgQ M (conjSubgroup g V) : Set (MBar M)) ≤
      Subgroup.normalizer (imgQ M (lOf M V g) : Set (MBar M)) := by
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥M) z
  have hxM : (x : G) ∈ M := x.2
  have hzA : conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) x)
      (imgQ M (conjSubgroup g V)) = imgQ M (conjSubgroup g V) :=
    mem_normalizer_iff_conjSubgroup_eq.mp hz
  have hAl : conjSubgroup (x : G) (conjSubgroup g V) ≤
      conjSubgroup g V ⊔ Pc M V := by
    refine hS.le_sup_Pc_of_imgQ_le (U := conjSubgroup (x : G) (conjSubgroup g V)) ?_ ?_
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      exact M.mul_mem (M.mul_mem hxM ((hS.sec5.le_M_of_mem_sigmaSet hg).1 ha))
        (M.inv_mem hxM)
    · rw [imgQ_conjSubgroup x (conjSubgroup g V)]
      exact hzA.le
  have hxP : conjSubgroup (x : G) (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc hxM)
  have hxAP : conjSubgroup (x : G) (conjSubgroup g V ⊔ Pc M V) =
      conjSubgroup g V ⊔ Pc M V := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [conjSubgroup_sup, hxP]
      exact sup_le hAl le_sup_right
    · rw [card_conjSubgroup]
  have hxL : conjSubgroup (x : G) (lOf M V g ⊔ Pc M V) = lOf M V g ⊔ Pc M V :=
    hS.stmt61a g (x : G) hg hxM hxAP
  rw [mem_normalizer_iff_conjSubgroup_eq]
  calc conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) x) (imgQ M (lOf M V g))
      = conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) x)
          (imgQ M (lOf M V g ⊔ Pc M V)) := by rw [imgQ_sup_Pc hS inf_le_right]
    _ = imgQ M (conjSubgroup (x : G) (lOf M V g ⊔ Pc M V)) :=
        (imgQ_conjSubgroup x (lOf M V g ⊔ Pc M V)).symm
    _ = imgQ M (lOf M V g ⊔ Pc M V) := by rw [hxL]
    _ = imgQ M (lOf M V g) := imgQ_sup_Pc hS inf_le_right

theorem Sec6Hyp.card_imgQ_lOf (hS : Sec6Hyp M V) {n : ℕ}
    (hn : Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1)) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    Nat.card (imgQ M (lOf M V g)) = Nat.card V ^ (2 * n - 3) := by
  obtain ⟨n', hn'2, hn'card, hn'L⟩ := hS.stmt61b
  have hq : 2 ≤ Nat.card V := le_trans (by norm_num) hS.sec5.toRootHyp.four_le_card
  have hexp : 2 * n + 1 = 2 * n' + 1 :=
    Nat.pow_right_injective hq (hn.symm.trans hn'card)
  have hnn' : n = n' := by omega
  subst hnn'
  obtain ⟨hLcard, hLP, -⟩ := hn'L g hg
  have hqpos : 0 < Nat.card V := Nat.card_pos
  have hP := hS.card_imgQ_mul_card_inf_Pc (U := lOf M V g) inf_le_right
  rw [hLcard, hLP] at hP
  apply Nat.mul_right_cancel (pow_pos hqpos 2)
  rw [hP, ← pow_add]
  congr 1
  omega

end CFSG.RankThree.GF2n.Tim81
