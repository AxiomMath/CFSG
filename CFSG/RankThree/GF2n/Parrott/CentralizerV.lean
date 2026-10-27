module

public import CFSG.RankThree.GF2n.Parrott.ActionV
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def centralizerJ (x : H z) : Subgroup (J z) :=
  (Subgroup.centralizer ({(x : G)} : Set G) ⊓ J z).subgroupOf (J z)

theorem mem_centralizerJ_iff {x : H z} {j : J z} :
    j ∈ centralizerJ x ↔ (j : G) * (x : G) = (x : G) * (j : G) := by
  simp [centralizerJ, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]

theorem autFixedSubgroup_conjJ'_eq_centralizerJ (x : H z) :
    autFixedSubgroup (conjJ' z x) = centralizerJ x := by
  ext j
  rw [mem_autFixedSubgroup, mem_centralizerJ_iff]
  constructor
  · intro hfix
    have hc : (x : G) * (j : G) * (x : G)⁻¹ = (j : G) := by
      have := congrArg Subtype.val hfix
      simpa [conjJ'_apply_coe] using this
    have hc' : (x : G) * (j : G) = (j : G) * (x : G) := by
      have := congrArg (fun t : G => t * (x : G)) hc
      simpa [mul_assoc] using this
    exact hc'.symm
  · intro h
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    rw [← h]
    simp

theorem conjV_eq_congr (h : Tim79a.ParrottHyp z) (x : H z) :
    conjV h x = MulAut.congr
      (QuotientGroup.quotientMulEquivOfEq
        (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm)
      (quotientAut (conjJ' z x)) :=
  rfl

theorem autFixedSubgroup_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (α : MulAut A) :
    (autFixedSubgroup α).map e.toMonoidHom =
      autFixedSubgroup (MulAut.congr e α) := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [mem_autFixedSubgroup] at ha ⊢
    simpa [MulAut.congr_apply, MulEquiv.trans_apply, ha]
  · intro hy
    rw [Subgroup.mem_map]
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_autFixedSubgroup]
    rw [mem_autFixedSubgroup] at hy
    have hy' := congrArg e.symm hy
    simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hy'

theorem autFixedSubgroup_quotientAut_map_eq_autFixedSubgroup_conjV
    (h : Tim79a.ParrottHyp z) (x : H z) :
    (autFixedSubgroup (quotientAut (conjJ' z x))).map
        (QuotientGroup.quotientMulEquivOfEq
          (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm).toMonoidHom =
      autFixedSubgroup (conjV h x) := by
  rw [conjV_eq_congr]
  rw [autFixedSubgroup_congr]

theorem card_autFixedSubgroup_quotientAut_eq_card_autFixedSubgroup_conjV
    (h : Tim79a.ParrottHyp z) (x : H z) :
    Nat.card (autFixedSubgroup (quotientAut (conjJ' z x))) =
      Nat.card (autFixedSubgroup (conjV h x)) := by
  rw [← autFixedSubgroup_quotientAut_map_eq_autFixedSubgroup_conjV h x]
  rw [Subgroup.card_map_of_injective]
  exact (QuotientGroup.quotientMulEquivOfEq
    (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm).injective

theorem card_autFixedSubgroup_conjV_eq_card_fixedBy
    (h : Tim79a.ParrottHyp z) (x : H z) :
    Nat.card (autFixedSubgroup (conjV h x)) =
      Nat.card (MulAction.fixedBy (QuotientV.V z)
        (MulAut.toPerm (QuotientV.V z) (conjV h x))) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun v => ?_)
  rw [mem_autFixedSubgroup, MulAction.mem_fixedBy]
  rfl

theorem card_centralizerJ_eq_card_inf_mul_card_fixedBy
    (h : Tim79a.ParrottHyp z) {x : H z}
    (hcopx : Nat.Coprime (orderOf x) (Nat.card (J z))) :
    Nat.card (centralizerJ x) =
      Nat.card ↥(centralizerJ x ⊓ Subgroup.center (J z)) *
        Nat.card (MulAction.fixedBy (QuotientV.V z)
          (MulAut.toPerm (QuotientV.V z) (conjV h x))) := by
  have hcop : Nat.Coprime (orderOf (conjJ' z x)) (Nat.card (J z)) :=
    Nat.Coprime.of_dvd_left (orderOf_map_dvd (conjJ' z) x) hcopx
  have hmain := card_autFixedSubgroup_eq_card_inf_mul_card_quotient (conjJ' z x) hcop
  rw [card_autFixedSubgroup_quotientAut_eq_card_autFixedSubgroup_conjV h x] at hmain
  rw [card_autFixedSubgroup_conjV_eq_card_fixedBy h x] at hmain
  rw [autFixedSubgroup_conjJ'_eq_centralizerJ] at hmain
  exact hmain

theorem card_centralizerJ_eq_card_inf_mul_card_autFixed
    (h : Tim79a.ParrottHyp z) {x : H z}
    (hcopx : Nat.Coprime (orderOf x) (Nat.card (J z))) :
    Nat.card (centralizerJ x) =
      Nat.card ↥(centralizerJ x ⊓ Subgroup.center (J z)) *
        Nat.card (autFixedSubgroup (conjV h x)) := by
  have hmain := card_centralizerJ_eq_card_inf_mul_card_fixedBy h hcopx
  rw [← card_autFixedSubgroup_conjV_eq_card_fixedBy h x] at hmain
  exact hmain

theorem card_centralizer_eq_card_inf_centerIn_mul_card_fixedBy
    (h : Tim79a.ParrottHyp z) {x : H z}
    (hcopx : Nat.Coprime (orderOf x) (Nat.card (J z))) :
    Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ J z) =
      Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ centerIn (J z)) *
        Nat.card (MulAction.fixedBy (QuotientV.V z)
          (MulAut.toPerm (QuotientV.V z) (conjV h x))) := by
  let C : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G) ⊓ J z
  have hCJ : centralizerJ x = C.subgroupOf (J z) := rfl
  have hcardC : Nat.card ↥C = Nat.card (centralizerJ x) := by
    rw [hCJ]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : C ≤ J z)).toEquiv).symm
  have hZle : centerIn (J z) ≤ J z := inf_le_left
  have hCZ : C ⊓ centerIn (J z) =
      Subgroup.centralizer ({(x : G)} : Set G) ⊓ centerIn (J z) := by
    dsimp [C]
    rw [inf_assoc, inf_eq_right.mpr hZle]
  have hcardZ :
      Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ centerIn (J z)) =
        Nat.card ↥(centralizerJ x ⊓ Subgroup.center (J z)) := by
    rw [← hCZ, hCJ, ← QuotientV.centerIn_subgroupOf_eq_center]
    have hsub : C.subgroupOf (J z) ⊓ (centerIn (J z)).subgroupOf (J z) =
        (C ⊓ centerIn (J z)).subgroupOf (J z) := by
      ext y
      simp [Subgroup.mem_subgroupOf]
    rw [hsub]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_trans inf_le_right hZle)).toEquiv).symm
  have hmain := card_centralizerJ_eq_card_inf_mul_card_fixedBy h hcopx
  dsimp only [C] at hcardC hcardZ ⊢
  rw [hcardC, hcardZ]
  exact hmain

end CFSG.RankThree.GF2n.Parrott
