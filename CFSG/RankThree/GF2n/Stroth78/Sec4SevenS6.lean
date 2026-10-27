module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Six

import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConjModel
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaLocal
import CFSG.RankThree.GF2n.Stroth78.Sec4OneW
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusNotCentral
import CFSG.Timmesfeld.Transvection.QTwoSp
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Struct
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Z
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Three
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem nonempty_mulEquiv_perm_six_statedSp : Nonempty (Perm (Fin 6) ≃* StatedSp 2 (ZMod 2)) := by
  obtain ⟨ψ, -⟩ := CFSG.Timmesfeld.Transvection.QTwo.exists_sympEquiv_of_perm_six
    (D := {g : Perm (Fin 6) | g.IsSwap}) (MulEquiv.refl (Perm (Fin 6))) fun g => Iff.rfl
  let e : StatedSp 2 (ZMod 2) ≃* TauCeti.GLSymplectic (Fin 2) (ZMod 2) :=
    MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
  exact ⟨ψ.trans e.symm⟩

theorem commute_of_mem_derived_two_s6 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (Ψ : ↥(Xsub S a) ≃* Perm (Fin 6))
    (hΨ : ∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap)
    (hZ : ∀ x ∈ commutator ↥(Xsub S a), rhoZ S (x : Hbar z) = 1) :
    ∀ x ∈ ⁅⁅H z, H z⁆, ⁅H z, H z⁆⁆, ∀ y ∈ ZQ z, Commute x y := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Hbar_prod_s6 S Ψ hΨ
  let C := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  let q : ↥(H z) →* C := ((MonoidHom.snd _ _).comp ψ.toMonoidHom).comp
    (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
  let p : ↥(H z) →* ↥(Xsub S a) := ((MonoidHom.fst _ _).comp ψ.toMonoidHom).comp
    (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
  have hC2 : ⁅commutator C, commutator C⁆ = ⊥ :=
    CFSG.EvenSmallLie.UnitarySix.Yamada.commutator_commutator_eq_bot_of_card_dvd_six
      (card_centralizer_Xsub_dvd_six S h h217)
  let T : Subgroup ↥(H z) := ⊤
  have hq : ∀ x' ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)), q x' = 1 := by
    intro x' hx'
    have hmem : q x' ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)).map q :=
      Subgroup.mem_map_of_mem q hx'
    rw [Subgroup.map_commutator, Subgroup.map_commutator] at hmem
    have hle : ⁅⁅T.map q, T.map q⁆, ⁅T.map q, T.map q⁆⁆ ≤ ⁅commutator C, commutator C⁆ := by
      rw [commutator_def]
      exact Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
        (Subgroup.commutator_mono le_top le_top)
    rw [hC2] at hle
    exact Subgroup.mem_bot.mp (hle hmem)
  have hp : ∀ x' ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)), p x' ∈ commutator ↥(Xsub S a) := by
    intro x' hx'
    have hmem : p x' ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)).map p :=
      Subgroup.mem_map_of_mem p hx'
    rw [Subgroup.map_commutator, Subgroup.map_commutator] at hmem
    have hle : ⁅⁅T.map p, T.map p⁆, ⁅T.map p, T.map p⁆⁆ ≤ commutator ↥(Xsub S a) := by
      refine (Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
        (Subgroup.commutator_mono le_top le_top)).trans ?_
      exact Subgroup.commutator_le_left _ _
    exact hle hmem
  intro x hx y hy
  have hT : T.map (H z).subtype = H z := by
    rw [show T = ⊤ from rfl, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hx' : x ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)).map (H z).subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hT]
    exact hx
  obtain ⟨x', hx'm, rfl⟩ := hx'
  have hmk : (QuotientGroup.mk x' : Hbar z) = ((p x' : ↥(Xsub S a)) : Hbar z) := by
    have h1 := hψ (ψ (QuotientGroup.mk x'))
    rw [MulEquiv.symm_apply_apply] at h1
    have hu2 : (ψ (QuotientGroup.mk x')).2 = 1 := hq x' hx'm
    rw [h1, hu2, OneMemClass.coe_one, mul_one]
    rfl
  have hrho : rhoZ S (QuotientGroup.mk x') = 1 := by
    rw [hmk]
    exact hZ _ (hp x' hx'm)
  have h2 := rhoZ_mk S x' ⟨y, hy⟩
  rw [hrho] at h2
  change ((⟨y, hy⟩ : ↥(ZQ z)) : G) = (x' : G) * y * (x' : G)⁻¹ at h2
  show (x' : G) * y = y * (x' : G)
  calc (x' : G) * y = (x' : G) * y * (x' : G)⁻¹ * (x' : G) := by group
    _ = y * (x' : G) := by rw [← h2]

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem stroth78_47_s6 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (φ : ↥(threeResidualQuot
      (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) ≃*
        Equiv.Perm (Fin 6))
    (hφ : ∀ g, g ∈ threeResidualClass
      (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ↔ (φ g).IsSwap) :
    StrothCaseVIII z w := by
  classical
  obtain ⟨α₀, hα₀, hα₀1, hc⟩ := Sec4OneW.exists_mem_Rbar_isConj S h h217 h3 hα
  obtain ⟨φ₀, hφ₀⟩ := exists_mulEquiv_threeResidualQuot_of_isConj hc φ hφ
  obtain ⟨Ψ, hΨ, hΨα⟩ :=
    Sec4SevenS6.exists_mulEquiv_Xsub_perm_six_swap S h h217 h3 hα₀ hα₀1 φ₀ hφ₀
  have hZ := Sec4SevenS6.rhoZ_commutator_Xsub_eq_one_s6 S h h217 h3 hα₀ hα₀1 Ψ hΨ hΨα
  have hw3 : w ≠ 3 := fun hw =>
    Sec4SevenS6.false_of_w_eq_three_s6 S h h217 h3 hα₀ hα₀1 Ψ hΨ hΨα hZ hw
  have hw4 : w ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hlt
    have h2 := h.two_pow_le_card_Lbar
    have h3' := Sec4SevenS6.card_Lbar_le_sixteen S h h217 Ψ hΨ
    omega
  have hw : w = 4 := by
    have := h.three_le
    omega
  obtain ⟨e⟩ := Sec4SevenS6.nonempty_mulEquiv_Hbar_perm_six_prod_perm_three S h h217 Ψ hΨ hw.ge
  obtain ⟨sp⟩ := Sec4SevenS6.nonempty_mulEquiv_perm_six_statedSp
  let e' : Hbar z ≃* ↥(StatedSp 2 (ZMod 2)) × Equiv.Perm (Fin 3) :=
    e.trans (MulEquiv.prodCongr sp (MulEquiv.refl (Equiv.Perm (Fin 3))))
  exact ⟨2, by omega, by omega, ⟨inferInstance, ⟨e'⟩⟩,
    Sec4SevenS6.commute_of_mem_derived_two_s6 S h h217 Ψ hΨ hZ, not_zq_le_centerIn_H S h⟩

end CFSG.RankThree.GF2n.Stroth78
