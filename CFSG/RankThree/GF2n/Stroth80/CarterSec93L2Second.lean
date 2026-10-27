module

public import CFSG.RankThree.GF2n.Stroth80.CarterSec93Core
public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step93L2Second_H_normal (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) :
    ((LB M Q B ⊓ conjSubgroup h (LB M Q B)).subgroupOf
      (LB M Q B ⊔ conjSubgroup h (LB M Q B))).Normal := by
  classical
  set L : Subgroup G := LB M Q B with hL
  set L' : Subgroup G := conjSubgroup h L with hL'
  set H : Subgroup G := L ⊓ L' with hH
  have hQL : Q ≤ L := sec39_Q_le_LB
  have hQL' : Q ≤ L' := by
    rw [hL', ← hc.conj_Q_eq hh]
    exact Subgroup.map_mono hQL
  have hQH : Q ≤ H := le_inf hQL hQL'
  have hcommL' : ∀ x ∈ L', ∀ y ∈ L', ⁅x, y⁆ ∈ Q := by
    intro x hx y hy
    rw [hL'] at hx hy
    change x ∈ L.map (MulAut.conj h).toMonoidHom at hx
    change y ∈ L.map (MulAut.conj h).toMonoidHom at hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hQ := hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator ha hb)
    have e : ⁅(MulEquiv.toMonoidHom (MulAut.conj h)) a,
        (MulEquiv.toMonoidHom (MulAut.conj h)) b⁆ =
        (MulEquiv.toMonoidHom (MulAut.conj h)) ⁅a, b⁆ :=
      (map_commutatorElement (f := (MulAut.conj h).toMonoidHom)
        (g₁ := a) (g₂ := b)).symm
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hh) _).mp hQ
  have hfwdL : ∀ w ∈ L, ∀ y ∈ H, w * y * w⁻¹ ∈ H := by
    intro w hw y hy
    have hcomm : ⁅w, y⁆ ∈ Q :=
      hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hw hy.1)
    have e : w * y * w⁻¹ = ⁅w, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact H.mul_mem (hQH hcomm) hy
  have hfwdL' : ∀ w ∈ L', ∀ y ∈ H, w * y * w⁻¹ ∈ H := by
    intro w hw y hy
    have hcomm : ⁅w, y⁆ ∈ Q := hcommL' w hw y hy.2
    have e : w * y * w⁻¹ = ⁅w, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact H.mul_mem (hQH hcomm) hy
  have hLN : L ≤ Subgroup.normalizer (H : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hfwdL w hw y
    · intro hy
      have h := hfwdL w⁻¹ (L.inv_mem hw) (w * y * w⁻¹) hy
      have e : w⁻¹ * (w * y * w⁻¹) * (w⁻¹)⁻¹ = y := by group
      rwa [e] at h
  have hL'N : L' ≤ Subgroup.normalizer (H : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hfwdL' w hw y
    · intro hy
      have h := hfwdL' w⁻¹ (L'.inv_mem hw) (w * y * w⁻¹) hy
      have e : w⁻¹ * (w * y * w⁻¹) * (w⁻¹)⁻¹ = y := by group
      rwa [e] at h
  have hHX : H ≤ L ⊔ L' := inf_le_left.trans le_sup_left
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHX]
  exact sup_le hLN hL'N

theorem step93L2Second_H_le_pCore (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) :
    LB M Q B ⊓ conjSubgroup h (LB M Q B) ≤
      inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) := by
  classical
  set L : Subgroup G := LB M Q B with hL
  set L' : Subgroup G := conjSubgroup h L with hL'
  set H : Subgroup G := L ⊓ L' with hH
  set X : Subgroup G := L ⊔ L' with hX
  have hHX : H ≤ X := inf_le_left.trans le_sup_left
  have hHnormal : (H.subgroupOf X).Normal := by
    simpa [hL, hL', hH, hX] using step93L2Second_H_normal hc hh
  have hH2 : IsPGroup 2 ↥(H.subgroupOf X) := by
    have hH2' : IsPGroup 2 ↥H := (isPGroup_LB_of_ctx hc).to_le inf_le_left
    exact hH2'.of_equiv (Subgroup.subgroupOfEquivOfLe hHX).symm
  have hcore : H.subgroupOf X ≤ pCore 2 X := le_sSup ⟨hHnormal, hH2⟩
  intro x hx
  change x ∈ (pCore 2 X).map X.subtype
  rw [Subgroup.mem_map]
  exact ⟨⟨x, hHX hx⟩, hcore (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end CFSG.RankThree.GF2n.Stroth80
