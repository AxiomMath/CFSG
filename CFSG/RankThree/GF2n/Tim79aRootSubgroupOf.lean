module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
import CFSG.GroupTheory.PCore.SubgroupOfNormalizer
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open
open scoped commutatorElement

variable {K : Type} [Group K] {X T : Subgroup K}

theorem eq_or_eq_of_rootIrrModel (hTX : T ≤ X) (hIrr : RootIrrModel ↥X (T.subgroupOf X))
    {Y : Subgroup K} (hTY : T ≤ Y)
    (hYR : Y ≤ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)))
    (hYN : X ⊓ Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (Y : Set K)) :
    Y = T ∨ Y = inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) := by
  have hR := CFSG.GroupTheory.map_subtype_pCoreOf_normalizer_subgroupOf 2 hTX
  have hYX : Y ≤ X := hYR.trans
    ((CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_left)
  have h1 : Y.subgroupOf X ≤
      pCoreOf 2 (Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X)) := by
    intro y hy
    have hy' := hYR (Subgroup.mem_subgroupOf.1 hy)
    rw [← hR] at hy'
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy'
    rwa [show z = y from Subtype.ext hzy] at hz
  have h2 : ∀ b ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X),
      ∀ r ∈ Y.subgroupOf X, b * r * b⁻¹ ∈ Y.subgroupOf X := by
    intro b hb r hr
    rw [← Subgroup.subgroupOf_normalizer_eq hTX, Subgroup.mem_subgroupOf] at hb
    have hbN : (b : K) ∈ Subgroup.normalizer (Y : Set K) := hYN ⟨b.2, hb⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 hbN _).1 (Subgroup.mem_subgroupOf.1 hr)
  rcases hIrr (Y.subgroupOf X)
      (fun _ hx => Subgroup.mem_subgroupOf.2 (hTY (Subgroup.mem_subgroupOf.1 hx))) h1 h2 with h | h
  · left
    rw [← Subgroup.map_subgroupOf_eq_of_le hYX, h, Subgroup.map_subgroupOf_eq_of_le hTX]
  · right
    rw [← Subgroup.map_subgroupOf_eq_of_le hYX, h, hR]

theorem exists_mem_pCore_inv_mul_mem_centralizer_of_rootS2Model [X.Normal] (hTX : T ≤ X)
    (hS2 : RootS2Model ↥X (T.subgroupOf X)) {l : K}
    (hl : l ∈ Subgroup.centralizer (T : Set K))
    (hlR : ∀ b ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)), ⁅l, b⁆ ∈ T) :
    ∃ s ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)),
      s⁻¹ * l ∈ Subgroup.centralizer (X : Set K) := by
  have hR := CFSG.GroupTheory.map_subtype_pCoreOf_normalizer_subgroupOf 2 hTX
  have hmem : ∀ b ∈ pCoreOf 2 (Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X)),
      (b : K) ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) := fun b hb => by
    rw [← hR]
    exact Subgroup.mem_map_of_mem _ hb
  have hfix : ∀ a ∈ T.subgroupOf X, MulAut.conjNormal l a = a := fun a ha => by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply,
      (Subgroup.mem_centralizer_iff.1 hl (a : K) (Subgroup.mem_subgroupOf.1 ha)).symm,
      mul_inv_cancel_right]
  have htriv : ∀ b ∈ pCoreOf 2 (Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X)),
      b⁻¹ * MulAut.conjNormal l b ∈ T.subgroupOf X := fun b hb => by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    have e : (b : K)⁻¹ * (l * (b : K) * l⁻¹) = ⁅l, (b : K)⁻¹⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact T.inv_mem (hlR _ (inv_mem (hmem b hb)))
  obtain ⟨s, hs, hα⟩ := hS2 (MulAut.conjNormal l) hfix htriv
  refine ⟨(s : K), hmem s hs, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : l * x * l⁻¹ = (s : K) * x * (s : K)⁻¹ := by
    calc l * x * l⁻¹ = ↑(MulAut.conjNormal l ⟨x, hx⟩) :=
          (MulAut.conjNormal_apply l ⟨x, hx⟩).symm
      _ = ↑(MulAut.conj s ⟨x, hx⟩) := by rw [DFunLike.congr_fun hα ⟨x, hx⟩]
      _ = (s : K) * x * (s : K)⁻¹ := by rw [MulAut.conj_apply]; simp
  calc x * ((s : K)⁻¹ * l) = (s : K)⁻¹ * ((s : K) * x * (s : K)⁻¹) * l := by group
    _ = (s : K)⁻¹ * (l * x * l⁻¹) * l := by rw [h1]
    _ = (s : K)⁻¹ * l * x := by group

theorem mem_pCore_sup_centralizer_of_rootS2Model [X.Normal] (hTX : T ≤ X)
    (hS2 : RootS2Model ↥X (T.subgroupOf X)) {l : K}
    (hl : l ∈ Subgroup.centralizer (T : Set K))
    (hlR : ∀ b ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)), ⁅l, b⁆ ∈ T) :
    l ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) ⊔
      Subgroup.centralizer (X : Set K) := by
  obtain ⟨s, hs, hc⟩ := exists_mem_pCore_inv_mul_mem_centralizer_of_rootS2Model hTX hS2 hl hlR
  have h3 := Subgroup.mul_mem_sup hs hc
  rwa [mul_inv_cancel_left] at h3

end CFSG.RankThree.GF2n.Tim79a
