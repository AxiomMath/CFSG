module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
public import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1617

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
open scoped Pointwise

theorem isElemAbelian_map' {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {p : ℕ}
    {B : Subgroup X} (hB : CFSG.Assembly.IsElemAbelian p B) :
    CFSG.Assembly.IsElemAbelian p (B.map f) := CFSG.SectionRank.isElemAbelian_map hB _

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {D : Subgroup G}
    (hD : CFSG.Assembly.IsElemAbelian p D) (L : Subgroup G) :
    CFSG.Assembly.IsElemAbelian p (D.subgroupOf L) := CFSG.Open.IsElemAbelian.subgroupOf hD L

theorem card_subgroupOf_of_le {G : Type*} [Group G] {D L : Subgroup G} (h : D ≤ L) :
    Nat.card (D.subgroupOf L) = Nat.card D :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

noncomputable abbrev conjL {G : Type*} [Group G] (L : Subgroup G) {h : G}
    (hh : h ∈ Subgroup.normalizer (L : Set G)) : MulAut L :=
  L.normalizerMonoidHom ⟨h, hh⟩

theorem conjL_apply_coe {G : Type*} [Group G] (L : Subgroup G) {h : G}
    (hh : h ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    ((conjL L hh l : L) : G) = h * l * h⁻¹ :=
  Sec4.normalizerMonoidHom_apply_coe hh l

theorem exists_eq_zpow_mul {G : Type*} [Group G] {c : G} {D : Subgroup G}
    (hD : D ≤ Subgroup.centralizer ({c} : Set G)) {f : G}
    (hf : f ∈ Subgroup.zpowers c ⊔ D) : ∃ k : ℤ, ∃ d ∈ D, f = c ^ k * d := by
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hD hd)
  have hf' : f ∈ (Subgroup.zpowers c : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN]
    exact hf
  obtain ⟨_, hw, d, hd, rfl⟩ := hf'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨k, d, hd, rfl⟩

end CFSG.RankThree.PartTwo.Sec16.Proof1617
