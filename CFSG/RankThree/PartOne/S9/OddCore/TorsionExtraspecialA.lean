module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.GroupTheory.SteinbergBMExtraspecialCentralProduct
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG CFSG.RankThree.GroupTheory Subgroup
open scoped commutatorElement

section Shape

variable {G : Type*} [Group G]

theorem map_subtype_center (D : Subgroup G) :
    (Subgroup.center ↥D).map D.subtype = D ⊓ Subgroup.centralizer (D : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun g hg => ?_⟩
    have := Subgroup.mem_center_iff.1 hy ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxD, hx⟩
    refine ⟨⟨x, hxD⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (hx g g.2)

theorem isExtraspecialPGroup_of_shape {q : ℕ} {D : Subgroup G} (hDq : IsPGroup q D)
    (hcard : Nat.card (⁅D, D⁆ : Subgroup G) = q)
    (hZ : D ⊓ Subgroup.centralizer (D : Set G) = ⁅D, D⁆)
    (hΦ : inSubgroup frattini D = ⁅D, D⁆) : IsExtraspecialPGroup q D := by
  have hinj := Subgroup.map_injective (D.subtype_injective)
  refine ⟨hDq, ?_, ?_, ?_⟩
  · apply hinj
    rw [OddCore37.map_subtype_commutator, map_subtype_center, hZ]
  · apply hinj
    rw [map_subtype_center, hZ, ← hΦ]
    rfl
  · rw [← Subgroup.card_map_of_injective D.subtype_injective, map_subtype_center, hZ, hcard]

end Shape

theorem exists_mul_of_central_product {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {R Q D : Subgroup G} [hQn : Q.Normal] (hQp : IsPGroup q Q) (hDQ : D ≤ Q)
    [hDn : D.Normal] (hExt : IsExtraspecialPGroup q D)
    (hΦZ : inSubgroup frattini D = D ⊓ Subgroup.centralizer (D : Set G))
    (hirr : ∀ X : Subgroup G, inSubgroup frattini D ≤ X → X ≤ D →
      R ≤ Subgroup.normalizer (X : Set G) → X = inSubgroup frattini D ∨ X = D) :
    ∀ x ∈ Q, ∃ d ∈ D, ∃ c ∈ Q ⊓ Subgroup.centralizer (D : Set G), x = d * c := by
  classical
  have hD'ext : IsExtraspecialPGroup q ↥(D.subgroupOf Q) :=
    isExtraspecialPGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDQ).symm hExt
  set D' : Subgroup ↥Q := D.subgroupOf Q with hD'
  set H : Subgroup (MulAut ↥Q) := ((MulAut.conjNormal (H := Q)).comp R.subtype).range with hH
  have hHD : ∀ h ∈ H, ∀ x ∈ D', h x ∈ D' := by
    rintro _ ⟨r, rfl⟩ x hx
    change ((MulAut.conjNormal (H := Q) (r : G) x : ↥Q) : G) ∈ D
    rw [MulAut.conjNormal_apply]
    exact hDn.conj_mem x hx r
  have hcenter : ∀ z : ↥Q, z ∈ (Subgroup.center ↥D').map D'.subtype ↔
      (z : G) ∈ D ⊓ Subgroup.centralizer (D : Set G) := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have := Subgroup.mem_center_iff.1 hy ⟨⟨g, hDQ hg⟩, hg⟩
      exact congrArg (fun w : ↥D' => ((w : ↥Q) : G)) this
    · rintro ⟨hzD, hz⟩
      refine ⟨⟨z, hzD⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hz (g : G) g.2
  have hprod := (SteinbergBM.normal_extraspecial_irreducible_central_product
    hq hQp D' hD'ext H hHD (fun X hZX hXD hXH => ?_)).1
  · intro x hx
    have hx' : (⟨x, hx⟩ : ↥Q) ∈ (Set.univ : Set ↥Q) := Set.mem_univ _
    rw [← hprod] at hx'
    obtain ⟨d, hd, c, hc, hdc⟩ := hx'
    refine ⟨d, hd, c, ⟨c.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩, ?_⟩
    · have := Subgroup.mem_centralizer_iff.1 hc ⟨g, hDQ hg⟩ hg
      exact congrArg Subtype.val this
    · exact (congrArg Subtype.val hdc).symm
  ·
    set X' : Subgroup G := X.map Q.subtype with hX'
    have hX'D : X' ≤ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hXD hx
    have hΦX' : inSubgroup frattini D ≤ X' := by
      intro z hz
      rw [hΦZ] at hz
      have hzQ : z ∈ Q := hDQ hz.1
      have h1 : (⟨z, hzQ⟩ : ↥Q) ∈ (Subgroup.center ↥D').map D'.subtype := (hcenter _).2 hz
      exact ⟨⟨z, hzQ⟩, hZX h1, rfl⟩
    have hRX' : R ≤ Subgroup.normalizer (X' : Set G) := by
      refine le_normalizer_of_forall fun r hr y hy => ?_
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨MulAut.conjNormal (H := Q) r x, hXH _ ⟨⟨r, hr⟩, rfl⟩ x hx, ?_⟩
      rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]
    rcases hirr X' hΦX' hX'D hRX' with h | h
    · left
      refine le_antisymm (fun x hx => ?_) hZX
      have hxX' : (x : G) ∈ X' := ⟨x, hx, rfl⟩
      rw [h, hΦZ] at hxX'
      exact (hcenter x).2 hxX'
    · right
      refine le_antisymm hXD (fun d hd => ?_)
      have hdD : (d : G) ∈ D := hd
      rw [← h] at hdD
      obtain ⟨x, hx, hxd⟩ := hdD
      rw [Subtype.ext hxd] at hx
      exact hx

end CFSG.RankThree.PartOne.Torsion37
