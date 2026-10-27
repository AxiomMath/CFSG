module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SupDecomposition
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.UpperCentralTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_upperCentralSeries_two_of_sup_cover
    {P L Q X : Subgroup G}
    (hXdecomp : X ≤ Q ⊔ centralizerBar P L)
    (hCQ : ∀ c ∈ centralizerBar P L, ∀ q ∈ Q, c * q = q * c)
    (hQQ : ⁅Q, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype)
    (hXcard : Nat.card X = 3) :
    X.subgroupOf (Q ⊔ X) ≤ Subgroup.upperCentralSeries ↥(Q ⊔ X) 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXcyc : IsCyclic ↥X := isCyclic_of_card_dvd_prime (p := 3) (by rw [hXcard])
  have hXcomm_amb : ∀ x ∈ X, ∀ x' ∈ X, x * x' = x' * x := by
    haveI : IsCyclic ↥X := hXcyc
    letI : CommGroup ↥X := hXcyc.commGroup
    intro x hx x' hx'
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥X) (⟨x', hx'⟩ : ↥X))
  have hcomm_amb : ∀ x ∈ X, ∀ q ∈ Q, ⁅x, q⁆ ∈ (Subgroup.center ↥Q).map Q.subtype := by
    intro x hx q hq
    exact commutator_mem_center_of_mem_sup (hXdecomp hx) hCQ hQQ hq
  have hZcentral_amb : ∀ x ∈ X, ∀ z ∈ (Subgroup.center ↥Q).map Q.subtype,
      x * z = z * x := by
    intro x hx z hz
    exact centralizes_center_of_mem_sup (hXdecomp hx) hCQ hz
  let W : Subgroup G := Q ⊔ X
  change X.subgroupOf W ≤ Subgroup.upperCentralSeries ↥W 2
  have hQW : Q ≤ W := le_sup_left
  have hmap_center :
      ((Subgroup.center ↥(Q.subgroupOf W)).map (Q.subgroupOf W).subtype).map W.subtype =
        (Subgroup.center ↥Q).map Q.subtype := by
    have hcomp : W.subtype.comp (Q.subgroupOf W).subtype =
        Q.subtype.comp (Subgroup.subgroupOfEquivOfLe hQW) := by
      ext y
      rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.map_center_eq]
  have center_mem_W : ∀ (z : ↥W),
      (z : G) ∈ (Subgroup.center ↥Q).map Q.subtype →
        z ∈ (Subgroup.center ↥(Q.subgroupOf W)).map (Q.subgroupOf W).subtype := by
    intro z hz
    obtain ⟨xQ, hxQcenter, hxQeq⟩ := Subgroup.mem_map.mp hz
    let e := Subgroup.subgroupOfEquivOfLe hQW
    have hcenter : e.symm xQ ∈ Subgroup.center ↥(Q.subgroupOf W) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact Subgroup.mem_center_iff.mp hxQcenter (e y)
    refine Subgroup.mem_map.mpr ⟨e.symm xQ, hcenter, ?_⟩
    apply Subtype.ext
    change (xQ : G) = (z : G)
    exact hxQeq
  have hsup : (Q.subgroupOf W) ⊔ (X.subgroupOf W) = ⊤ :=
    codisjoint_iff.mp (by
      simpa [W] using Subgroup.codisjoint_subgroupOf_sup Q X)
  have hXcomm : ∀ x ∈ X.subgroupOf W, ∀ x' ∈ X.subgroupOf W, x * x' = x' * x := by
    intro x hx x' hx'
    apply Subtype.ext
    exact hXcomm_amb (x : G) hx (x' : G) hx'
  have hcomm : ∀ x ∈ X.subgroupOf W, ∀ q ∈ Q.subgroupOf W,
      ⁅x, q⁆ ∈ (Subgroup.center ↥(Q.subgroupOf W)).map (Q.subgroupOf W).subtype := by
    intro x hx q hq
    have hz : ⁅(x : G), (q : G)⁆ ∈ (Subgroup.center ↥Q).map Q.subtype :=
      hcomm_amb (x : G) hx (q : G) hq
    have hz' : W.subtype (⁅x, q⁆ : ↥W) ∈ (Subgroup.center ↥Q).map Q.subtype := by
      rw [map_commutatorElement]
      exact hz
    exact center_mem_W (⁅x, q⁆ : ↥W) hz'
  have hZcentral : ∀ x ∈ X.subgroupOf W,
      ∀ z ∈ (Subgroup.center ↥(Q.subgroupOf W)).map (Q.subgroupOf W).subtype,
        x * z = z * x := by
    intro x hx z hz
    have hzamb : (z : G) ∈ (Subgroup.center ↥Q).map Q.subtype := by
      rw [← hmap_center]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    apply Subtype.ext
    exact hZcentral_amb (x : G) hx (z : G) hzamb
  exact le_upperCentralSeries_two_of_commutator_le_center
    (W := ↥W) (Q := Q.subgroupOf W) (X := X.subgroupOf W)
    hsup hXcomm hcomm hZcentral

theorem le_map_upperCentralSeries_two_of_sup_cover
    {P L Q X : Subgroup G}
    (hXdecomp : X ≤ Q ⊔ centralizerBar P L)
    (hCQ : ∀ c ∈ centralizerBar P L, ∀ q ∈ Q, c * q = q * c)
    (hQQ : ⁅Q, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype)
    (hXcard : Nat.card X = 3) :
    X ≤ (Subgroup.upperCentralSeries ↥(Q ⊔ X) 2).map (Q ⊔ X).subtype := by
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, Subgroup.mem_sup_right hx⟩, ?_, rfl⟩
  exact le_upperCentralSeries_two_of_sup_cover hXdecomp hCQ hQQ hXcard hx

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
