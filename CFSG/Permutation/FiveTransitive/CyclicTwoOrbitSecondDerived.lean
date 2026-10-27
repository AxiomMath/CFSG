module

public import CFSG.Permutation.FiveTransitive.AbelianOrbitCommutator
public import CFSG.Permutation.FiveTransitive.CyclicTwoOrbitNormalizerCommutator
public import CFSG.Permutation.FiveTransitive.TwoOrbitNormalizerCommutator

public section

namespace CFSG

namespace FiveTransitive.CyclicTwoOrbitSecondDerived

open MulAction NormalizerFixedComplement

variable {G X : Type*} [Group G] [Finite X] [MulAction G X]

private theorem fixes_points (Q : Subgroup G) [IsCyclic Q] (x : Normalizer Q)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
    let L := Subgroup.normalizer (R : Set (Normalizer Q))
    ∀ (a : L), a ∈ ⁅commutator L, commutator L⁆ →
      ∀ y : Domain (X := X) Q,
        NormalizerSevenOrbitCount.orbitPerm (X := X) Q x (Quotient.mk'' y) = Quotient.mk'' y →
        a.val • y = y := by
  let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
  let L := Subgroup.normalizer (R : Set (Normalizer Q))
  let D := (commutator L).map L.subtype
  let : IsCyclic (Inside Q) :=
    (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).isCyclic.mpr inferInstance
  have hcentral : D ≤ Subgroup.centralizer (Inside Q : Set (Normalizer Q)) := by
    rintro n ⟨a, ha, rfl⟩
    have hc := CyclicTwoOrbitNormalizerCommutator.centralizes Q R a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc q.val hq
  dsimp only
  intro a ha y hy
  have haD : a.val ∈ ⁅D, D⁆ := by
    rw [← Subgroup.map_commutator]
    exact ⟨a, ha, rfl⟩
  apply AbelianOrbitCommutator.commutator_fixes_orbit (Inside Q) D hcentral
    (Quotient.mk'' y) ?_ a.val haD y rfl
  rintro n ⟨b, hb, rfl⟩ z hz
  change NormalizerSevenOrbitCount.orbitPerm (X := X) Q b.val (Quotient.mk'' z) = _
  rw [hz]
  exact TwoOrbitNormalizerCommutator.fixes_orbits Q x horbits b hb _ hy

private theorem outside_fixed_ge_twice_card [Finite G]
    (Q : Subgroup G) [IsCyclic Q]
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
    let L := Subgroup.normalizer (R : Set (Normalizer Q))
    ∀ (a : L), a ∈ ⁅commutator L, commutator L⁆ →
      2 * Nat.card Q ≤ (fixedBy X a.val.val \ fixedPoints Q X).ncard := by
  dsimp only
  intro a ha
  let P := fun O : orbitRel.Quotient (Inside Q) (Domain (X := X) Q) =>
    NormalizerSevenOrbitCount.orbitPerm (X := X) Q x O = O
  have hcount := FreeActionTransporterCount.card_orbit_preimage (free_inside Q hfree) P
  have hinj : Function.Injective
      (fun y : {y : Domain (X := X) Q // P (Quotient.mk'' y)} =>
        (⟨y.val, fixes_points Q x horbits a ha y.val y.property⟩ : fixedBy (Domain (X := X) Q) a.val)) := by
    intro y z he
    exact Subtype.ext (congrArg (fun t : fixedBy (Domain (X := X) Q) a.val => t.val) he)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcount] at hle
  have hInside : Nat.card (Inside Q) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv
  rw [hInside] at hle
  have hP : Nat.card {O : orbitRel.Quotient (Inside Q) (Domain (X := X) Q) // P O} = 2 := horbits
  rw [hP, fixed_card] at hle
  simpa only [Nat.mul_comm] using hle

theorem card_le_two [Finite G]
    (hbound : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) [IsCyclic Q]
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
    let L := Subgroup.normalizer (R : Set (Normalizer Q))
    let D := commutator L
    ∀ (y : D), y ∈ commutator D → IsPGroup 2 (Subgroup.zpowers y) →
      y.val.val.val ≠ 1 → 3 ≤ (fixedBy X y.val.val.val ∩ fixedPoints Q X).ncard →
      Nat.card Q ≤ 2 := by
  let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
  let L := Subgroup.normalizer (R : Set (Normalizer Q))
  let D := commutator L
  dsimp only
  intro y hy hy2 hyne hlocal
  have hm : (commutator D).map D.subtype = ⁅D, D⁆ := by
    rw [map_commutator_eq, Subgroup.range_subtype]
  have hyD : y.val ∈ ⁅D, D⁆ := by
    rw [← hm]
    exact ⟨y, hy, rfl⟩
  have hout := outside_fixed_ge_twice_card Q hfree x horbits y.val hyD
  let f : D →* G := (Normalizer Q).subtype.comp (L.subtype.comp D.subtype)
  have hp : IsPGroup 2 (Subgroup.zpowers y.val.val.val) := by
    have hh := hy2.map f
    rw [MonoidHom.map_zpowers] at hh
    exact hh
  have hne : (⟨y.val.val.val, Subgroup.mem_zpowers y.val.val.val⟩ :
      Subgroup.zpowers y.val.val.val) ≠ 1 := by
    intro he
    exact hyne (congrArg Subtype.val he)
  have hb := TwoGroupCosetFixedBound.fixed_le 7 hbound
    (Subgroup.zpowers y.val.val.val) hp ⟨y.val.val.val, Subgroup.mem_zpowers _⟩ hne
  change (fixedBy X y.val.val.val).ncard ≤ 7 at hb
  have htotal := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (fixedBy X y.val.val.val) (fixedPoints Q X)
  omega

end FiveTransitive.CyclicTwoOrbitSecondDerived

end CFSG
