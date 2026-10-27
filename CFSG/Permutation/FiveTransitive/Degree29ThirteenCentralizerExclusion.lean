module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer
public import CFSG.Permutation.FiveTransitive.CyclicNormalizerThreeImage
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree29ThirteenCentralizerExclusion

open MulAction FixedNormalizerAction Degree28ThirteenCentralizer

private theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (hcycleType : (u : Equiv.Perm X).cycleType = {13,13}) :
    Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set P)) ∣ 338 := by
  classical
  let g : Equiv.Perm X := u
  have hgsupport : g.support.card = 26 := by
    rw [← g.sum_cycleType, hcycleType]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (Subgroup.zpowers u : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapInjective :
      Function.Injective baseMap := by
    intro a b hab
    exact C.subtype_injective
      (P.subtype_injective hab)
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((q.prop u (Subgroup.mem_zpowers u)).symm)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (centralizerToSupport g).comp centMap
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hsupportMapMem :
      ∀ q : C, supportMap q ∈
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap q (g x.1) =
      g (baseMap q x.1)
    have hcomm : Commute (baseMap q) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap q).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      C →*
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) :=
    supportMap.codRestrict
      (Subgroup.centralizer
        ({gSupport} :
          Set (Equiv.Perm g.support)))
      hsupportMapMem
  have hsupportCentMapInjective :
      Function.Injective supportCentMap := by
    intro a b hab
    by_contra habNe
    let w : C := a * b⁻¹
    have hwNe : w ≠ 1 := by
      intro hw
      exact habNe (mul_inv_eq_one.mp hw)
    have hwSupportCentOne :
        supportCentMap w = 1 := by
      dsimp only [w]
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have hwSupportOne :
        supportMap w = 1 :=
      congrArg Subtype.val hwSupportCentOne
    let wP : P := w
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happly :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happly
    have hwSupportSubset :
        wPerm.support ⊆ g.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxg
      exact
        Equiv.Perm.mem_support.mp hx
          (hwFixSupport x hxg)
    have hwSupportCard :
        wPerm.support.card ≤ 3 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ = 3 := by
          rw [Finset.card_compl, hcard, hgsupport]
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply hbaseMapInjective
      rw [map_one]
      exact hwOne
    have hm := HighDegreeManningSupport.degree_le_two_mul_support
      P (by omega) h5 hnotAlt wP.prop hwPermNe
    change Fintype.card X ≤ 2 * wPerm.support.card at hm
    rw [hcard] at hm
    omega
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportTypeCard :
      Fintype.card g.support = 26 := by
    rw [Fintype.card_coe, hgsupport]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 338 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hcycleType,
      hsupportTypeCard]
    norm_num
  have hCdvdSupport : Nat.card C ∣ 338 := by
    rw [← hsupportCentralizerCard]
    exact Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective
  exact hCdvdSupport

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (hcycleType : (u : Equiv.Perm X).cycleType = {13,13})
    (hfixed : Nat.card (Fixed (X := X) (Subgroup.zpowers u)) = 3)
    (himage : Image (X := X) (Subgroup.zpowers u) = ⊤) : False := by
  let Q := Subgroup.zpowers u
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp himage
  have hthree := CyclicNormalizerThreeImage.three_dvd_centralizer_card Q hfixed f hf
  have hd := hthree.trans (centralizer_card_dvd P hcard h5 hnotAlt u hcycleType)
  norm_num at hd

end FiveTransitive.Degree29ThirteenCentralizerExclusion

end CFSG
