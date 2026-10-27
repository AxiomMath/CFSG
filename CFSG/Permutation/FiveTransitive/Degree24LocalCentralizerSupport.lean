module

public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24SmallSupport

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem local_centralizer_card_dvd_support_centralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (T : Subgroup (fixingSubgroup P s))
    (u : T)
    (hsupport :
      12 ≤
        (((((u : T) : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card)) :
    let g : Equiv.Perm X :=
      (((u : T) : fixingSubgroup P s) : P)
    let gSupport : Equiv.Perm g.support :=
      g.subtypePerm (fun _ => g.apply_mem_support)
    Nat.card
        (Subgroup.centralizer
          (T : Set (fixingSubgroup P s))) ∣
      Nat.card
        (Subgroup.centralizer
          ({gSupport} : Set (Equiv.Perm g.support))) := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let g : Equiv.Perm X := (((u : T) : H) : P)
  let C : Subgroup H :=
    Subgroup.centralizer (T : Set H)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp (H.subtype.comp C.subtype)
  have hbaseMapInjective : Function.Injective baseMap := by
    intro a b hab
    exact
      C.subtype_injective
        (H.subtype_injective
          (P.subtype_injective hab))
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqCommuteH : Commute (q.1 : H) (u : H) :=
      (q.prop (u : H) u.prop).symm
    exact
      congrArg Subtype.val
        (congrArg Subtype.val hqCommuteH)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (Degree19.centralizerToSupport g).comp centMap
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
    let wH : H := w
    let wP : P := wH
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happ :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happ
    have hwFixS :
        ∀ x ∈ s, wPerm x = x := by
      exact (mem_fixingSubgroup_iff P).mp wH.prop
    have hSupportDisjoint :
        Disjoint (g.support : Set X) s := by
      rw [Set.disjoint_left]
      intro x hxg hxs
      exact
        Equiv.Perm.mem_support.mp hxg
          ((mem_fixingSubgroup_iff P).mp
            (u : H).prop x hxs)
    let U : Set X := (g.support : Set X) ∪ s
    have hUncard :
        U.ncard = g.support.card + 5 := by
      change
        ((g.support : Set X) ∪ s).ncard =
          g.support.card + 5
      rw [Set.ncard_union_eq hSupportDisjoint,
        Set.ncard_coe_finset, hs]
    have hUcomplCard :
        Uᶜ.ncard + U.ncard = 24 := by
      have htotal := Set.ncard_add_ncard_compl U
      rw [Nat.card_eq_fintype_card, hcard] at htotal
      omega
    have hUcomplLe : Uᶜ.ncard ≤ 7 := by
      have hsupport' : 12 ≤ g.support.card := by
        simpa only [g, H] using hsupport
      omega
    have hwSupportSubset :
        (wPerm.support : Set X) ⊆ Uᶜ := by
      intro x hx
      rw [Set.mem_compl_iff]
      intro hxU
      apply Equiv.Perm.mem_support.mp hx
      rcases hxU with hxg | hxs
      · exact hwFixSupport x hxg
      · exact hwFixS x hxs
    have hwSupportCard :
        wPerm.support.card ≤ 7 := by
      rw [← Set.ncard_coe_finset]
      exact
        (Set.ncard_le_ncard hwSupportSubset).trans
          hUcomplLe
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply hbaseMapInjective
      rw [map_one]
      exact hwOne
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 wP.prop hwPermNe hwSupportCard)
  exact
    Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective

end FiveTransitive.Degree24

end CFSG
