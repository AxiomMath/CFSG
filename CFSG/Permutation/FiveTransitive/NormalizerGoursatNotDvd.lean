module

public import CFSG.Permutation.FiveTransitive.NormalizerGoursat

public section

namespace CFSG

namespace FiveTransitive.NormalizerGoursatNotDvd

open MulAction SubMulAction Subgroup

theorem alternatingGroup_le_of_fixed_action_of_two_not_dvd
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (R : Subgroup P) (r : R)
    [fixedFintype :
      Fintype
        (MulAction.fixedPoints
          (R.subgroupOf
            (Subgroup.normalizer (R : Set P))) X)]
    (hfixed :
      MulAction.fixedPoints
          (R.subgroupOf
            (Subgroup.normalizer (R : Set P))) X =
        Function.fixedPoints
          (((r : R) : P) : Equiv.Perm X))
    (hfive :
      5 ≤ Fintype.card
        (MulAction.fixedPoints
          (R.subgroupOf
            (Subgroup.normalizer (R : Set P))) X))
    (hAlt :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      alternatingGroup F ≤
        (MulAction.toPermHom N F).range)
    (hAutNotDvd :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let κ : N →* MulAut R :=
        R.normalizerMonoidHom
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card κ.range)
    (hSupportNotDvd :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let g : Equiv.Perm X := ((r : R) : P)
      let gSupport : Equiv.Perm g.support :=
        g.subtypePerm (fun _ => g.apply_mem_support)
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support)))) :
    alternatingGroup X ≤ P := by
  classical
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N := R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let κ : N →* MulAut R :=
    R.normalizerMonoidHom
  let C : Subgroup N := κ.ker
  let ρC : C →* Equiv.Perm F :=
    ρ.comp C.subtype
  have hAlt' :
      alternatingGroup F ≤ ρ.range := by
    simpa only [N, SN, F, ρ] using hAlt
  have hAutNotDvd' :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card κ.range := by
    simpa only [N, SN, F, κ] using hAutNotDvd
  letI : IsSimpleGroup (alternatingGroup F) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card]
      simpa only [N, SN, F] using hfive)
  have hAltC :
      alternatingGroup F ≤ ρC.range := by
    intro q hq
    obtain ⟨n, hnFixed, hnCentral⟩ :=
      SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
        N (Equiv.Perm F) (MulAut R)
          ρ κ (alternatingGroup F) hAlt'
            hAutNotDvd' q hq
    exact ⟨⟨n, hnCentral⟩, hnFixed⟩
  let g : Equiv.Perm X := ((r : R) : P)
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp (N.subtype.comp C.subtype)
  have hbaseMapMem :
      ∀ c : C, baseMap c ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro c
    have hcCentral :
        (c.1 : N) ∈
          (Subgroup.centralizer (R : Set P)).subgroupOf N := by
      rw [← R.normalizerMonoidHom_ker]
      exact c.prop
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcCommute :
        Commute ((c.1 : N) : P) (r : P) :=
      (hcCentral (r : P) r.prop).symm
    exact congrArg Subtype.val hcCommute
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
  have hsupportMapMem :
      ∀ c : C, supportMap c ∈
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) := by
    intro c
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap c (g x.1) =
      g (baseMap c x.1)
    have hcomm : Commute (baseMap c) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap c).prop
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
  have hSupportNotDvd' :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) := by
    simpa only [N, SN, F, g, gSupport] using
      hSupportNotDvd
  have hSupportRangeNotDvd :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card supportCentMap.range := by
    intro hdvd
    apply hSupportNotDvd'
    exact hdvd.trans
      (Subgroup.card_subgroup_dvd_card
        supportCentMap.range)
  have hSupportLift :
      ∀ q : Equiv.Perm F,
        q ∈ alternatingGroup F →
        ∃ c : N, ρ c = q ∧
          ∀ x ∈ g.support,
            (((c : N) : P) : Equiv.Perm X) x = x := by
    intro q hq
    obtain ⟨c, hcFixed, hcSupport⟩ :=
      SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
        C (Equiv.Perm F)
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support)))
        ρC supportCentMap (alternatingGroup F)
          hAltC hSupportRangeNotDvd q hq
    refine ⟨(c : N), hcFixed, ?_⟩
    intro x hx
    have happ :=
      congrFun
        (congrArg DFunLike.coe
          (congrArg Subtype.val hcSupport))
        (⟨x, hx⟩ : g.support)
    exact congrArg Subtype.val happ
  apply
    NormalizerGoursat.alternatingGroup_le_of_fixed_action_of_support_lift
      X P hdegree h5 R r hfixed hfive
  simpa only [N, SN, F, ρ, g] using hSupportLift

end FiveTransitive.NormalizerGoursatNotDvd

end CFSG
