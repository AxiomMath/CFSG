module

public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.SimpleGoursat

public section

namespace CFSG

namespace FiveTransitive.NormalizerGoursat

open MulAction SubMulAction Subgroup

@[expose] noncomputable def centralizerSupportMap
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R) :
    R.normalizerMonoidHom.ker →*
      Subgroup.centralizer
        ({(((r : R) : P) : Equiv.Perm X).subtypePerm
            (fun _ =>
              (((r : R) : P) : Equiv.Perm X).apply_mem_support)} :
          Set
            (Equiv.Perm
              (((r : R) : P) : Equiv.Perm X).support)) := by
  classical
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let C : Subgroup N :=
    R.normalizerMonoidHom.ker
  let g : Equiv.Perm X := ((r : R) : P)
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp
      (N.subtype.comp C.subtype)
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
    (FiveTransitive.Degree19.centralizerToSupport g).comp
      centMap
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
  exact
    supportMap.codRestrict
      (Subgroup.centralizer
        ({gSupport} :
          Set (Equiv.Perm g.support)))
      hsupportMapMem

@[expose] noncomputable def centralizerCycleMap
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R) :
    R.normalizerMonoidHom.ker →*
      Equiv.Perm
        ((((r : R) : P) : Equiv.Perm X).subtypePerm
          (fun _ =>
            (((r : R) : P) : Equiv.Perm X).apply_mem_support)).cycleFactorsFinset :=
  (Equiv.Perm.OnCycleFactors.toPermHom
    ((((r : R) : P) : Equiv.Perm X).subtypePerm
      (fun _ =>
        (((r : R) : P) : Equiv.Perm X).apply_mem_support))).comp
    (centralizerSupportMap X P R r)

theorem alternatingGroup_le_of_fixed_action_cycle_kernel
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
    (hAutSmall :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      Nat.card (MulAut R) <
        Nat.card (alternatingGroup F))
    (hCycleSmall :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      Nat.card (centralizerCycleMap X P R r).range <
        Nat.card (alternatingGroup F))
    (hKernelNotDvd :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let g : Equiv.Perm X := ((r : R) : P)
      let gSupport : Equiv.Perm g.support :=
        g.subtypePerm (fun _ => g.apply_mem_support)
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom gSupport).ker) :
    alternatingGroup X ≤ P := by
  classical
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N :=
    R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let κ : N →* MulAut R :=
    R.normalizerMonoidHom
  let g : Equiv.Perm X := ((r : R) : P)
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hAlt' :
      alternatingGroup F ≤ ρ.range := by
    simpa only [N, SN, F, ρ] using hAlt
  have hAutSmall' :
      Nat.card (MulAut R) <
        Nat.card (alternatingGroup F) := by
    simpa only [N, SN, F] using hAutSmall
  have hCycleSmall' :
      Nat.card (centralizerCycleMap X P R r).range <
        Nat.card (alternatingGroup F) := by
    simpa only [N, SN, F] using hCycleSmall
  have hKernelNotDvd' :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom gSupport).ker := by
    simpa only [N, SN, F, g, gSupport] using hKernelNotDvd
  letI : IsSimpleGroup (alternatingGroup F) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card]
      simpa only [N, SN, F] using hfive)
  have hκrangeLe :
      Nat.card κ.range ≤ Nat.card (MulAut R) :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_subgroup_dvd_card κ.range)
  have hcentralLift
      (q : Equiv.Perm F)
      (hq : q ∈ alternatingGroup F) :
      ∃ n : N, ρ n = q ∧ κ n = 1 := by
    apply
      FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one
        N (Equiv.Perm F) (MulAut R)
          ρ κ (alternatingGroup F) hAlt'
    · omega
    · exact hq
  let C : Subgroup N :=
    κ.ker
  let ρC : C →* Equiv.Perm F :=
    ρ.comp C.subtype
  have hAltC :
      alternatingGroup F ≤ ρC.range := by
    intro q hq
    obtain ⟨n, hnFixed, hnCentral⟩ :=
      hcentralLift q hq
    let c : C := ⟨n, hnCentral⟩
    exact ⟨c, hnFixed⟩
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp
      (N.subtype.comp C.subtype)
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
    (FiveTransitive.Degree19.centralizerToSupport g).comp
      centMap
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
  let χ :
      Subgroup.centralizer
          ({gSupport} : Set (Equiv.Perm g.support)) →*
        Equiv.Perm gSupport.cycleFactorsFinset :=
    Equiv.Perm.OnCycleFactors.toPermHom gSupport
  let cycleMap :
      C →* Equiv.Perm gSupport.cycleFactorsFinset :=
    centralizerCycleMap X P R r
  have hcycleLift
      (q : Equiv.Perm F)
      (hq : q ∈ alternatingGroup F) :
      ∃ c : C, ρC c = q ∧ cycleMap c = 1 := by
    apply
      FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one
        C (Equiv.Perm F)
          (Equiv.Perm gSupport.cycleFactorsFinset)
          ρC cycleMap (alternatingGroup F) hAltC
    · simpa only [cycleMap] using hCycleSmall'
    · exact hq
  let D : Subgroup C :=
    cycleMap.ker
  let ρD : D →* Equiv.Perm F :=
    ρC.comp D.subtype
  have hAltD :
      alternatingGroup F ≤ ρD.range := by
    intro q hq
    obtain ⟨c, hcFixed, hcCycle⟩ :=
      hcycleLift q hq
    let d : D := ⟨c, hcCycle⟩
    exact ⟨d, hcFixed⟩
  have hkernelMapMem :
      ∀ d : D, supportCentMap (d : C) ∈ χ.ker := by
    intro d
    rw [MonoidHom.mem_ker]
    exact d.prop
  let kernelMap :
      D →* χ.ker :=
    (supportCentMap.comp D.subtype).codRestrict
      χ.ker hkernelMapMem
  have hkernelRangeNotDvd :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card kernelMap.range := by
    intro hdiv
    apply hKernelNotDvd'
    exact hdiv.trans
      (Subgroup.card_subgroup_dvd_card kernelMap.range)
  have hthreeCard :
      3 ≤ Fintype.card F := by
    have hfiveF :
        5 ≤ Fintype.card F := by
      simpa only [N, SN, F] using hfive
    omega
  let e : Fin 3 ↪ F :=
    Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr
        (by
          rw [Fintype.card_fin]
          exact hthreeCard))
  have heZeroOne : e 0 ≠ e 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1)
      (e.injective h)
  have heZeroTwo : e 0 ≠ e 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2)
      (e.injective h)
  have heOneTwo : e 1 ≠ e 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2)
      (e.injective h)
  let q : Equiv.Perm F :=
    Equiv.swap (e 0) (e 1) *
      Equiv.swap (e 0) (e 2)
  have hqThree : q.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same
      heZeroOne heZeroTwo heOneTwo
  have hqAlt : q ∈ alternatingGroup F :=
    hqThree.mem_alternatingGroup
  obtain ⟨d, hdFixed, hdSupport⟩ :=
    FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
      D (Equiv.Perm F) χ.ker
        ρD kernelMap (alternatingGroup F) hAltD
        hkernelRangeNotDvd q hqAlt
  have hdSupport' :
      supportCentMap ((d : D) : C) = 1 := by
    exact congrArg Subtype.val hdSupport
  let dC : C := d
  let dN : N := dC
  let dP : P := dN
  let dPerm : Equiv.Perm X := dP
  have hdFixSupport :
      ∀ x ∈ g.support,
        dPerm x = x := by
    intro x hx
    have happ :=
      congrFun
        (congrArg DFunLike.coe
          (congrArg Subtype.val hdSupport'))
        (⟨x, hx⟩ : g.support)
    exact congrArg Subtype.val happ
  have hFset :
      (F : Set X) =
        (g.support : Set X)ᶜ := by
    calc
      (F : Set X) =
          Function.fixedPoints g := by
        simpa only [N, SN, F, g] using hfixed
      _ = (g.support : Set X)ᶜ := by
        ext x
        simp only [Function.mem_fixedPoints_iff,
          Set.mem_compl_iff, Finset.mem_coe,
          Equiv.Perm.mem_support, not_not]
  have hdSupportSubset :
      (dPerm.support : Set X) ⊆ F := by
    intro x hx
    rw [hFset]
    rw [Set.mem_compl_iff]
    intro hxg
    exact
      Equiv.Perm.mem_support.mp hx
        (hdFixSupport x hxg)
  have hdInvariantF :
      ∀ x, dPerm x ∈ F ↔ x ∈ F := by
    intro x
    rw [hFset]
    constructor
    · intro hdx hxSupport
      apply hdx
      rw [hdFixSupport x hxSupport]
      exact hxSupport
    · intro hx hdxSupport
      have hfixedImage :=
        hdFixSupport (dPerm x) hdxSupport
      have heq : dPerm x = x :=
        dPerm.injective hfixedImage
      rw [heq] at hdxSupport
      exact hx hdxSupport
  let dF : Equiv.Perm F :=
    dPerm.subtypePerm hdInvariantF
  have hdFq : dF = q := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have happ :=
      congrFun
        (congrArg DFunLike.coe hdFixed) x
    exact congrArg Subtype.val happ
  let valEmbedding : F ↪ X :=
    Function.Embedding.subtype _
  have hsupportMap :
      Finset.map valEmbedding dF.support =
        dPerm.support := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      exact
        Equiv.Perm.mem_support.mp hy
          (Subtype.ext hfix)
    · intro hx
      have hxF : x ∈ F :=
        hdSupportSubset (by exact hx)
      let y : F := ⟨x, hxF⟩
      have hy : y ∈ dF.support := by
        apply Equiv.Perm.mem_support.mpr
        intro hfix
        exact
          Equiv.Perm.mem_support.mp hx
            (congrArg Subtype.val hfix)
      exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
  have hdSupportCard :
      dPerm.support.card = 3 := by
    calc
      dPerm.support.card =
          (Finset.map valEmbedding dF.support).card := by
        rw [hsupportMap]
      _ = dF.support.card :=
        Finset.card_map valEmbedding
      _ = q.support.card := by
        rw [hdFq]
      _ = 3 := hqThree.card_support
  have hdPermNe : dPerm ≠ 1 := by
    intro hdOne
    rw [hdOne, Equiv.Perm.support_one] at hdSupportCard
    norm_num at hdSupportCard
  apply
    FiveTransitive.Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 hdegree dP.prop
  · exact hdPermNe
  · change dPerm.support.card ≤ 5
    rw [hdSupportCard]
    norm_num

end FiveTransitive.NormalizerGoursat

end CFSG
