module

public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.SimpleGoursat

public section

namespace CFSG

namespace FiveTransitive.NormalizerGoursat

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_fixed_action_of_ker
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
    (hAltKer :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let ρ : N →* Equiv.Perm F :=
        MulAction.toPermHom N F
      let κ : N →* MulAut R :=
        R.normalizerMonoidHom
      let C : Subgroup N := κ.ker
      alternatingGroup F ≤
        (ρ.comp C.subtype).range)
    (hSupportSmall :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let g : Equiv.Perm X := ((r : R) : P)
      let gSupport : Equiv.Perm g.support :=
        g.subtypePerm (fun _ => g.apply_mem_support)
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) <
        Nat.card (alternatingGroup F)) :
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
  have hSupportSmall' :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) <
        Nat.card (alternatingGroup F) := by
    simpa only [N, SN, F, g, gSupport] using
      hSupportSmall
  letI : IsSimpleGroup (alternatingGroup F) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card]
      simpa only [N, SN, F] using hfive)
  let C : Subgroup N :=
    κ.ker
  let ρC : C →* Equiv.Perm F :=
    ρ.comp C.subtype
  have hAltC :
      alternatingGroup F ≤ ρC.range := by
    simpa only [N, SN, F, ρ, κ, C, ρC] using
      hAltKer
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
  have hsupportRangeLe :
      Nat.card supportCentMap.range ≤
        Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_subgroup_dvd_card
        supportCentMap.range)
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
  have hqThree : q.IsThreeCycle := by
    exact
      Equiv.Perm.isThreeCycle_swap_mul_swap_same
        heZeroOne heZeroTwo heOneTwo
  have hqAlt : q ∈ alternatingGroup F :=
    hqThree.mem_alternatingGroup
  obtain ⟨c, hcFixed, hcSupport⟩ :=
    FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one
      C (Equiv.Perm F)
        (Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)))
      ρC supportCentMap
        (alternatingGroup F) hAltC (by
          omega)
        q hqAlt
  let cN : N := c
  let cP : P := cN
  let cPerm : Equiv.Perm X := cP
  have hcFixSupport :
      ∀ x ∈ g.support,
        cPerm x = x := by
    intro x hx
    have happ :=
      congrFun
        (congrArg DFunLike.coe
          (congrArg Subtype.val hcSupport))
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
  have hcSupportSubset :
      (cPerm.support : Set X) ⊆ F := by
    intro x hx
    rw [hFset]
    rw [Set.mem_compl_iff]
    intro hxg
    exact
      Equiv.Perm.mem_support.mp hx
        (hcFixSupport x hxg)
  have hcInvariantF :
      ∀ x, cPerm x ∈ F ↔ x ∈ F := by
    intro x
    rw [hFset]
    constructor
    · intro hcx hxSupport
      apply hcx
      rw [hcFixSupport x hxSupport]
      exact hxSupport
    · intro hx hcxSupport
      have hfixedImage :=
        hcFixSupport (cPerm x) hcxSupport
      have heq : cPerm x = x :=
        cPerm.injective hfixedImage
      rw [heq] at hcxSupport
      exact hx hcxSupport
  let cF : Equiv.Perm F :=
    cPerm.subtypePerm hcInvariantF
  have hcFq : cF = q := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have happ :=
      congrFun
        (congrArg DFunLike.coe hcFixed) x
    exact congrArg Subtype.val happ
  let valEmbedding : F ↪ X :=
    Function.Embedding.subtype _
  have hsupportMap :
      Finset.map valEmbedding cF.support =
        cPerm.support := by
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
        hcSupportSubset
          (by exact hx)
      let y : F := ⟨x, hxF⟩
      have hy : y ∈ cF.support := by
        apply Equiv.Perm.mem_support.mpr
        intro hfix
        exact
          Equiv.Perm.mem_support.mp hx
            (congrArg Subtype.val hfix)
      exact
        Finset.mem_map.mpr
          ⟨y, hy, rfl⟩
  have hcSupportCard :
      cPerm.support.card = 3 := by
    calc
      cPerm.support.card =
          (Finset.map valEmbedding cF.support).card := by
        rw [hsupportMap]
      _ = cF.support.card :=
        Finset.card_map valEmbedding
      _ = q.support.card := by
        rw [hcFq]
      _ = 3 := hqThree.card_support
  have hcPermNe : cPerm ≠ 1 := by
    intro hcOne
    rw [hcOne, Equiv.Perm.support_one] at hcSupportCard
    norm_num at hcSupportCard
  apply
    FiveTransitive.Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 hdegree cP.prop
  · exact hcPermNe
  · change cPerm.support.card ≤ 5
    omega

private theorem alternatingGroup_le_of_fixed_action_of_not_dvd
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
    (hSupportSmall :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let g : Equiv.Perm X := ((r : R) : P)
      let gSupport : Equiv.Perm g.support :=
        g.subtypePerm (fun _ => g.apply_mem_support)
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) <
        Nat.card (alternatingGroup F)) :
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
  let C : Subgroup N := κ.ker
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
  have hAltKer :
      alternatingGroup F ≤
        (ρ.comp C.subtype).range := by
    intro q hq
    obtain ⟨n, hnFixed, hnCentral⟩ :=
      FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
        N (Equiv.Perm F) (MulAut R)
          ρ κ (alternatingGroup F) hAlt'
            hAutNotDvd' q hq
    exact ⟨⟨n, hnCentral⟩, hnFixed⟩
  apply
    alternatingGroup_le_of_fixed_action_of_ker
      X P hdegree h5 R r hfixed hfive hAlt
  · simpa only [N, SN, F, ρ, κ, C] using hAltKer
  · exact hSupportSmall

theorem alternatingGroup_le_of_fixed_action
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
    (hSupportSmall :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let g : Equiv.Perm X := ((r : R) : P)
      let gSupport : Equiv.Perm g.support :=
        g.subtypePerm (fun _ => g.apply_mem_support)
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) <
        Nat.card (alternatingGroup F)) :
    alternatingGroup X ≤ P := by
  classical
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N :=
    R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let κ : N →* MulAut R :=
    R.normalizerMonoidHom
  have hAutSmall' :
      Nat.card (MulAut R) <
        Nat.card (alternatingGroup F) := by
    simpa only [N, SN, F] using hAutSmall
  have hκrangeLe :
      Nat.card κ.range ≤ Nat.card (MulAut R) :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_subgroup_dvd_card κ.range)
  have hAutNotDvd :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card κ.range := by
    intro hdvd
    have hle :=
      Nat.le_of_dvd Nat.card_pos hdvd
    omega
  apply
    alternatingGroup_le_of_fixed_action_of_not_dvd
      X P hdegree h5 R r hfixed hfive hAlt
  · simpa only [N, SN, F, κ] using hAutNotDvd
  · exact hSupportSmall

theorem alternatingGroup_le_of_fixed_action_of_support_lift
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
    (hSupportLift :
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let F :=
        MulAction.fixedPoints (R.subgroupOf N) X
      let ρ : N →* Equiv.Perm F :=
        MulAction.toPermHom N F
      let g : Equiv.Perm X := ((r : R) : P)
      ∀ q : Equiv.Perm F,
        q ∈ alternatingGroup F →
        ∃ c : N, ρ c = q ∧
          ∀ x ∈ g.support,
            (((c : N) : P) : Equiv.Perm X) x = x) :
    alternatingGroup X ≤ P := by
  classical
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N :=
    R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let g : Equiv.Perm X := ((r : R) : P)
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
  have hqThree : q.IsThreeCycle := by
    exact
      Equiv.Perm.isThreeCycle_swap_mul_swap_same
        heZeroOne heZeroTwo heOneTwo
  have hqAlt : q ∈ alternatingGroup F :=
    hqThree.mem_alternatingGroup
  obtain ⟨cN, hcFixed, hcFixSupport⟩ :=
    hSupportLift q hqAlt
  let cP : P := cN
  let cPerm : Equiv.Perm X := cP
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
  have hcSupportSubset :
      (cPerm.support : Set X) ⊆ F := by
    intro x hx
    rw [hFset]
    rw [Set.mem_compl_iff]
    intro hxg
    exact
      Equiv.Perm.mem_support.mp hx
        (hcFixSupport x hxg)
  have hcInvariantF :
      ∀ x, cPerm x ∈ F ↔ x ∈ F := by
    intro x
    rw [hFset]
    constructor
    · intro hcx hxSupport
      apply hcx
      rw [hcFixSupport x hxSupport]
      exact hxSupport
    · intro hx hcxSupport
      have hfixedImage :=
        hcFixSupport (cPerm x) hcxSupport
      have heq : cPerm x = x :=
        cPerm.injective hfixedImage
      rw [heq] at hcxSupport
      exact hx hcxSupport
  let cF : Equiv.Perm F :=
    cPerm.subtypePerm hcInvariantF
  have hcFq : cF = q := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have happ :=
      congrFun
        (congrArg DFunLike.coe hcFixed) x
    exact congrArg Subtype.val happ
  let valEmbedding : F ↪ X :=
    Function.Embedding.subtype _
  have hsupportMap :
      Finset.map valEmbedding cF.support =
        cPerm.support := by
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
        hcSupportSubset
          (by exact hx)
      let y : F := ⟨x, hxF⟩
      have hy : y ∈ cF.support := by
        apply Equiv.Perm.mem_support.mpr
        intro hfix
        exact
          Equiv.Perm.mem_support.mp hx
            (congrArg Subtype.val hfix)
      exact
        Finset.mem_map.mpr
          ⟨y, hy, rfl⟩
  have hcSupportCard :
      cPerm.support.card = 3 := by
    calc
      cPerm.support.card =
          (Finset.map valEmbedding cF.support).card := by
        rw [hsupportMap]
      _ = cF.support.card :=
        Finset.card_map valEmbedding
      _ = q.support.card := by
        rw [hcFq]
      _ = 3 := hqThree.card_support
  have hcPermNe : cPerm ≠ 1 := by
    intro hcOne
    rw [hcOne, Equiv.Perm.support_one] at hcSupportCard
    norm_num at hcSupportCard
  apply
    FiveTransitive.Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 hdegree cP.prop
  · exact hcPermNe
  · change cPerm.support.card ≤ 5
    omega

end FiveTransitive.NormalizerGoursat

end CFSG
