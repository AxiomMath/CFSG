module

public import CFSG.Permutation.FiveTransitive.NormalizerGoursatCycleKernel
public import CFSG.Permutation.FiveTransitive.Degree24Order96Normalizer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open Subgroup

private theorem card_lt_three_hundred_sixty_of_small_normal
    (F : Type) [Fintype F] [DecidableEq F]
    (hFcard : Fintype.card F = 6)
    (Q : Subgroup (Equiv.Perm F))
    (L : Subgroup Q) [L.Normal] [Nontrivial L]
    (hLcard : Nat.card L ≤ 6) :
    Nat.card Q < 360 := by
  classical
  letI : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [hFcard]
      norm_num)
  have hPermCard :
      Nat.card (Equiv.Perm F) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hFcard]
    norm_num
  have hQdvd :
      Nat.card Q ∣ 720 := by
    simpa only [hPermCard] using
      Subgroup.card_subgroup_dvd_card Q
  by_contra hnot
  have hQlower : 360 ≤ Nat.card Q :=
    le_of_not_gt hnot
  have hQupper : Nat.card Q ≤ 720 :=
    Nat.le_of_dvd (by norm_num) hQdvd
  have hQcases :
      Nat.card Q = 360 ∨ Nat.card Q = 720 := by
    obtain ⟨k, hk⟩ := hQdvd
    have hkbound : k ≤ 2 := by
      have hmul := Nat.mul_le_mul_right k hQlower
      rw [← hk] at hmul
      omega
    interval_cases k <;> omega
  rcases hQcases with hQcard | hQcard
  · have hQindexCard := Q.index_mul_card
    have hQindex : Q.index = 2 := by
      rw [hPermCard, hQcard] at hQindexCard
      omega
    have hAltLe :
        alternatingGroup F ≤ Q :=
      Equiv.Perm.alternatingGroup_le_of_index_le_two
        (by rw [hQindex])
    have hAltCard :
        Nat.card (alternatingGroup F) = 360 := by
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup,
        hFcard]
      norm_num
    have hQeq :
        Q = alternatingGroup F := by
      symm
      apply Subgroup.eq_of_le_of_card_ge hAltLe
      rw [hQcard, hAltCard]
    letI : IsSimpleGroup Q := by
      rw [hQeq]
      exact
        alternatingGroup.isSimpleGroup (by
          rw [Nat.card_eq_fintype_card, hFcard]
          norm_num)
    rcases
        (inferInstance : L.Normal).eq_bot_or_eq_top with
      hLbot | hLtop
    · have hLne : L ≠ ⊥ :=
        L.nontrivial_iff_ne_bot.mp
          (by infer_instance)
      exact hLne hLbot
    · have hLcardQ : Nat.card L = Nat.card Q := by
        rw [hLtop, Subgroup.card_top]
      rw [hQcard] at hLcardQ
      omega
  · have hQeq : Q = ⊤ :=
      Subgroup.eq_top_of_card_eq Q (by
        rw [hQcard, hPermCard])
    have hQsubtypeSurjective :
        Function.Surjective Q.subtype := by
      intro q
      refine ⟨⟨q, ?_⟩, rfl⟩
      rw [hQeq]
      exact Subgroup.mem_top q
    let M : Subgroup (Equiv.Perm F) :=
      L.map Q.subtype
    letI : M.Normal := by
      dsimp only [M]
      exact
        (inferInstance : L.Normal).map
          Q.subtype hQsubtypeSurjective
    let inclusion : L →* Equiv.Perm F :=
      Q.subtype.comp L.subtype
    have hinclusion :
        Function.Injective inclusion := by
      intro a b hab
      exact L.subtype_injective
        (Q.subtype_injective hab)
    have hrangeEq :
        inclusion.range = M := by
      have hLrange :
          L.subtype.range = L := by
        ext q
        simp
      change
        (Q.subtype.comp L.subtype).range =
          L.map Q.subtype
      rw [MonoidHom.range_comp,
        hLrange]
    have hMcard :
        Nat.card M = Nat.card L := by
      have hcardEq :
          Nat.card L =
            Nat.card inclusion.range :=
        Nat.card_congr
          (MonoidHom.ofInjective
            hinclusion).toEquiv
      rw [hrangeEq] at hcardEq
      exact hcardEq.symm
    have hMnontrivial : Nontrivial M :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hMcard]
        exact
          Finite.one_lt_card_iff_nontrivial.mpr
            (by infer_instance : Nontrivial L))
    have hAltLe :
        alternatingGroup F ≤ M :=
      Equiv.Perm.alternatingGroup_le_of_normal
        (by
          rw [Nat.card_eq_fintype_card, hFcard]
          norm_num)
        hMnontrivial
    let altInclusion :
        alternatingGroup F →* M :=
      (alternatingGroup F).subtype.codRestrict
        M (fun q => hAltLe q.prop)
    have hAltInclusionInjective :
        Function.Injective altInclusion := by
      intro a b hab
      apply Subtype.ext
      exact
        congrArg
          (fun q : M =>
            (q : Equiv.Perm F)) hab
    have hdiv :
        Nat.card (alternatingGroup F) ∣
          Nat.card M :=
      Subgroup.card_dvd_of_injective
        altInclusion hAltInclusionInjective
    have hAltCard :
        Nat.card (alternatingGroup F) = 360 := by
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFcard]
      norm_num
    have hAltLeM :
        360 ≤ Nat.card M :=
      Nat.le_of_dvd Nat.card_pos (by
        rwa [hAltCard] at hdiv)
    rw [hMcard] at hAltLeM
    omega

private theorem cycle_factor_action_ne_one_of_centralizing_involution
    {X : Type} [Fintype X] [DecidableEq X]
    (u t : Equiv.Perm X)
    (huOrder : orderOf u = 3)
    (huSupport : u.support.card = 18)
    (htOrder : orderOf t = 2)
    (hcomm : Commute u t)
    (hfix : ∀ x : X, u x = x → t x = x) :
    let uSupport : Equiv.Perm u.support :=
      u.subtypePerm (fun _ => u.apply_mem_support)
    let tSupport : Equiv.Perm u.support :=
      t.subtypePerm
        (fun x =>
          Equiv.Perm.mem_support_iff_of_commute
            hcomm.symm x)
    let tCentral :
        Subgroup.centralizer
          ({uSupport} :
            Set (Equiv.Perm u.support)) :=
      ⟨tSupport, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Equiv.ext
        intro x
        apply Subtype.ext
        exact congrFun
          (congrArg DFunLike.coe hcomm.symm.eq) x.1⟩
    (Equiv.Perm.OnCycleFactors.toPermHom
      uSupport) tCentral ≠ 1 := by
  classical
  dsimp
  have hinvariant :
      ∀ x : X, t x ∈ u.support ↔ x ∈ u.support :=
    fun x =>
      Equiv.Perm.mem_support_iff_of_commute
        hcomm.symm x
  let uSupport : Equiv.Perm u.support :=
    u.subtypePerm (fun _ => u.apply_mem_support)
  let tSupport : Equiv.Perm u.support :=
    t.subtypePerm hinvariant
  have htSquare : t ^ 2 = 1 := by
    rw [← htOrder]
    exact pow_orderOf_eq_one t
  have htSupportSquare : tSupport ^ 2 = 1 := by
    ext x
    change (t ^ 2) x.1 = x.1
    rw [htSquare]
    rfl
  have htSupportNe : tSupport ≠ 1 := by
    intro htOne
    have htFixSupport :
        ∀ x ∈ u.support, t x = x := by
      intro x hx
      have happ :=
        congrFun
          (congrArg DFunLike.coe htOne)
          (⟨x, hx⟩ : u.support)
      exact congrArg Subtype.val happ
    have htOne' : t = 1 := by
      ext x
      by_cases hx : x ∈ u.support
      · exact htFixSupport x hx
      · exact hfix x
          (Equiv.Perm.notMem_support.mp hx)
    rw [htOne', orderOf_one] at htOrder
    norm_num at htOrder
  have htSupportOrder :
      orderOf tSupport = 2 :=
    orderOf_eq_prime htSupportSquare htSupportNe
  have hcommSupport :
      Commute tSupport uSupport := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe hcomm.symm.eq) x.1
  let tCentral :
      Subgroup.centralizer
        ({uSupport} :
          Set (Equiv.Perm u.support)) :=
    ⟨tSupport, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommSupport⟩
  intro hcycleOne
  let χ :
      Subgroup.centralizer
          ({uSupport} :
            Set (Equiv.Perm u.support)) →*
        Equiv.Perm uSupport.cycleFactorsFinset :=
    Equiv.Perm.OnCycleFactors.toPermHom uSupport
  let z : χ.ker :=
    ⟨tCentral, by
      change χ tCentral = 1
      exact hcycleOne⟩
  have hzOrder : orderOf z = 2 := by
    calc
      orderOf z = orderOf tCentral :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf tSupport :=
        (Subgroup.orderOf_coe _).symm
      _ = 2 := htSupportOrder
  have htwoDvd :
      2 ∣ Nat.card χ.ker := by
    rw [← hzOrder, Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order
      (by rw [huOrder]; norm_num)
  have hsum := u.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, huOrder, huSupport] at hsum
  have hmSix : m + 1 = 6 := by omega
  have huCycleType :
      u.cycleType = {3, 3, 3, 3, 3, 3} := by
    rw [hm, huOrder, hmSix]
    norm_num
  have huSupportExtend :
      Equiv.Perm.ofSubtype uSupport = u :=
    Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => u.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have huSupportCycleType :
      uSupport.cycleType = u.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      huSupportExtend]
  have hsupportTypeCard :
      Fintype.card u.support = 18 := by
    rw [Fintype.card_coe, huSupport]
  have hKernelCard :
      Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom
            uSupport).ker = 729 := by
    have hRangeCard :
        Fintype.card
            (Equiv.Perm.OnCycleFactors.kerParam
              uSupport).range = 729 := by
      rw [
        Equiv.Perm.OnCycleFactors.kerParam_range_card,
        hsupportTypeCard, huSupportCycleType,
        huCycleType]
      norm_num
    have hRangeEq :
        Fintype.card
            (Equiv.Perm.OnCycleFactors.kerParam
              uSupport).range =
          Nat.card
            (Equiv.Perm.OnCycleFactors.toPermHom
              uSupport).ker := by
      rw [← Nat.card_eq_fintype_card,
        Equiv.Perm.OnCycleFactors.kerParam_range_eq,
        Subgroup.card_subtype]
    omega
  change
    2 ∣ Nat.card
      (Equiv.Perm.OnCycleFactors.toPermHom
        uSupport).ker at htwoDvd
  rw [hKernelCard] at htwoDvd
  norm_num at htwoDvd

theorem cycle_factor_kernel_card_of_order_three_support_eighteen
    {X : Type} [Fintype X] [DecidableEq X]
    (u : Equiv.Perm X)
    (huOrder : orderOf u = 3)
    (huSupport : u.support.card = 18) :
    let uSupport : Equiv.Perm u.support :=
      u.subtypePerm (fun _ => u.apply_mem_support)
    Nat.card
        (Equiv.Perm.OnCycleFactors.toPermHom
          uSupport).ker = 729 := by
  classical
  dsimp
  let uSupport : Equiv.Perm u.support :=
    u.subtypePerm (fun _ => u.apply_mem_support)
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order
      (by rw [huOrder]; norm_num)
  have hsum := u.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, huOrder, huSupport] at hsum
  have hmSix : m + 1 = 6 := by omega
  have huCycleType :
      u.cycleType = {3, 3, 3, 3, 3, 3} := by
    rw [hm, huOrder, hmSix]
    norm_num
  have huSupportExtend :
      Equiv.Perm.ofSubtype uSupport = u :=
    Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => u.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have huSupportCycleType :
      uSupport.cycleType = u.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      huSupportExtend]
  have hsupportTypeCard :
      Fintype.card u.support = 18 := by
    rw [Fintype.card_coe, huSupport]
  have hRangeCard :
      Fintype.card
          (Equiv.Perm.OnCycleFactors.kerParam
            uSupport).range = 729 := by
    rw [
      Equiv.Perm.OnCycleFactors.kerParam_range_card,
      hsupportTypeCard, huSupportCycleType,
      huCycleType]
    norm_num
  have hRangeEq :
      Fintype.card
          (Equiv.Perm.OnCycleFactors.kerParam
            uSupport).range =
        Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom
            uSupport).ker := by
    rw [← Nat.card_eq_fintype_card,
      Equiv.Perm.OnCycleFactors.kerParam_range_eq,
      Subgroup.card_subtype]
  exact hRangeEq.symm.trans hRangeCard

theorem auxiliary_range_card_lt_three_hundred_sixty_of_small_kernel
    (C F B : Type) [Group C] [Fintype C]
    [Fintype F] [DecidableEq F]
    [Fintype B] [DecidableEq B]
    (hBcard : Fintype.card B = 6)
    (fixedMap : C →* Equiv.Perm F)
    (auxMap : C →* Equiv.Perm B)
    (hKerCard : Nat.card fixedMap.ker ≤ 6)
    (hKerNontrivial :
      ∃ k : fixedMap.ker,
        auxMap k.1 ≠ 1) :
    Nat.card auxMap.range < 360 := by
  classical
  let Q : Subgroup (Equiv.Perm B) :=
    auxMap.range
  let auxRangeMap : C →* Q :=
    auxMap.rangeRestrict
  have hAuxRangeSurjective :
      Function.Surjective auxRangeMap := by
    simpa only [Q, auxRangeMap] using
      MonoidHom.rangeRestrict_surjective auxMap
  let L : Subgroup Q :=
    fixedMap.ker.map auxRangeMap
  letI : L.Normal := by
    dsimp only [L]
    exact
      (inferInstance : fixedMap.ker.Normal).map
        auxRangeMap hAuxRangeSurjective
  obtain ⟨k, hk⟩ := hKerNontrivial
  let kQ : Q :=
    auxRangeMap k.1
  have hkQL : kQ ∈ L := by
    exact ⟨k.1, k.prop, rfl⟩
  let kL : L := ⟨kQ, hkQL⟩
  have hkLne : kL ≠ 1 := by
    intro hkL
    apply hk
    have hval :=
      congrArg
        (fun q : L =>
          ((q : Q) : Equiv.Perm B)) hkL
    exact hval
  letI : Nontrivial L :=
    nontrivial_iff.mpr ⟨kL, 1, hkLne⟩
  let kernelToImage : fixedMap.ker → L :=
    fun z =>
      ⟨auxRangeMap z.1,
        ⟨z.1, z.prop, rfl⟩⟩
  have hKernelToImageSurjective :
      Function.Surjective kernelToImage := by
    intro l
    obtain ⟨c, hcKer, hc⟩ := l.prop
    let z : fixedMap.ker := ⟨c, hcKer⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hc
  have hLcard :
      Nat.card L ≤ Nat.card fixedMap.ker :=
    Nat.card_le_card_of_surjective
      kernelToImage hKernelToImageSurjective
  exact
    card_lt_three_hundred_sixty_of_small_normal
      B hBcard Q L (hLcard.trans hKerCard)

theorem centralizer_cycle_range_small_of_kernel_involution
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hKerCard :
      Nat.card
          (MulAction.toPermHom
            (Subgroup.normalizer (R : Set P))
            (MulAction.fixedPoints R X)).ker = 6)
    (t :
      (MulAction.toPermHom
        (Subgroup.normalizer (R : Set P))
        (MulAction.fixedPoints R X)).ker)
    (hrOrder : orderOf r = 3)
    (hrSupport :
      ((r : P) : Equiv.Perm X).support.card = 18)
    (htOrder : orderOf t = 2)
    (hcentral :
      MulAut.conj
          ((((t :
              (MulAction.toPermHom
                (Subgroup.normalizer (R : Set P))
                (MulAction.fixedPoints R X)).ker) :
              Subgroup.normalizer (R : Set P)) : P))
          (r : P) =
        (r : P)) :
    Nat.card
        (FiveTransitive.NormalizerGoursat.centralizerCycleMap
          X P R r).range < 360 := by
  classical
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let κ : N →* MulAut R :=
    R.normalizerMonoidHom
  let C : Subgroup N := κ.ker
  let ρC : C →* Equiv.Perm F :=
    ρ.comp C.subtype
  let g : Equiv.Perm X := (r : P)
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  let cycleMap :
      C →* Equiv.Perm gSupport.cycleFactorsFinset :=
    FiveTransitive.NormalizerGoursat.centralizerCycleMap
      X P R r
  let tN : N := t
  let tP : P := tN
  let tPerm : Equiv.Perm X := tP
  have hrPOrder : orderOf (r : P) = 3 := by
    calc
      orderOf (r : P) = orderOf r :=
        Subgroup.orderOf_coe _
      _ = 3 := hrOrder
  have hgOrder : orderOf g = 3 := by
    calc
      orderOf g = orderOf (r : P) :=
        Subgroup.orderOf_coe _
      _ = 3 := hrPOrder
  have htPermOrder : orderOf tPerm = 2 := by
    calc
      orderOf tPerm = orderOf tP :=
        Subgroup.orderOf_coe _
      _ = orderOf tN :=
        Subgroup.orderOf_coe _
      _ = orderOf t :=
        Subgroup.orderOf_coe _
      _ = 2 := htOrder
  have hcommP :
      Commute (r : P) tP := by
    have hcentral' :
        tP * (r : P) * tP⁻¹ = (r : P) := by
      exact hcentral
    exact
      (mul_inv_eq_iff_eq_mul.mp hcentral').symm
  have hcommPerm : Commute g tPerm :=
    congrArg Subtype.val hcommP
  have htCentralR :
      tP ∈ Subgroup.centralizer (R : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hRgenerated] at ha
    obtain ⟨z, hz⟩ :=
      Subgroup.mem_zpowers_iff.mp ha
    rw [← hz]
    exact (hcommP.zpow_left z).eq
  have htC : tN ∈ C := by
    change tN ∈ κ.ker
    rw [R.normalizerMonoidHom_ker]
    exact htCentralR
  let tC : C := ⟨tN, htC⟩
  have htρC : ρC tC = 1 := by
    exact t.prop
  let k : ρC.ker := ⟨tC, htρC⟩
  let fixedKernelToOriginal :
      ρC.ker → ρ.ker :=
    fun z =>
      ⟨z.1.1, z.prop⟩
  have hfixedKernelToOriginalInjective :
      Function.Injective fixedKernelToOriginal := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact
      congrArg
        (fun z : ρ.ker => (z : N)) hab
  have hρCkerCard :
      Nat.card ρC.ker ≤ 6 := by
    calc
      Nat.card ρC.ker ≤ Nat.card ρ.ker :=
        Nat.card_le_card_of_injective
          fixedKernelToOriginal
          hfixedKernelToOriginalInjective
      _ = 6 := by
        simpa only [F, N, ρ] using hKerCard
  have htFix :
      ∀ x : X, g x = x → tPerm x = x := by
    intro x hgx
    have hxF : x ∈ F := by
      rw [MulAction.mem_fixedPoints]
      intro a
      have haZ :
          (a : P) ∈
            Subgroup.zpowers (r : P) := by
        rw [← hRgenerated]
        exact a.prop
      obtain ⟨z, hz⟩ :=
        Subgroup.mem_zpowers_iff.mp haZ
      have hz' := congrArg Subtype.val hz
      rw [Subgroup.coe_zpow] at hz'
      change ((a : P) : Equiv.Perm X) x = x
      rw [← hz']
      exact
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
          hgx z
    have htKer : ρ tN = 1 := t.prop
    have happ :=
      congrFun
        (congrArg DFunLike.coe htKer)
        (⟨x, hxF⟩ : F)
    exact congrArg Subtype.val happ
  have hcycleK :
      cycleMap k.1 ≠ 1 := by
    have hne :=
      cycle_factor_action_ne_one_of_centralizing_involution
        g tPerm hgOrder (by
          simpa only [g] using hrSupport)
          htPermOrder hcommPerm htFix
    change
      (FiveTransitive.NormalizerGoursat.centralizerCycleMap
        X P R r) tC ≠ 1
    intro hcycleOne
    apply hne
    rw [← hcycleOne]
    apply congrArg
      (Equiv.Perm.OnCycleFactors.toPermHom gSupport)
    apply Subtype.ext
    rfl
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order
      (by rw [hgOrder]; norm_num)
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder,
    show g.support.card = 18 by
      simpa only [g] using hrSupport] at hsum
  have hmSix : m + 1 = 6 := by omega
  have hgCycleType :
      g.cycleType = {3, 3, 3, 3, 3, 3} := by
    rw [hm, hgOrder, hmSix]
    norm_num
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g :=
    Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hcycleFactorsCard :
      Fintype.card gSupport.cycleFactorsFinset = 6 := by
    rw [Fintype.card_coe]
    have hcard :=
      congrArg Multiset.card
        (Equiv.Perm.cycleType_def gSupport)
    rw [hgSupportCycleType, hgCycleType] at hcard
    norm_num at hcard ⊢
    exact hcard.symm
  exact
    auxiliary_range_card_lt_three_hundred_sixty_of_small_kernel
      C F gSupport.cycleFactorsFinset
        hcycleFactorsCard ρC cycleMap hρCkerCard
        ⟨k, hcycleK⟩

end FiveTransitive.Degree24

end CFSG
