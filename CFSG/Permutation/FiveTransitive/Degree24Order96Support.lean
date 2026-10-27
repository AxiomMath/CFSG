module

public import CFSG.Permutation.FiveTransitive.Degree24Order96CycleTransfer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

private theorem support_card_of_commuting_involution_order_three
    {X : Type} [Fintype X] [DecidableEq X]
    (g q : Equiv.Perm X)
    (hgOrder : orderOf g = 3)
    (hqOrder : orderOf q = 2)
    (hcomm : Commute q g) :
    let qC :
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
      ⟨q,
        Subgroup.mem_centralizer_singleton_iff.mpr
          hcomm⟩
    let τ :=
      Equiv.Perm.OnCycleFactors.toPermHom g qC
    let u : Equiv.Perm (Function.fixedPoints g) :=
      q.subtypePerm
        (fun _ =>
          Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
            qC.prop)
    q.support.card =
      u.support.card + 3 * τ.support.card := by
  classical
  dsimp
  let qC :
      Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)) :=
    ⟨q,
      Subgroup.mem_centralizer_singleton_iff.mpr
        hcomm⟩
  let τ :=
    Equiv.Perm.OnCycleFactors.toPermHom g qC
  let u : Equiv.Perm (Function.fixedPoints g) :=
    q.subtypePerm
      (fun _ =>
        Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
          qC.prop)
  let fixedMoved : Finset X :=
    u.support.map
      (Function.Embedding.subtype
        (fun x : X => x ∈ Function.fixedPoints g))
  let cycleMoved : Finset X :=
    τ.support.biUnion (fun c => c.1.support)
  have hcycleCard
      (c : g.cycleFactorsFinset) :
      c.1.support.card = 3 := by
    have hmem :
        c.1.support.card ∈ g.cycleType := by
      rw [Equiv.Perm.cycleType_def]
      exact
        Multiset.mem_map.mpr
          ⟨c.1, c.2, rfl⟩
    have horderDvd :
        c.1.support.card ∣ 3 := by
      rw [← hgOrder]
      exact Equiv.Perm.dvd_of_mem_cycleType hmem
    have htwo :
        2 ≤ c.1.support.card :=
      Equiv.Perm.two_le_of_mem_cycleType hmem
    rcases (Nat.dvd_prime (by norm_num)).mp horderDvd with
      hone | hthree
    · rw [hone] at htwo
      norm_num at htwo
    · exact hthree
  have hsupport :
      q.support = fixedMoved ∪ cycleMoved := by
    ext x
    by_cases hxg : x ∈ g.support
    · have hc :
          g.cycleOf x ∈ g.cycleFactorsFinset :=
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
          hxg
      let c : g.cycleFactorsFinset :=
        ⟨g.cycleOf x, hc⟩
      have hxc : x ∈ c.1.support := by
        rw [Equiv.Perm.mem_support_cycleOf_iff]
        exact
          ⟨Equiv.Perm.SameCycle.refl g x, hxg⟩
      have hcycleIff :
          x ∈ cycleMoved ↔ x ∈ q.support := by
        constructor
        · intro hxCycle
          rw [Finset.mem_biUnion] at hxCycle
          obtain ⟨d, hdMoved, hxd⟩ := hxCycle
          by_contra hxq
          have hqx : q x = x :=
            Equiv.Perm.notMem_support.mp hxq
          have hqInvx : q⁻¹ x = x := by
            change q.symm x = x
            calc
              q.symm x = q.symm (q x) :=
                congrArg q.symm hqx.symm
              _ = x := q.symm_apply_apply x
          have hxConj :
              x ∈
                (q * d.1 * q⁻¹).support := by
            rw [Equiv.Perm.mem_support]
            change q (d.1 (q⁻¹ x)) ≠ x
            rw [hqInvx]
            intro heq
            apply Equiv.Perm.mem_support.mp hxd
            apply q.injective
            exact heq.trans hqx.symm
          have hxImage :
              x ∈ (τ d).1.support := by
            simpa only [τ, qC,
              Equiv.Perm.OnCycleFactors.coe_toPermHom]
              using hxConj
          have himage :
              (τ d).1 = g.cycleOf x :=
            Equiv.Perm.cycle_is_cycleOf
              hxImage (τ d).2
          have hd :
              d.1 = g.cycleOf x :=
            Equiv.Perm.cycle_is_cycleOf hxd d.2
          have hτd : τ d = d := by
            apply Subtype.ext
            exact himage.trans hd.symm
          exact Equiv.Perm.mem_support.mp hdMoved hτd
        · intro hxq
          rw [Finset.mem_biUnion]
          refine ⟨c, ?_, hxc⟩
          rw [Equiv.Perm.mem_support]
          intro hτc
          have hconj :
              q * c.1 * q⁻¹ = c.1 := by
            have hval := congrArg Subtype.val hτc
            simpa only [τ, qC,
              Equiv.Perm.OnCycleFactors.coe_toPermHom]
              using hval
          have hqc : Commute q c.1 :=
            mul_inv_eq_iff_eq_mul.mp hconj
          have hcOrder : orderOf c.1 = 3 := by
            rw [(Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.orderOf,
              hcycleCard c]
          have hcoprime :
              Nat.Coprime (orderOf q) (orderOf c.1) := by
            rw [hqOrder, hcOrder]
            norm_num
          have hdisjoint :=
            PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
              (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
              hqc hcoprime
          have hxCompl := hdisjoint hxq
          rw [Finset.mem_compl] at hxCompl
          exact hxCompl hxc
      have hxNotFixed : x ∉ fixedMoved := by
        intro hxFixed
        rw [Finset.mem_map] at hxFixed
        obtain ⟨y, hy, hyx⟩ := hxFixed
        have hyFixed :
            g y.1 = y.1 :=
          Function.mem_fixedPoints_iff.mp y.2
        have hyVal : y.1 = x := hyx
        rw [hyVal] at hyFixed
        exact Equiv.Perm.mem_support.mp hxg hyFixed
      simp only [Finset.mem_union, hxNotFixed, false_or,
        hcycleIff]
    · have hxFixed :
          x ∈ Function.fixedPoints g := by
        rw [Function.mem_fixedPoints_iff]
        exact Equiv.Perm.notMem_support.mp hxg
      have hfixedIff :
          x ∈ fixedMoved ↔ x ∈ q.support := by
        constructor
        · intro hxMoved
          rw [Finset.mem_map] at hxMoved
          obtain ⟨y, hy, hyx⟩ := hxMoved
          rw [Equiv.Perm.mem_support] at hy ⊢
          intro hqx
          apply hy
          apply Subtype.ext
          change q y.1 = y.1
          change y.1 = x at hyx
          rw [hyx, hqx]
        · intro hxq
          rw [Finset.mem_map]
          let y : Function.fixedPoints g :=
            ⟨x, hxFixed⟩
          refine ⟨y, ?_, rfl⟩
          rw [Equiv.Perm.mem_support]
          intro hy
          exact Equiv.Perm.mem_support.mp hxq
            (congrArg Subtype.val hy)
      have hxNotCycle : x ∉ cycleMoved := by
        intro hxCycle
        rw [Finset.mem_biUnion] at hxCycle
        obtain ⟨c, _, hxc⟩ := hxCycle
        exact hxg
          (Equiv.Perm.mem_cycleFactorsFinset_support_le
            c.2 hxc)
      simp only [Finset.mem_union, hfixedIff,
        hxNotCycle, or_false]
  have hdisjoint :
      Disjoint fixedMoved cycleMoved := by
    rw [Finset.disjoint_left]
    intro x hxFixed hxCycle
    rw [Finset.mem_map] at hxFixed
    obtain ⟨y, _, hyx⟩ := hxFixed
    rw [Finset.mem_biUnion] at hxCycle
    obtain ⟨c, _, hxc⟩ := hxCycle
    have hxg :=
      Equiv.Perm.mem_cycleFactorsFinset_support_le
        c.2 hxc
    have hyFixed :
        g y.1 = y.1 :=
      Function.mem_fixedPoints_iff.mp y.2
    have hyVal : y.1 = x := hyx
    rw [hyVal] at hyFixed
    exact Equiv.Perm.mem_support.mp hxg hyFixed
  have hfixedCard :
      fixedMoved.card = u.support.card := by
    simp only [fixedMoved, Finset.card_map]
  have hcycleMovedCard :
      cycleMoved.card = 3 * τ.support.card := by
    change
      (τ.support.biUnion
        (fun c => c.1.support)).card =
          3 * τ.support.card
    rw [Finset.card_biUnion]
    · simp_rw [hcycleCard]
      simp [Nat.mul_comm]
    · intro a _ b _ hab
      exact
        Equiv.Perm.Disjoint.disjoint_support
          (g.cycleFactorsFinset_pairwise_disjoint
            a.2 b.2 (Subtype.coe_ne_coe.mpr hab))
  rw [hsupport, Finset.card_union_of_disjoint hdisjoint,
    hfixedCard, hcycleMovedCard]

private theorem card_support_permCongr
    {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (e : A ≃ B) (p : Equiv.Perm A) :
    (e.permCongr p).support.card =
      p.support.card := by
  have hsupport :
      (e.permCongr p).support =
        p.support.map e.toEmbedding := by
    ext y
    simp only [Equiv.Perm.mem_support,
      Equiv.permCongr_apply, Finset.mem_map]
    constructor
    · intro hy
      refine
        ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      intro hfix
      exact hy
        ((congrArg e hfix).trans
          (e.apply_symm_apply y))
    · rintro ⟨x, hx, hxy⟩
      intro hfix
      apply hx
      apply e.injective
      calc
        e (p x) = e.permCongr p (e x) := by
          simp only [Equiv.permCongr_apply,
            e.symm_apply_apply]
        _ = e.permCongr p y :=
          congrArg (e.permCongr p) hxy
        _ = y := hfix
        _ = e x := hxy.symm
  rw [hsupport, Finset.card_map]

theorem normalizer_support_card_of_commuting_involution
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    [Fintype (MulAction.fixedPoints R X)]
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3)
    (q : Subgroup.normalizer (R : Set P))
    (hqOrder :
      orderOf
        ((((q :
          Subgroup.normalizer (R : Set P)) : P) :
            Equiv.Perm X)) = 2)
    (hcomm :
      Commute
        ((((q :
          Subgroup.normalizer (R : Set P)) : P) :
            Equiv.Perm X))
        ((r : P) : Equiv.Perm X)) :
    let F : Set X := MulAction.fixedPoints R X
    let ρ :
        Subgroup.normalizer (R : Set P) →*
          Equiv.Perm F :=
      MulAction.toPermHom
        (Subgroup.normalizer (R : Set P)) F
    let B :=
      cycleSupportFinset
        ((r : P) : Equiv.Perm X)
    let ψ :
        Subgroup.normalizer (R : Set P) →*
          Equiv.Perm B :=
      normalizerCycleSupportMap
        X P R r hRgenerated hrOrder
    ((((q :
      Subgroup.normalizer (R : Set P)) : P) :
        Equiv.Perm X)).support.card =
      (ρ q).support.card +
        3 * (ψ q).support.card := by
  classical
  dsimp
  let g : Equiv.Perm X := (r : P)
  let qPerm : Equiv.Perm X :=
    ((q :
      Subgroup.normalizer (R : Set P)) : P)
  let F : Set X := MulAction.fixedPoints R X
  let ρ :
      Subgroup.normalizer (R : Set P) →*
        Equiv.Perm F :=
    MulAction.toPermHom
      (Subgroup.normalizer (R : Set P)) F
  let B := cycleSupportFinset g
  let ψ :
      Subgroup.normalizer (R : Set P) →*
        Equiv.Perm B :=
    normalizerCycleSupportMap
      X P R r hRgenerated hrOrder
  let qC :
      Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)) :=
    ⟨qPerm,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (by
          simpa only [g, qPerm] using hcomm.eq)⟩
  let τ :=
    Equiv.Perm.OnCycleFactors.toPermHom g qC
  let u : Equiv.Perm (Function.fixedPoints g) :=
    qPerm.subtypePerm
      (fun _ =>
        Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
          qC.prop)
  have hgOrder : orderOf g = 3 := by
    calc
      orderOf g = orderOf (r : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf r :=
        Subgroup.orderOf_coe _
      _ = 3 := hrOrder
  have hgeneric :
      qPerm.support.card =
        u.support.card + 3 * τ.support.card := by
    simpa only [qC, τ, u] using
      support_card_of_commuting_involution_order_three
        g qPerm hgOrder
          (by simpa only [qPerm] using hqOrder)
          (by simpa only [g, qPerm] using hcomm)
  have hfixedSet :
      F = Function.fixedPoints g := by
    ext x
    constructor
    · intro hx
      rw [Function.mem_fixedPoints_iff]
      exact
        MulAction.mem_fixedPoints.mp hx r
    · intro hx
      rw [Function.mem_fixedPoints_iff] at hx
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
          hx z
  let eF : F ≃ Function.fixedPoints g :=
    Set.equivOfEq hfixedSet
  have hfixedConj :
      eF.permCongr (ρ q) = u := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  have hfixedCard :
      (ρ q).support.card = u.support.card := by
    have hcard := card_support_permCongr eF (ρ q)
    rw [hfixedConj] at hcard
    exact hcard.symm
  let factorSupport :
      g.cycleFactorsFinset → B :=
    fun c =>
      ⟨c.1.support,
        Finset.mem_image.mpr
          ⟨c.1, c.2, rfl⟩⟩
  have hfactorSupportInjective :
      Function.Injective factorSupport := by
    intro a b hab
    apply cycleFactor_support_injective g
    exact congrArg Subtype.val hab
  have hfactorSupportSurjective :
      Function.Surjective factorSupport := by
    intro b
    obtain ⟨c, hc, hcb⟩ :=
      Finset.mem_image.mp b.2
    let c' : g.cycleFactorsFinset := ⟨c, hc⟩
    refine ⟨c', ?_⟩
    apply Subtype.ext
    exact hcb
  let eB : g.cycleFactorsFinset ≃ B :=
    Equiv.ofBijective factorSupport
      ⟨hfactorSupportInjective,
        hfactorSupportSurjective⟩
  have hcycleConj :
      eB.permCongr τ = ψ q := by
    apply Equiv.ext
    intro b
    let c : g.cycleFactorsFinset := eB.symm b
    have hcb :
        c.1.support = b.1 := by
      have happly := eB.apply_symm_apply b
      exact congrArg Subtype.val happly
    apply Subtype.ext
    change
      (qPerm * c.1 * qPerm⁻¹).support =
        ((q :
          Subgroup.normalizer (R : Set P)) : P) • b.1
    rw [Equiv.Perm.support_conj, hcb]
    ext x
    simp only [Finset.mem_map,
      Finset.mem_smul_finset, qPerm]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, hyx⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, hyx⟩
  have hcycleCard :
      τ.support.card = (ψ q).support.card := by
    have hcard := card_support_permCongr eB τ
    rw [hcycleConj] at hcard
    exact hcard.symm
  change
    qPerm.support.card =
      (ρ q).support.card +
        3 * (ψ q).support.card
  calc
    qPerm.support.card =
        u.support.card + 3 * τ.support.card :=
      hgeneric
    _ = u.support.card + 3 * (ψ q).support.card := by
      rw [hcycleCard]
    _ = (ρ q).support.card +
        3 * (ψ q).support.card := by
      rw [hfixedCard]

end FiveTransitive.Degree24

end CFSG
