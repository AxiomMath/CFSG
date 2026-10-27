module

public import CFSG.Permutation.FiveTransitive.Degree24Order96Goursat
public import CFSG.Permutation.FiveTransitive.Degree24Order96Kernel

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

@[expose] noncomputable def cycleSupportFinset
    {X : Type} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) : Finset (Finset X) :=
  g.cycleFactorsFinset.image Equiv.Perm.support

private theorem inv_mem_cycleFactorsFinset
    {X : Type} [Fintype X] [DecidableEq X]
    {g c : Equiv.Perm X}
    (h : c ∈ g.cycleFactorsFinset) :
    c⁻¹ ∈ g⁻¹.cycleFactorsFinset := by
  classical
  rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at h ⊢
  refine ⟨h.1.inv, ?_⟩
  intro x hx
  have hxc : x ∈ c.support := by
    simpa only [Equiv.Perm.support_inv] using hx
  have hpre : c⁻¹ x ∈ c.support := by
    change c.symm x ∈ c.support
    rw [← Equiv.Perm.apply_mem_support]
    simpa only [Equiv.apply_symm_apply] using hxc
  have hagree := h.2 (c⁻¹ x) hpre
  have hcInv : c (c⁻¹ x) = x := by
    change c (c.symm x) = x
    exact c.apply_symm_apply x
  rw [hcInv] at hagree
  apply g.injective
  have hgInv : g (g⁻¹ x) = x := by
    change g (g.symm x) = x
    exact g.apply_symm_apply x
  rw [hgInv]
  exact hagree.symm

theorem normalizer_smul_mem_cycleSupportFinset
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3)
    (q : Subgroup.normalizer (R : Set P))
    (b : Finset X)
    (hb :
      b ∈ cycleSupportFinset
        ((r : P) : Equiv.Perm X)) :
    ((q :
      Subgroup.normalizer (R : Set P)) : P) • b ∈
      cycleSupportFinset
        ((r : P) : Equiv.Perm X) := by
  classical
  let g : Equiv.Perm X := (r : P)
  let qP : P := q
  let qPerm : Equiv.Perm X := qP
  have hqNormalizer :
      qP ∈ Subgroup.normalizer
        (Subgroup.zpowers (r : P) : Set P) := by
    rw [← hRgenerated]
    exact q.prop
  have hdichotomy :=
    conj_eq_or_eq_inv_of_mem_normalizer_zpowers_order_three
      (r : P) qP
        ((Subgroup.orderOf_coe r).trans hrOrder)
        hqNormalizer
  obtain ⟨c, hc, hcb⟩ :=
    Finset.mem_image.mp hb
  let d : Equiv.Perm X :=
    qPerm * c * qPerm⁻¹
  have hdSupport :
      d.support = qP • c.support := by
    dsimp only [d]
    rw [Equiv.Perm.support_conj]
    ext x
    simp only [Finset.mem_map, Finset.mem_smul_finset,
      qPerm, qP]
    constructor
    · rintro ⟨a, ha, hax⟩
      refine ⟨a, ha, ?_⟩
      exact hax
    · rintro ⟨a, ha, hax⟩
      refine ⟨a, ha, ?_⟩
      exact hax
  rcases hdichotomy with hcentral | hinverts
  · have hcentralPerm :
        qPerm * g * qPerm⁻¹ = g :=
      congrArg Subtype.val hcentral
    have hd :
        d ∈ g.cycleFactorsFinset := by
      have hd' :=
        Equiv.Perm.mem_cycleFactorsFinset_conj
          g qPerm c
      apply hd'.2 at hc
      simpa only [d, hcentralPerm] using hc
    rw [← hcb]
    exact
      Finset.mem_image.mpr
        ⟨d, hd, hdSupport⟩
  · have hinvertsPerm :
        qPerm * g * qPerm⁻¹ = g⁻¹ :=
      congrArg Subtype.val hinverts
    have hdInv :
        d ∈ g⁻¹.cycleFactorsFinset := by
      have hd' :=
        Equiv.Perm.mem_cycleFactorsFinset_conj
          g qPerm c
      apply hd'.2 at hc
      simpa only [d, hinvertsPerm] using hc
    have hd :
        d⁻¹ ∈ g.cycleFactorsFinset :=
      by
        simpa only [inv_inv] using
          inv_mem_cycleFactorsFinset hdInv
    rw [← hcb]
    exact
      Finset.mem_image.mpr
        ⟨d⁻¹, hd, by
          rw [Equiv.Perm.support_inv, hdSupport]⟩

@[expose, implicit_reducible]
noncomputable def normalizerCycleSupportMulAction
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3) :
    MulAction
      (Subgroup.normalizer (R : Set P))
      (cycleSupportFinset
        ((r : P) : Equiv.Perm X)) where
  smul q b :=
    ⟨((q :
        Subgroup.normalizer (R : Set P)) : P) • b.1,
      normalizer_smul_mem_cycleSupportFinset
        X P R r hRgenerated hrOrder q b.1 b.2⟩
  one_smul b := by
    apply Subtype.ext
    exact one_smul P b.1
  mul_smul a b c := by
    apply Subtype.ext
    exact mul_smul
      ((a :
        Subgroup.normalizer (R : Set P)) : P)
      ((b :
        Subgroup.normalizer (R : Set P)) : P)
      c.1

@[expose] noncomputable def normalizerCycleSupportMap
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3) :
    Subgroup.normalizer (R : Set P) →*
      Equiv.Perm
        (cycleSupportFinset
          ((r : P) : Equiv.Perm X)) := by
  letI :
      MulAction
        (Subgroup.normalizer (R : Set P))
        (cycleSupportFinset
          ((r : P) : Equiv.Perm X)) :=
    normalizerCycleSupportMulAction
      X P R r hRgenerated hrOrder
  exact
    MulAction.toPermHom
      (Subgroup.normalizer (R : Set P))
      (cycleSupportFinset
        ((r : P) : Equiv.Perm X))

theorem normalizerCycleSupportMap_apply_val
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3)
    (q : Subgroup.normalizer (R : Set P))
    (b :
      cycleSupportFinset
        ((r : P) : Equiv.Perm X)) :
    ((normalizerCycleSupportMap
        X P R r hRgenerated hrOrder q) b).1 =
      ((q :
        Subgroup.normalizer (R : Set P)) : P) • b.1 := by
  rfl

theorem mem_cycleSupportFinset_card_three
    {X : Type} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X)
    (hgOrder : orderOf g = 3)
    (hgSupport : g.support.card = 18)
    (b : Finset X)
    (hb : b ∈ cycleSupportFinset g) :
    b.card = 3 := by
  classical
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order
      (by rw [hgOrder]; norm_num)
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder, hgSupport] at hsum
  have hmSix : m + 1 = 6 := by omega
  have hgCycleType :
      g.cycleType = {3, 3, 3, 3, 3, 3} := by
    rw [hm, hgOrder, hmSix]
    norm_num
  obtain ⟨c, hc, hcb⟩ :=
    Finset.mem_image.mp hb
  have hmem :
      c.support.card ∈ g.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact
      Multiset.mem_map.mpr
        ⟨c, by simpa using hc, rfl⟩
  rw [hgCycleType] at hmem
  norm_num at hmem
  rw [← hcb]
  exact hmem

theorem cycleSupportFinset_card_of_order_three_support_eighteen
    {X : Type} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X)
    (hgOrder : orderOf g = 3)
    (hgSupport : g.support.card = 18) :
    Fintype.card (cycleSupportFinset g) = 6 := by
  classical
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order
      (by rw [hgOrder]; norm_num)
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder, hgSupport] at hsum
  have hmSix : m + 1 = 6 := by omega
  have hfactorCard :
      g.cycleFactorsFinset.card = 6 := by
    have hcard :=
      congrArg Multiset.card
        (Equiv.Perm.cycleType_def g)
    rw [hm, Multiset.card_replicate, hmSix] at hcard
    simpa using hcard.symm
  have hinjective :
      Set.InjOn
        Equiv.Perm.support
        (g.cycleFactorsFinset : Set (Equiv.Perm X)) := by
    intro c hc d hd hsupport
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ c.support
    · have hxd : x ∈ d.support := by
        rwa [← hsupport]
      exact
        ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
          x hx).trans
          ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hd).2
            x hxd).symm
    · have hxd : x ∉ d.support := by
        rwa [← hsupport]
      rw [Equiv.Perm.notMem_support.mp hx,
        Equiv.Perm.notMem_support.mp hxd]
  rw [Fintype.card_coe, cycleSupportFinset,
    Finset.card_image_of_injOn hinjective,
    hfactorCard]

private theorem support_eq_twelve_of_inverting_cycleSupport_action_eq_one
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (t : Subgroup.normalizer (R : Set P))
    (hrOrder : orderOf r = 3)
    (hrSupport :
      ((r : P) : Equiv.Perm X).support.card = 18)
    (htOrder : orderOf t = 2)
    (hinverts :
      MulAut.conj
          ((t :
            Subgroup.normalizer (R : Set P)) : P)
          (r : P) =
        (r : P)⁻¹)
    (hfix :
      ∀ x : X,
        ((r : P) : Equiv.Perm X) x = x →
          (((t :
            Subgroup.normalizer (R : Set P)) : P) :
              Equiv.Perm X) x = x)
    (hcycle :
      normalizerCycleSupportMap
          X P R r hRgenerated hrOrder t = 1) :
    ((((t :
      Subgroup.normalizer (R : Set P)) : P) :
        Equiv.Perm X).support.card = 12) := by
  classical
  let g : Equiv.Perm X := (r : P)
  let tP : P := t
  let tPerm : Equiv.Perm X := tP
  let B := cycleSupportFinset g
  have hgOrder : orderOf g = 3 := by
    calc
      orderOf g = orderOf (r : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf r :=
        Subgroup.orderOf_coe _
      _ = 3 := hrOrder
  have hgSupport : g.support.card = 18 := by
    simpa only [g] using hrSupport
  have htPermOrder : orderOf tPerm = 2 := by
    calc
      orderOf tPerm = orderOf tP :=
        Subgroup.orderOf_coe _
      _ = orderOf t :=
        Subgroup.orderOf_coe _
      _ = 2 := htOrder
  have hinvertsPerm :
      MulAut.conj tPerm g = g⁻¹ := by
    exact congrArg Subtype.val hinverts
  have htSupportSubset :
      tPerm.support ⊆ g.support := by
    intro x hxt
    by_contra hxg
    exact Equiv.Perm.mem_support.mp hxt
      (hfix x
        (Equiv.Perm.notMem_support.mp hxg))
  have hsupportLower :
      12 ≤ tPerm.support.card :=
    twelve_le_support_of_inverts_order_three_of_fixed
      g tPerm hgOrder hgSupport
        hinvertsPerm hfix
  have hBcard : Fintype.card B = 6 := by
    simpa only [B] using
      cycleSupportFinset_card_of_order_three_support_eighteen
        g hgOrder hgSupport
  have hcycleInvariant
      (b : B) :
      tP • b.1 = b.1 := by
    have happ :=
      congrFun
        (congrArg DFunLike.coe hcycle) b
    have hval := congrArg Subtype.val happ
    calc
      tP • b.1 =
          ((normalizerCycleSupportMap
            X P R r hRgenerated hrOrder t) b).1 :=
        (normalizerCycleSupportMap_apply_val
          X P R r hRgenerated hrOrder t b).symm
      _ = b.1 := by
        simpa only [Equiv.Perm.one_apply] using hval
  have hfixedInCycle
      (b : B) :
      ∃ x : X,
        x ∈ b.1 ∧
          x ∈ g.support ∧
          tPerm x = x := by
    have hbCard : b.1.card = 3 :=
      mem_cycleSupportFinset_card_three
        g hgOrder hgSupport b.1 b.2
    have hbSubset : b.1 ⊆ g.support := by
      obtain ⟨c, hc, hcb⟩ :=
        Finset.mem_image.mp b.2
      rw [← hcb]
      exact
        Equiv.Perm.mem_cycleFactorsFinset_support_le hc
    have htInvariant :
        ∀ x : X, tPerm x ∈ b.1 ↔ x ∈ b.1 := by
      intro x
      constructor
      · intro htx
        have htxP : tP • x ∈ b.1 := by
          change tPerm x ∈ b.1
          exact htx
        have hmem :
            tP • x ∈ tP • b.1 := by
          rw [hcycleInvariant b]
          exact htxP
        exact
          (Finset.smul_mem_smul_finset_iff tP).mp hmem
      · intro hx
        have hmem : tP • x ∈ tP • b.1 :=
          Finset.smul_mem_smul_finset hx
        have hmem' : tP • x ∈ b.1 := by
          rwa [hcycleInvariant b] at hmem
        change tPerm x ∈ b.1
        exact hmem'
    let tB : Equiv.Perm b.1 :=
      tPerm.subtypePerm htInvariant
    have htSquare : tPerm ^ 2 = 1 := by
      rw [← htPermOrder]
      exact pow_orderOf_eq_one tPerm
    have htBSquare : tB ^ 2 = 1 := by
      ext x
      change (tPerm ^ 2) x.1 = x.1
      rw [htSquare]
      rfl
    have hexists : ∃ x : b.1, tB x = x := by
      by_contra hnone
      push Not at hnone
      have hsupportFull :
          tB.support = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true,
          Equiv.Perm.mem_support]
        exact hnone x
      have htwoDvd :=
        Equiv.Perm.two_dvd_card_support htBSquare
      rw [hsupportFull, Finset.card_univ,
        Fintype.card_coe, hbCard] at htwoDvd
      norm_num at htwoDvd
    obtain ⟨x, hx⟩ := hexists
    refine ⟨x.1, x.2, hbSubset x.2, ?_⟩
    exact congrArg Subtype.val hx
  choose x hxB hxSupport hxFix using hfixedInCycle
  let D : Type := ↥(g.support \ tPerm.support)
  let f : B → D :=
    fun b =>
      ⟨x b, Finset.mem_sdiff.mpr
        ⟨hxSupport b,
          Equiv.Perm.notMem_support.mpr (hxFix b)⟩⟩
  have hsupport_eq_cycleOf
      (b : B) (y : X) (hy : y ∈ b.1) :
      b.1 = (g.cycleOf y).support := by
    obtain ⟨c, hc, hcb⟩ :=
      Finset.mem_image.mp b.2
    have hyc : y ∈ c.support := by
      rwa [hcb]
    have hcycleOf :
        c = g.cycleOf y :=
      Equiv.Perm.cycle_is_cycleOf hyc hc
    calc
      b.1 = c.support := hcb.symm
      _ = (g.cycleOf y).support :=
        congrArg Equiv.Perm.support hcycleOf
  have hfInjective : Function.Injective f := by
    intro b d hbd
    have hxd : x b = x d :=
      congrArg Subtype.val hbd
    apply Subtype.ext
    calc
      b.1 = (g.cycleOf (x b)).support :=
        hsupport_eq_cycleOf b (x b) (hxB b)
      _ = (g.cycleOf (x d)).support := by rw [hxd]
      _ = d.1 :=
        (hsupport_eq_cycleOf d (x d) (hxB d)).symm
  have hdiffLower :
      6 ≤ (g.support \ tPerm.support).card := by
    calc
      6 = Fintype.card B := hBcard.symm
      _ ≤ Fintype.card D :=
        Fintype.card_le_of_injective f hfInjective
      _ = (g.support \ tPerm.support).card :=
        Fintype.card_coe _
  have hpartition :=
    Finset.card_sdiff_add_card_eq_card htSupportSubset
  rw [hgSupport] at hpartition
  simpa only [tPerm, tP] using
    (show tPerm.support.card = 12 by omega)

theorem normalizer_cycleSupport_range_small_of_inverting_kernel
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
    (hinverts :
      MulAut.conj
          ((((t :
            (MulAction.toPermHom
              (Subgroup.normalizer (R : Set P))
              (MulAction.fixedPoints R X)).ker) :
                Subgroup.normalizer (R : Set P)) : P))
          (r : P) =
        (r : P)⁻¹)
    (hSupportNe :
      ((((t :
          Subgroup.normalizer (R : Set P)) : P) :
            Equiv.Perm X).support.card ≠ 12)) :
    Nat.card
        (normalizerCycleSupportMap
          X P R r hRgenerated hrOrder).range < 360 := by
  classical
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let ψ :
      N →*
        Equiv.Perm
          (cycleSupportFinset
            ((r : P) : Equiv.Perm X)) :=
    normalizerCycleSupportMap
      X P R r hRgenerated hrOrder
  let t₀ : ρ.ker := t
  let tN : N := t₀
  let tP : P := tN
  let tPerm : Equiv.Perm X := tP
  let g : Equiv.Perm X := (r : P)
  have hrPOrder : orderOf (r : P) = 3 :=
    (Subgroup.orderOf_coe r).trans hrOrder
  have hgOrder : orderOf g = 3 := by
    calc
      orderOf g = orderOf (r : P) :=
        Subgroup.orderOf_coe _
      _ = 3 := hrPOrder
  have hgSupport : g.support.card = 18 := by
    simpa only [g] using hrSupport
  have hBcard :
      Fintype.card
          (cycleSupportFinset g) = 6 :=
    cycleSupportFinset_card_of_order_three_support_eighteen
      g hgOrder hgSupport
  have htNOrder : orderOf tN = 2 := by
    calc
      orderOf tN = orderOf t₀ :=
        Subgroup.orderOf_coe _
      _ = 2 := by
        simpa only [t₀, ρ, N, F] using htOrder
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
  have hψt : ψ tN ≠ 1 := by
    intro hψOne
    apply hSupportNe
    have hsupport :=
      support_eq_twelve_of_inverting_cycleSupport_action_eq_one
        X P R r hRgenerated tN hrOrder hrSupport
          htNOrder
          (by
            simpa only [tN, t₀, tP, ρ, N, F] using
              hinverts)
          (by
            simpa only [g, tPerm, tP] using htFix)
          (by
            simpa only [ψ] using hψOne)
    simpa only [tPerm, tP, tN, t₀, ρ, N, F] using
      hsupport
  apply
    auxiliary_range_card_lt_three_hundred_sixty_of_small_kernel
      N F
        (cycleSupportFinset g)
        hBcard ρ ψ
  · rw [show Nat.card ρ.ker = 6 by
      simpa only [ρ, N, F] using hKerCard]
  · exact ⟨t₀, by
      simpa only [t₀] using hψt⟩

end FiveTransitive.Degree24

end CFSG
