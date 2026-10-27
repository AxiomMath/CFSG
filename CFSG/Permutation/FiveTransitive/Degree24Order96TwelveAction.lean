module

public import CFSG.Permutation.FiveTransitive.Degree24Order96CycleSupports

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

private theorem cycleSupports_eq_of_common_mem
    {X : Type} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X)
    {b d : Finset X}
    (hb : b ∈ cycleSupportFinset g)
    (hd : d ∈ cycleSupportFinset g)
    {x : X} (hxb : x ∈ b) (hxd : x ∈ d) :
    b = d := by
  classical
  obtain ⟨c, hc, hcb⟩ :=
    Finset.mem_image.mp hb
  obtain ⟨e, he, hed⟩ :=
    Finset.mem_image.mp hd
  have hxc : x ∈ c.support := by
    rwa [hcb]
  have hxe : x ∈ e.support := by
    rwa [hed]
  have hcCycle :
      c = g.cycleOf x :=
    Equiv.Perm.cycle_is_cycleOf hxc hc
  have heCycle :
      e = g.cycleOf x :=
    Equiv.Perm.cycle_is_cycleOf hxe he
  calc
    b = c.support := hcb.symm
    _ = (g.cycleOf x).support := by
      rw [hcCycle]
    _ = e.support := by
      rw [heCycle]
    _ = d := hed

theorem cycleSupport_action_eq_one_of_inverting_support_eq_twelve
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (t : Subgroup.normalizer (R : Set P))
    (hrOrder : orderOf r = 3)
    (hrSupport :
      ((r : P) : Equiv.Perm X).support.card = 18)
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
    (htSupport :
      ((((t :
        Subgroup.normalizer (R : Set P)) : P) :
          Equiv.Perm X).support.card = 12)) :
    normalizerCycleSupportMap
        X P R r hRgenerated hrOrder t = 1 := by
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
  let D : Type := ↥(g.support \ tPerm.support)
  have hDcard : Nat.card D = 6 := by
    have hpartition :=
      Finset.card_sdiff_add_card_eq_card
        htSupportSubset
    have htSupport' :
        tPerm.support.card = 12 := by
      simpa only [tPerm, tP] using htSupport
    rw [hgSupport, htSupport'] at hpartition
    rw [Nat.card_eq_fintype_card,
      Fintype.card_coe]
    omega
  have hBcard : Nat.card B = 6 := by
    rw [Nat.card_eq_fintype_card]
    simpa only [B] using
      cycleSupportFinset_card_of_order_three_support_eighteen
        g hgOrder hgSupport
  let f : D → B :=
    fun x =>
      ⟨(g.cycleOf x.1).support,
        Finset.mem_image.mpr
          ⟨g.cycleOf x.1,
            Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
              (Finset.mem_sdiff.mp x.2).1,
            rfl⟩⟩
  have hfInjective : Function.Injective f := by
    intro x y hxy
    have hsupportEq :
        (g.cycleOf x.1).support =
          (g.cycleOf y.1).support :=
      congrArg Subtype.val hxy
    have hyMem :
        y.1 ∈ (g.cycleOf x.1).support := by
      rw [hsupportEq,
        Equiv.Perm.mem_support_cycleOf_iff]
      exact
        ⟨Equiv.Perm.SameCycle.refl g y.1,
          (Finset.mem_sdiff.mp y.2).1⟩
    have hsame :
        g.SameCycle x.1 y.1 :=
      (Equiv.Perm.mem_support_cycleOf_iff.mp hyMem).1
    apply Subtype.ext
    exact
      eq_of_sameCycle_of_fixed_of_inverts_order_three
        g tPerm hgOrder hinvertsPerm
          (Finset.mem_sdiff.mp x.2).1
          (Finset.mem_sdiff.mp y.2).1
          (Equiv.Perm.notMem_support.mp
            (Finset.mem_sdiff.mp x.2).2)
          (Equiv.Perm.notMem_support.mp
            (Finset.mem_sdiff.mp y.2).2)
          hsame
  have hfSurjective : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfInjective, hDcard.trans hBcard.symm⟩).2
  apply Equiv.ext
  intro b
  apply Subtype.ext
  obtain ⟨x, hxb⟩ :=
    hfSurjective b
  have hcycleSupport :
      (g.cycleOf x.1).support = b.1 :=
    congrArg Subtype.val hxb
  have hxB : x.1 ∈ b.1 := by
    rw [← hcycleSupport,
      Equiv.Perm.mem_support_cycleOf_iff]
    exact
      ⟨Equiv.Perm.SameCycle.refl g x.1,
        (Finset.mem_sdiff.mp x.2).1⟩
  have htFixX : tPerm x.1 = x.1 :=
    Equiv.Perm.notMem_support.mp
      (Finset.mem_sdiff.mp x.2).2
  have hxSmul :
      tP • x.1 ∈ tP • b.1 :=
    Finset.smul_mem_smul_finset hxB
  have htPFixX : tP • x.1 = x.1 := by
    exact htFixX
  have hxImage :
      x.1 ∈
        ((normalizerCycleSupportMap
          X P R r hRgenerated hrOrder t) b).1 := by
    rw [normalizerCycleSupportMap_apply_val]
    rwa [htPFixX] at hxSmul
  exact
    cycleSupports_eq_of_common_mem
      g
      ((normalizerCycleSupportMap
        X P R r hRgenerated hrOrder t) b).2
      b.2 hxImage hxB

end FiveTransitive.Degree24

end CFSG
