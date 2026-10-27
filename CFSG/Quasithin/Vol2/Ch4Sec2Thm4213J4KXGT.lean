module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXJ3
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open
open scoped commutatorElement

noncomputable def quotCenterEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)

theorem card_center_eq_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center B) = Nat.card (Subgroup.center A) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

section SubgroupOf

variable {G : Type} [Group G] {C KX : Subgroup G}

theorem isQuasisimple_subgroupOf (h : KX ≤ C) (hq : CFSG.IsQuasisimple ↥KX) :
    CFSG.IsQuasisimple ↥(KX.subgroupOf C) :=
  CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h) hq

theorem card_center_subgroupOf (h : KX ≤ C) :
    Nat.card (Subgroup.center ↥(KX.subgroupOf C)) = Nat.card (Subgroup.center ↥KX) :=
  (card_center_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h)).symm

theorem exists_e0_subgroupOf (h : KX ≤ C) (E0 : Subgroup (↥KX ⧸ Subgroup.center ↥KX))
    (hE0 : IsElemAbelian 3 E0) (hE0c : Nat.card E0 = 9) :
    ∃ E0' : Subgroup (↥(KX.subgroupOf C) ⧸ Subgroup.center ↥(KX.subgroupOf C)),
      IsElemAbelian 3 E0' ∧ Nat.card E0' = 9 := by
  refine ⟨E0.map (quotCenterEquiv (Subgroup.subgroupOfEquivOfLe h)).symm.toMonoidHom,
    isElemAbelian_map_aux hE0 _, ?_⟩
  have hinj : Function.Injective (quotCenterEquiv (Subgroup.subgroupOfEquivOfLe h)).symm.toMonoidHom :=
    (quotCenterEquiv (Subgroup.subgroupOfEquivOfLe h)).symm.injective
  rw [Subgroup.card_map_of_injective hinj, hE0c]

theorem isSporadic_M22_subgroupOf (h : KX ≤ C)
    (hM : CFSG.Quasithin.IsSporadic .M22 (↥KX ⧸ Subgroup.center ↥KX)) :
    CFSG.Quasithin.IsSporadic .M22 (↥(KX.subgroupOf C) ⧸ Subgroup.center ↥(KX.subgroupOf C)) :=
  CFSG.Quasithin.IsSporadic.of_mulEquiv
    (quotCenterEquiv (Subgroup.subgroupOfEquivOfLe h)).symm hM

end SubgroupOf

theorem isPerfect_of_commutator_eq {Γ : Type} [Group Γ] {J : Subgroup Γ} (h : ⁅J, J⁆ = J) :
    Group.IsPerfect ↥J := by
  constructor
  apply Subgroup.map_injective (f := J.subtype) J.subtype_injective
  have htop : (⊤ : Subgroup ↥J).map J.subtype = J := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  change Subgroup.map J.subtype ⁅(⊤ : Subgroup ↥J), ⊤⁆ = Subgroup.map J.subtype (⊤ : Subgroup ↥J)
  rw [Subgroup.map_commutator, htop, h]

theorem central_of_commutator_central {Q : Type} [Group Q] (hP : ⁅(⊤ : Subgroup Q), ⊤⁆ = (⊤ : Subgroup Q))
    (x : Q) (hx : ∀ q : Q, ⁅x, q⁆ ∈ Subgroup.center Q) : x ∈ Subgroup.center Q := by
  have key : ∀ a b : Q, ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
    intro a b
    rw [commutatorElement_mul_expand]
    congr 1
    have hc : a * ⁅x, b⁆ = ⁅x, b⁆ * a := Subgroup.mem_center_iff.mp (hx b) a
    rw [hc]
    group
  let f : Q →* Q := MonoidHom.mk' (fun q => ⁅x, q⁆) key
  have hS : ∀ a ∈ (Subgroup.center Q : Set Q), ∀ b ∈ (Subgroup.center Q : Set Q),
      a * b = b * a := fun a _ b hb => (Subgroup.mem_center_iff.mp hb a)
  have htriv := hom_trivial_of_commuting_values hP f (Subgroup.center Q : Set Q) hS
    (fun q => hx q)
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have h1 : ⁅x, g⁆ = 1 := htriv g
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

end CFSG.Quasithin.H13.Ch4.J4KX

end
