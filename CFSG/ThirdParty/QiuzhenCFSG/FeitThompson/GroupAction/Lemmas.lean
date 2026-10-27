module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Basic

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

public theorem CFSG.semidirect_comm_inl_inv_inr {G A : Type*} [Group G] [Group A] (φ : A →* MulAut G)
    (a : A) (g : G) :
    ⁅(((SemidirectProduct.inl (φ := φ) g : G ⋊[φ] A))⁻¹), (SemidirectProduct.inr (φ := φ) a)⁆ =
      SemidirectProduct.inl (φ := φ) (g⁻¹ * ((φ a) g)) := by
  let inl : G →* G ⋊[φ] A := SemidirectProduct.inl (φ := φ)
  let inr : A →* G ⋊[φ] A := SemidirectProduct.inr (φ := φ)
  have hconj : (inr a : G ⋊[φ] A) * (inl g : G ⋊[φ] A) * (inr a : G ⋊[φ] A)⁻¹ = inl ((φ a) g) := by
    simpa [inl, inr] using (SemidirectProduct.inl_aut (φ := φ) a g).symm
  calc
    ⁅(((inl g : G ⋊[φ] A))⁻¹), (inr a)⁆
        =
        ((inl g : G ⋊[φ] A)⁻¹) * (inr a : G ⋊[φ] A) * ((inl g : G ⋊[φ] A)⁻¹)⁻¹ *
            (inr a : G ⋊[φ] A)⁻¹ := by
          rw [commutatorElement_def]
    _ = ((inl g : G ⋊[φ] A)⁻¹) * ((inr a : G ⋊[φ] A) * (inl g : G ⋊[φ] A) * (inr a : G ⋊[φ] A)⁻¹) := by
          simp [mul_assoc]
    _ = ((inl g : G ⋊[φ] A)⁻¹) * inl ((φ a) g) := by
          simp [hconj]
    _ = inl (g⁻¹ * ((φ a) g)) := by
          simp [inl]

/-!
Small semidirect-product bridges used to translate `fixedPointSubgroup`/`commutatorAction`
statements into subgroup commutators in `G ⋊ A`.
-/

namespace CFSG.Semidirect

open scoped Pointwise

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

local notation "φ₀" => (MulDistribMulAction.toMulAut A G)
local notation "SD" => (G ⋊[φ₀] A)
local notation "inl" => (SemidirectProduct.inl (φ := φ₀) : G →* SD)
local notation "inr" => (SemidirectProduct.inr (φ := φ₀) : A →* SD)


end CFSG.Semidirect

public theorem CFSG.commutatorAction_eq_closure {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    commutatorAction (A := A) (G := G) =
      Subgroup.closure {x : G | ∃ a : A, ∃ g : G, x = g⁻¹ * (a • g)} := by
  ext x
  simp [commutatorAction, commutatorSubgroup]


public theorem CFSG.commutatorAction₂_le_commutatorAction
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    commutatorAction₂ (A := A) (G := G) ≤ commutatorAction (A := A) (G := G) := by
  change commutatorSubgroup (A := A) (G := G) (H := commutatorAction (A := A) (G := G)) ≤
      commutatorAction (A := A) (G := G)
  refine (Subgroup.closure_le (K := commutatorAction (A := A) (G := G))).2 ?_
  intro x hx
  rcases hx with ⟨a, g, _hg, rfl⟩
  rw [commutatorAction_eq_closure (G := G) (A := A)]
  exact Subgroup.subset_closure ⟨a, g, rfl⟩


public theorem CFSG.fixedPointSubgroup_map_subtype_eq_inf
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [IsInvariant A G H] :
    (fixedPointSubgroup A H).map H.subtype = H ⊓ fixedPointSubgroup A G := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor
    · exact y.property
    · change (y : G) ∈ fixedPointSubgroup A G
      have hy' : ∀ a : A, a • (y : G) = (y : G) := by
        intro a
        exact congrArg Subtype.val (by simpa [fixedPointSubgroup] using (show a • y = y from by simpa [fixedPointSubgroup] using hy a))
      simpa [fixedPointSubgroup] using hy'
  · rintro ⟨hxH, hxFix⟩
    have hxFix' : ∀ a : A, a • x = x := by
      simpa [fixedPointSubgroup] using hxFix
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    change ∀ a : A, a • ((⟨x, hxH⟩ : H) : H) = ⟨x, hxH⟩
    intro a
    ext
    exact hxFix' a


set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.commutatorAction_normal_and_invariant {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] :
    (commutatorAction (A := A) (G := G)).Normal ∧
      IsInvariant A G (commutatorAction (A := A) (G := G)) := by
  let N : Subgroup G := commutatorAction (A := A) (G := G)
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  let SD := G ⋊[φ] A
  letI : Group SD := by
    infer_instance
  let inl : G →* SD := SemidirectProduct.inl (φ := φ)
  let inr : A →* SD := SemidirectProduct.inr (φ := φ)
  let HG : Subgroup SD := (⊤ : Subgroup G).map inl
  let HA : Subgroup SD := (⊤ : Subgroup A).map inr
  let C : Subgroup SD := ⁅HG, HA⁆

  have hinl_inj : Function.Injective (inl : G → SD) := by
    simpa [inl] using
      (SemidirectProduct.inl_injective (φ := φ) :
        Function.Injective (SemidirectProduct.inl (φ := φ) : G → SD))

  have comm_inl_inr (a : A) (g : G) :
      ⁅((inl g : SD)⁻¹), (inr a)⁆ = inl (g⁻¹ * (a • g)) := by
    simpa [SD, inl, inr, φ] using
      (semidirect_comm_inl_inv_inr (φ := φ) a g)

  have hN_def :
      N = Subgroup.closure {x : G | ∃ a : A, ∃ g : G, x = g⁻¹ * (a • g)} := by
    simpa [N] using (commutatorAction_eq_closure (G := G) (A := A))

  have hmap : N.map inl = C := by
    let S : Set G := {x : G | ∃ a : A, ∃ g : G, x = g⁻¹ * (a • g)}
    have hN' : N = Subgroup.closure S := by
      simpa [S] using hN_def
    have hmap_closure : N.map inl = Subgroup.closure (inl '' S) := by
      simpa [hN'] using (MonoidHom.map_closure inl S)
    rw [hmap_closure]
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le (K := C) (k := inl '' S)).2 ?_
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      rcases hy with ⟨a, g, rfl⟩
      have hg : (inl g : SD) ∈ HG := Subgroup.mem_map_of_mem inl (by simp)
      have hg' : ((inl g : SD)⁻¹) ∈ HG := HG.inv_mem hg
      have ha : inr a ∈ HA := Subgroup.mem_map_of_mem inr (by simp)
      have hcomm : ⁅((inl g : SD)⁻¹), inr a⁆ ∈ C := Subgroup.commutator_mem_commutator hg' ha
      simpa [comm_inl_inr (a := a) (g := g)] using hcomm
    · refine (Subgroup.commutator_le).2 ?_
      intro x hx y hy
      rcases (Subgroup.mem_map).1 hx with ⟨g, _hg, rfl⟩
      rcases (Subgroup.mem_map).1 hy with ⟨a, _ha, rfl⟩
      have : inl (g * (a • g)⁻¹) ∈ Subgroup.closure (inl '' S) := by
        refine Subgroup.subset_closure ?_
        refine ⟨g * (a • g)⁻¹, ?_, rfl⟩
        refine ⟨a, g⁻¹, ?_⟩
        simp
      have hcomm' : ⁅inl g, inr a⁆ = inl (g * (a • g)⁻¹) := by
        simpa [inv_inv] using (comm_inl_inr (a := a) (g := g⁻¹))
      simpa [hcomm'] using this

  have pullback_mem_N_of_inl_mem_C {y : G} (hy : inl y ∈ C) : y ∈ N := by
    have : inl y ∈ N.map inl := by simpa [hmap] using hy
    rcases (Subgroup.mem_map).1 this with ⟨m, hm, hmEq⟩
    have : m = y := hinl_inj (by simpa [inl] using hmEq)
    simpa [this] using hm

  have hC_normal : ((C).subgroupOf (HG ⊔ HA)).Normal := commutator_normal_in_sup HG HA
  have hC_le : C ≤ HG ⊔ HA := commutator_le_sup HG HA

  have hconj : ∀ c s : SD, c ∈ C → s ∈ HG ⊔ HA → s * c * s⁻¹ ∈ C := by
    exact (Subgroup.normal_subgroupOf_iff (H := C) (K := HG ⊔ HA) hC_le).1 hC_normal

  have conj_mem_N {g n : G} (hn : n ∈ N) : g * n * g⁻¹ ∈ N := by
    have hnC : (inl n : SD) ∈ C := by
      have : (inl n : SD) ∈ N.map inl := Subgroup.mem_map_of_mem inl hn
      simpa [hmap] using this
    have hgSup : (inl g : SD) ∈ HG ⊔ HA := by
      have : (inl g : SD) ∈ HG := Subgroup.mem_map_of_mem inl (by simp)
      exact (le_sup_left : HG ≤ HG ⊔ HA) this
    have h_conj : (inl g : SD) * (inl n : SD) * (inl g : SD)⁻¹ ∈ C :=
      hconj (c := inl n) (s := inl g) hnC hgSup
    have h_in_C : (inl (g * n * g⁻¹) : SD) ∈ C := by
      simpa [inl, mul_assoc] using h_conj
    exact pullback_mem_N_of_inl_mem_C h_in_C

  have smul_mem_N (a : A) {g : G} (hg : g ∈ N) : a • g ∈ N := by
    have hgC : (inl g : SD) ∈ C := by
      have : (inl g : SD) ∈ N.map inl := Subgroup.mem_map_of_mem inl hg
      simpa [hmap] using this
    have haSup : (inr a : SD) ∈ HG ⊔ HA := by
      have : (inr a : SD) ∈ HA := Subgroup.mem_map_of_mem inr (by simp)
      exact (le_sup_right : HA ≤ HG ⊔ HA) this
    have h_conj : (inr a : SD) * (inl g : SD) * (inr a : SD)⁻¹ ∈ C :=
      hconj (c := inl g) (s := inr a) hgC haSup
    have h_in_C : (inl (a • g) : SD) ∈ C := by
      have hconj_eq : (inr a : SD) * (inl g : SD) * (inr a : SD)⁻¹ = inl (a • g) := by
        simpa [inl, inr, φ] using (SemidirectProduct.inl_aut (φ := φ) a g).symm
      simpa [hconj_eq] using h_conj
    exact pullback_mem_N_of_inl_mem_C h_in_C

  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    intro n hn g
    simpa [N] using conj_mem_N (g := g) (n := n) hn
  · constructor
    intro a g
    constructor
    · intro hg
      simpa [N] using smul_mem_N (a := a) (g := g) hg
    · intro hg
      have : a⁻¹ • (a • g) ∈ N := smul_mem_N (a := a⁻¹) (g := a • g) hg
      simpa [smul_smul] using this


public theorem CFSG.commutatorAction_normal
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    (commutatorAction (A := A) (G := G)).Normal :=
  (commutatorAction_normal_and_invariant (G := G) (A := A)).1

public theorem CFSG.commutatorAction_isInvariant
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    IsInvariant A G (commutatorAction (A := A) (G := G)) :=
  (commutatorAction_normal_and_invariant (G := G) (A := A)).2


public theorem CFSG.commutatorAction_map_subtype_eq_commutatorAction₂
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    let H : Subgroup G := commutatorAction (A := A) (G := G)
    letI : IsInvariant A G H := (commutatorAction_normal_and_invariant (G := G) (A := A)).2
    (commutatorAction (A := A) (G := H)).map H.subtype = commutatorAction₂ (A := A) (G := G) := by
  classical
  let H : Subgroup G := commutatorAction (A := A) (G := G)
  letI : IsInvariant A G H := (commutatorAction_normal_and_invariant (G := G) (A := A)).2
  let SH : Set H := {x : H | ∃ a : A, ∃ h : H, x = h⁻¹ * (a • h)}
  let SG : Set G := {x : G | ∃ a : A, ∃ g : G, g ∈ H ∧ x = g⁻¹ * (a • g)}
  have himage : H.subtype '' SH = SG := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨a, h, rfl⟩
      exact ⟨a, (h : G), h.property, by rfl⟩
    · rintro ⟨a, g, hg, rfl⟩
      refine ⟨((⟨g, hg⟩ : H)⁻¹ * (a • (⟨g, hg⟩ : H))), ?_, ?_⟩
      · exact ⟨a, ⟨g, hg⟩, rfl⟩
      · rfl
  calc
    (commutatorAction (A := A) (G := H)).map H.subtype
        = (Subgroup.closure SH).map H.subtype := by
            simpa [SH] using (congrArg (fun K : Subgroup H => K.map H.subtype)
              (commutatorAction_eq_closure (G := H) (A := A)))
    _ = Subgroup.closure (H.subtype '' SH) := by
          simpa using (MonoidHom.map_closure (f := H.subtype) SH)
    _ = Subgroup.closure SG := by
          simpa using congrArg Subgroup.closure himage
    _ = commutatorAction₂ (A := A) (G := G) := by
          simp [commutatorAction₂, commutatorSubgroup, SG, H]


section subgroupOf

variable {G : Type*} [Group G]

public lemma CFSG.subgroupOf_map_subtype_eq {K : Subgroup G} (H : Subgroup K) :
    (H.map K.subtype).subgroupOf K = H := by
  ext x; simp [Subgroup.mem_subgroupOf]

end subgroupOf

section card

variable {G : Type*} [Group G]

public lemma CFSG.natCard_subgroupOf_eq (H K : Subgroup G) (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (G := G) (H := H) (K := K) hHK).toEquiv

end card

section PGroupAction

variable {A G : Type*} [Group A] [Group G] [Finite G] [MulDistribMulAction A G]

/-- If a `p`-group `A` acts on a cyclic group `G` of order `p`, then the action is trivial. -/
public theorem CFSG.actsTrivially_of_isPGroup_on_cyclic_prime_order
    {p : ℕ} (hp : Nat.Prime p) (hA : IsPGroup p A) (hG_cyclic : IsCyclic G)
    (hG_card : Nat.card G = p) :
    ActsTrivially (A := A) (G := G) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic G := hG_cyclic
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  have hA_top : IsPGroup p (⊤ : Subgroup A) := by
    simpa using hA.to_subgroup (⊤ : Subgroup A)
  have hφrange_p : IsPGroup p φ.range := by
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup A)) hA_top φ
  have hmulAut_card : Nat.card (MulAut G) = p - 1 := by
    rw [IsCyclic.card_mulAut, hG_card, Nat.totient_prime hp]
  have hp_not_dvd_mulAut : ¬ p ∣ Nat.card (MulAut G) := by
    intro hp_dvd
    have hdiv_one : p ∣ 1 := by
      have hdiv_sub : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) (hmulAut_card ▸ hp_dvd)
      have hsub : p - (p - 1) = 1 := by
        have hp_eq : p = (p - 1) + 1 := by
          simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hp.pos).symm
        rw [hp_eq]
        exact Nat.add_sub_cancel_left (p - 1) 1
      rw [hsub] at hdiv_sub
      exact hdiv_sub
    exact hp.not_dvd_one hdiv_one
  have hp_not_dvd_range : ¬ p ∣ Nat.card φ.range := by
    intro hp_dvd
    exact hp_not_dvd_mulAut (hp_dvd.trans (Subgroup.card_subgroup_dvd_card φ.range))
  have hφrange_card_one : Nat.card φ.range = 1 :=
    (hφrange_p.card_eq_or_dvd).resolve_right hp_not_dvd_range
  have hφrange_bot : φ.range = ⊥ := (Subgroup.card_eq_one (H := φ.range)).1 hφrange_card_one
  intro a g
  have ha_range : φ a ∈ φ.range := ⟨a, rfl⟩
  have ha_bot : φ a ∈ (⊥ : Subgroup (MulAut G)) := by simpa [hφrange_bot] using ha_range
  have ha_one : φ a = 1 := by simpa using ha_bot
  simpa [φ, MulDistribMulAction.toMulAut_apply] using congrArg (fun f : MulAut G => f g) ha_one

end PGroupAction
