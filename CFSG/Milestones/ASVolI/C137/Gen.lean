module

public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

variable {G : Type} [Group G]

theorem burnsideC137_isG2Two_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsG2Two A) : IsG2Two B := by
  obtain ⟨hc, hz, D, hDn, hDi, hD⟩ := h
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans hc, ?_, D.map e.toMonoidHom, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro b hb
    have ha : e.symm b ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff] at hb ⊢
      intro a
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hb (e a)
    rw [hz, Subgroup.mem_bot] at ha
    rw [Subgroup.mem_bot]
    simpa using congrArg e ha
  · exact hDn.map e.toMonoidHom e.surjective
  · exact (Subgroup.index_map_equiv D e).trans hDi
  · exact IsPSU.of_mulEquiv (D.equivMapOfInjective e.toMonoidHom e.injective) hD

noncomputable def burnsideC137_autIEquiv {X U V : Subgroup G} (hU : IsElemAbelian 2 U)
    (hV : IsElemAbelian 2 V) (hXU : X ≤ normalizer (U : Set G))
    (hXV : X ≤ normalizer (V : Set G))
    (hC : X ⊓ centralizer (U : Set G) = X ⊓ centralizer (V : Set G)) :
    ↥(autI hU X) ≃* ↥(autI hV X) :=
  have hker : (convHom hU X hXU).ker = (convHom hV X hXV).ker := by
    rw [ker_convHom, ker_convHom, hC]
  (MulEquiv.subgroupCongr (range_convHom hU X hXU).symm).trans
    ((QuotientGroup.quotientKerEquivRange (convHom hU X hXU)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        ((QuotientGroup.quotientKerEquivRange (convHom hV X hXV)).trans
          (MulEquiv.subgroupCongr (range_convHom hV X hXV)))))

theorem burnsideC137_mem_normalizer_centralizer {L : Subgroup G} {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    x ∈ normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : ∀ g y : G, g ∈ normalizer (L : Set G) → y ∈ centralizer (L : Set G) →
      g * y * g⁻¹ ∈ centralizer (L : Set G) := by
    intro g y hg hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) l).1 hl
      simpa using this
    have h1 := hy _ hl'
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * l := by group
  constructor
  · exact key x y hx
  · intro h
    have := key x⁻¹ _ (Subgroup.inv_mem _ hx) h
    simpa [mul_assoc] using this

theorem burnsideC137_isIrrSection_of_isIrrSec {X L U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hLX : L ≤ X) (hXU : X ≤ normalizer (U : Set G)) (hXL : X ≤ normalizer (L : Set G))
    (hirr : XMod.IsIrrSec ↥(autI hU L) (XMod.fixed ↥(autI hU L) (⊤ : Subgroup (IntMod U hU)))
      (⊤ : Subgroup (IntMod U hU))) :
    IsIrrSection X (U ⊓ centralizer (L : Set G)) U := by
  have hLU : L ≤ normalizer (U : Set G) := hLX.trans hXU
  have hfix : ∀ w : IntMod U hU, w ∈ XMod.fixed ↥(autI hU L) (⊤ : Subgroup (IntMod U hU)) ↔
      w.val ∈ centralizer (L : Set G) := by
    intro w
    rw [← mem_fixV_autI hU hLU w]
    constructor
    · rintro ⟨-, hw⟩ a ha
      exact hw ⟨a, ha⟩
    · intro hw
      exact ⟨Subgroup.mem_top w, fun a => hw a.1 a.2⟩
  let pull : Subgroup G → Subgroup (IntMod U hU) := fun K =>
    { carrier := {w | w.val ∈ K}
      one_mem' := K.one_mem
      mul_mem' := fun {a b} ha hb => K.mul_mem ha hb
      inv_mem' := fun {a} ha => K.inv_mem ha }
  have hpull : ∀ K w, w ∈ pull K ↔ w.val ∈ K := fun _ _ => Iff.rfl
  obtain ⟨hlt, hmax⟩ := hirr
  have hXZ : X ≤ normalizer ((U ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hXU hx) y
    have h2 := Subgroup.mem_normalizer_iff.1 (burnsideC137_mem_normalizer_centralizer (hXL hx)) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  refine ⟨?_, hXZ, hXU, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun heq => ?_
    apply hlt.ne
    ext w
    refine ⟨fun _ => Subgroup.mem_top w, fun _ => (hfix w).2 ?_⟩
    have hwU : w.val ∈ U ⊓ centralizer (L : Set G) := by rw [heq]; exact w.val_mem
    exact hwU.2
  · intro K hZK hKU hXK
    have hinv : XMod.IsInv ↥(autI hU L) (pull K) := by
      rintro ⟨a, ha⟩ w hw
      obtain ⟨g, hgL, rfl⟩ := (mem_autI hU).1 ha
      rw [hpull]
      change ((convI hU g) w).val ∈ K
      rw [convI_apply_val]
      exact (Subgroup.mem_normalizer_iff.1 (hXK (hLX hgL)) _).1 hw
    have hle : XMod.fixed ↥(autI hU L) (⊤ : Subgroup (IntMod U hU)) ≤ pull K := by
      intro w hw
      exact hZK ⟨w.val_mem, (hfix w).1 hw⟩
    rcases hmax (pull K) hinv hle le_top with h1 | h1
    · left
      refine le_antisymm (fun k hk => ?_) hZK
      have hk' : IntMod.mk hU ⟨k, hKU hk⟩ ∈ pull K := hk
      rw [h1] at hk'
      exact ⟨hKU hk, (hfix _).1 hk'⟩
    · right
      refine le_antisymm hKU fun u hu => ?_
      have hu' : IntMod.mk hU ⟨u, hu⟩ ∈ pull K := by rw [h1]; exact Subgroup.mem_top _
      exact hu'

theorem burnsideC137_relIndex_of_surj [Finite G] {U Z : Subgroup G} (hU : IsElemAbelian 2 U)
    {M : Type*} [Group M] (f : IntMod U hU →* M) (hfs : Function.Surjective f)
    (hfk : ∀ w : IntMod U hU, f w = 1 ↔ w.val ∈ Z) :
    Z.relIndex U = Nat.card M := by
  classical
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv] at h1
  have hk : Nat.card ↥f.ker = Nat.card ↥(Z.subgroupOf U) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨⟨w.1.val, w.1.val_mem⟩, (hfk w.1).1 w.2⟩
        invFun := fun z => ⟨IntMod.mk hU z.1, (hfk _).2 z.2⟩
        left_inv := fun w => rfl
        right_inv := fun z => rfl }
  have hU' : Nat.card (IntMod U hU) = Nat.card ↥U := rfl
  have h2 := Subgroup.card_mul_index (Z.subgroupOf U)
  have hpos : 0 < Nat.card ↥(Z.subgroupOf U) := Nat.card_pos
  rw [hk, hU'] at h1
  rw [Subgroup.relIndex]
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h2, h1, mul_comm]

end CFSG.ASVolI
