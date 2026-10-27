module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULinDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceUAuxAbs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem su_reduceU_of_leaves : SUPInvLeaf → SUPCentLeaf → SUStabCardLeaf → (SUNormalizerLeaf → ∀ (p
    : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis
    (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)), SULinData p m V b H A → (∀ r ∈ H,
    GGLinRefl r → ggLinMove r ≤ SUAug p b) → SUClassReady p m H) := by
  intro hP1 hP2 hP3
  intro hN p hpFact m V instAC instMod b H A hD hU
  haveI : NeZero m := ⟨by have := hD.hm; omega⟩
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ m := (CharP.cast_eq_zero_iff (ZMod p) p m).mp h
    rw [hD.hp] at hpdiv
    exact hD.h3 hpdiv
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    rw [hD.hp] at hpdiv
    norm_num at hpdiv
  obtain ⟨S, hS, hScl, -⟩ := hD.hgen
  have hSker : S ⊆ hdRo7SUReduceUAux_kerAug p (SUAug p b) := by
    intro s hs v
    exact (hU s (hS s hs).1 (hS s hs).2) (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  have hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b) := by
    rw [hScl]
    exact (Subgroup.closure_le _).mpr hSker
  let res := hdRo7SUReduceUAux_res (SUAug p b) H hHK
  let R : Subgroup (↥(SUAug p b) ≃ₗ[ZMod p] ↥(SUAug p b)) := res.range
  have hresinj : Function.Injective res :=
    hdRo7SUReduceUAux_res_injective b hm0 H A hHK hD.hHA hD.hNoT
  have hcardRH : Nat.card ↥R = Nat.card ↥H :=
    hdRo7SUReduceUAux_card_range b hHK hresinj
  have hRgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} :=
    hdRo7SUReduceUAux_range_eq_closure b hHK S hS hScl h2
  have habs : ZS.AbsIrred p R :=
    ⟨hdRo7SUReduceUAux_irreducible hP1 b hD hHK hm0,
     hdRo7SUReduceUAux_commutant hP2 b hD hHK hm0⟩
  have hcard : Nat.card ↥R ≤ 2 * 3 ^ (m - 1) * ((m - 1 + 1).factorial) := by
    rw [hcardRH]
    exact hdRo7SUReduceUAux_card_le b hm0 hN hP3 hD hHK
  have hlift := hdRo7SUReduceUAux_linWeyl_lift b hHK h2 hresinj
  exact ⟨m - 1, ↥(SUAug p b), inferInstance, inferInstance, R, Or.inl rfl,
    hdRo7SUReduceUAux_finrank_aug b hm0, habs, hRgen, hcard, hlift⟩

end CFSG.StandardType.HdRo7SU
