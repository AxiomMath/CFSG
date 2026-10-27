module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.GroupTheory.ConjNormalFaithful

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {Y : Type} [Group Y]

theorem card_inner_of_center_eq_bot {G : Type*} [Group G] (h : center G = ⊥) :
    Nat.card (inner G) = Nat.card G := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← h]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have e := congrArg (fun α : MulAut G => α y) (MonoidHom.mem_ker.1 hx)
    simp only [MulAut.conj_apply, MulAut.one_apply] at e
    calc y * x = x * y * x⁻¹ * x := by rw [e]
      _ = x * y := by group
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem center_eq_bot_of_centralizer_eq_bot (L : Subgroup Y)
    (hC : centralizer (L : Set Y) = ⊥) : center ↥L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzC : (z : Y) ∈ centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨y, hy⟩)
  rw [hC, Subgroup.mem_bot] at hzC
  exact (Subgroup.mem_bot).2 (Subtype.ext hzC)

theorem nonempty_mulEquiv_or_of_card_outer_eq_two {C : Type} [Group C] [Finite Y]
    (hOut : Nat.card (Outer C) = 2) (L : Subgroup Y) [L.Normal] (φ : ↥L ≃* C)
    (hC : centralizer (L : Set Y) = ⊥) :
    Nonempty (Y ≃* C) ∨ Nonempty (Y ≃* MulAut C) := by
  have hOutL : Nat.card (Outer ↥L) = 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv,
      hOut]
  have hidx := (index_le_card_outer L hC).trans hOutL.le
  have hpos : 0 < L.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : L.index = 1 ∨ L.index = 2) with h1 | h2
  · left
    have hLt : L = ⊤ := Subgroup.index_eq_one.1 h1
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLt.symm)).trans φ⟩
  · right
    have hinj := Subgroup.conjNormal_injective_of_centralizer_eq_bot hC
    have hcardAut : Nat.card (MulAut ↥L) = 2 * Nat.card ↥L := by
      rw [(inner ↥L).card_eq_card_quotient_mul_card_subgroup,
        card_inner_of_center_eq_bot (center_eq_bot_of_centralizer_eq_bot L hC)]
      exact congrArg (· * Nat.card ↥L) hOutL
    have hcardY : Nat.card Y = 2 * Nat.card ↥L := by
      rw [← L.index_mul_card, h2]
    have hbij : Function.Bijective (MulAut.conjNormal : Y →* MulAut ↥L) :=
      hinj.bijective_of_nat_card_le (by rw [hcardAut, hcardY])
    exact ⟨(MulEquiv.ofBijective _ hbij).trans (MulAut.congr φ)⟩

theorem lGen_eq_top_of_isLPair_of_card_outer_eq_two {C D : Type} [Group C] [Group D] [Finite C]
    [Finite D] [Finite Y] {P : ∀ (X : Type) [Group X], Prop} (hOut : Nat.card (Outer C) = 2)
    (eD : MulAut C ≃* D) {T₀ A₀ B₀ : Subgroup C} (hT₀ : IsSylowIn 2 T₀ ⊤)
    (h : IsLPair P T₀ A₀ B₀) {T₁ A₁ B₁ : Subgroup D} (hT₁ : IsSylowIn 2 T₁ ⊤)
    (h' : IsLPair P T₁ A₁ B₁) (L : Subgroup Y) [L.Normal] (φ : ↥L ≃* C)
    (hC : centralizer (L : Set Y) = ⊥) {T : Subgroup Y} (hT : IsSylowIn 2 T ⊤) :
    lGen P ⊤ T = ⊤ := by
  rcases nonempty_mulEquiv_or_of_card_outer_eq_two hOut L φ hC with h1 | h2
  · obtain ⟨e⟩ := h1
    exact lGen_eq_top_of_isLPair_mulEquiv hT₀ h e.symm hT
  · obtain ⟨e⟩ := h2
    exact lGen_eq_top_of_isLPair_mulEquiv hT₁ h' (e.trans eD).symm hT

theorem asch54SporGenAt_of_isLPair_of_card_outer_eq_two {s : TauCeti.SporadicName} {C D : Type}
    [Group C] [Group D] [Finite C] [Finite D]
    (hsC : ∀ (X : Type) [Group X], CFSG.Models.IsSporadic X s → Nonempty (X ≃* C))
    (hOut : Nat.card (Outer C) = 2) (eD : MulAut C ≃* D) {T₀ A₀ B₀ : Subgroup C}
    (hT₀ : IsSylowIn 2 T₀ ⊤) (h : IsLPair IsCalL0 T₀ A₀ B₀) {T₁ A₁ B₁ : Subgroup D}
    (hT₁ : IsSylowIn 2 T₁ ⊤) (h' : IsLPair IsCalL0 T₁ A₁ B₁) : Asch54SporGenAt s := by
  intro Q _ _ L T hLn hL hC hT
  obtain ⟨φ⟩ := hsC ↥L hL
  exact lGen_eq_top_of_isLPair_of_card_outer_eq_two hOut eD hT₀ h hT₁ h' L φ hC hT

end CFSG.LocalAnalysis.WeakClosure81

end
