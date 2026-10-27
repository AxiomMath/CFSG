module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelU
public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open SUTB NsFrameComp

namespace CoordSU

section Lift

variable {f n : ℕ} {K : Type} [Field K]

theorem exists_lift_pow_eq_one (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
    {ψ₁ : ↥(unitarySU 2 f K n) →* G} (hFk : SURep.GGFrameKer ψ₁) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f + 1) {b : G} (hb : b ∈ ψ₁.range) (hbp : b ^ p = 1) :
    ∃ X : ↥(unitarySU 2 f K n), X ^ p = 1 ∧ ψ₁ X = b := by
  have : Finite K := h.finite
  have : Finite ↥(unitarySU 2 f K n) := Subtype.finite
  obtain ⟨X₀, rfl⟩ := hb
  set z := X₀ ^ p with hz
  have hzk : ψ₁ z = 1 := by rw [hz, map_pow, hbp]
  have hnd : ¬ p ∣ orderOf z := by
    intro hd
    have h0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
    set w := z ^ (orderOf z / p) with hw
    have hwo : orderOf w = p := orderOf_pow_orderOf_div h0 hd
    have hwk : ψ₁ w = 1 := by rw [hw, map_pow, hzk, one_pow]
    have hw1 : w = 1 := by
      rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
      · apply Subtype.ext
        apply Units.ext
        ext x
        exact isEmptyElim x
      · obtain ⟨c, hc⟩ := hFk w hwk
        exact SUNS.eq_one_of_scalar_mem h hp hpq i hc (by rw [← hwo]; exact pow_orderOf_eq_one w)
    rw [hw1, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have hcomm : Commute X₀ (z ^ m)⁻¹ := by
    rw [hz, ← pow_mul]
    exact ((Commute.refl X₀).pow_right _).inv_right
  refine ⟨X₀ * (z ^ m)⁻¹, ?_, ?_⟩
  · rw [hcomm.mul_pow, inv_pow, ← pow_mul, mul_comm m p, pow_mul, hm, ← hz, mul_inv_cancel]
  · rw [map_mul, map_inv, map_pow, hzk, one_pow, inv_one, mul_one]

end Lift

section Moves

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

@[expose] def FrameMoves (F : PieceFrame f n K h p A) : Prop :=
  ∀ (π : Equiv.Perm (Fin F.r)) (η : Fin F.r → (ZMod p)ˣ), (∀ i, η i ∈ negQ p (2 ^ f)) →
    ∏ i, η i = 1 → ∃ w : ↥(unitarySU 2 f K n), ∀ s : Fin F.r → ZMod p,
      w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd fun i => (η i : ZMod p) * s (π i))

end Moves

end CoordSU

@[expose] def GGSUPieceMoveInput : Prop :=
  ∀ (f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (p : ℕ)
    (A : Subgroup ↥(unitarySU 2 f K n)), MaxElemAb p A →
      ∃ F : PieceFrame f n K h p A, CoordSU.FrameMoves F

@[expose] def GGSUPieceCompInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K)
    (p : ℕ) (A : Subgroup ↥(unitarySU 2 f K n)), MaxElemAb p A →
    ∀ F : PieceFrame f n K h p A, CoordSU.FrameMoves F → 4 ≤ F.r →
    ∀ ψ₁ : ↥(unitarySU 2 f K n) →* G, SURep.GGFrameKer ψ₁ →
    ∀ (L₁ : Subgroup G) (β : Fin F.r → ZMod p),
      IsComponentOf L₁ (ψ₁.range ⊓ Subgroup.centralizer {ψ₁ (F.ι (ofAdd β))}) →
      Nat.card ((ψ₁.comp F.ι).range ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
        (∃ j j' : Fin F.r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
          ∀ s : Fin F.r → ZMod p, s j = 0 → s j' = 0 → ψ₁ (F.ι (ofAdd s)) ∈ L₁) ∨
        (∃ (k : Fin F.r) (c : ZMod p) (ε : Fin F.r → (ZMod p)ˣ), c ≠ 0 ∧
          (∀ i, ε i ∈ CoordSU.negQ p (2 ^ f)) ∧ (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
          ∀ s : Fin F.r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
            ψ₁ (F.ι (ofAdd s)) ∈ L₁)

@[expose] def GGSUPieceShapeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K)
    (p : ℕ) (A : Subgroup ↥(unitarySU 2 f K n)), MaxElemAb p A →
    ∀ F : PieceFrame f n K h p A, CoordSU.FrameMoves F → 4 ≤ F.r →
    ∀ ψ₁ : ↥(unitarySU 2 f K n) →* G, SURep.GGFrameKer ψ₁ →
    ∀ E J : Subgroup G, E ≤ (ψ₁.comp F.ι).range →
      IsComponentOf J (ψ₁.range ⊓ Subgroup.centralizer (E : Set G)) →
      Nat.card ((ψ₁.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 3 →
        StepTwoToral.GGStepTwoCoordShape p F.r (CoordSU.negQ p (2 ^ f)) (ψ₁.comp F.ι) E

theorem ggSUNsCoordInput_of_piece (hmove : GGSUPieceMoveInput) (hcomp : GGSUPieceCompInput)
    (hshape : GGSUPieceShapeInput) : GGSUNsCoordInput := by
  intro G _ _ f n K _ h p _ hp2 hpq ψ₁ hFk Bs hBsle hBsel hcard4 hmax
  have hp : p.Prime := Fact.out
  have : Finite K := h.finite
  have hlift : ∀ b ∈ Bs, ∃ X : ↥(unitarySU 2 f K n), X ^ p = 1 ∧ ψ₁ X = b := fun b hb =>
    CoordSU.exists_lift_pow_eq_one h hFk hp hpq (hBsle hb) (hBsel.2 b hb)
  have hcomm : ∀ X Y : ↥(unitarySU 2 f K n), X ^ p = 1 → ψ₁ X ∈ Bs → ψ₁ Y ∈ Bs →
      X * Y = Y * X := fun X Y hXp hX hY =>
    SUNS.commute_of_frame_commute h hFk hp hpq hXp (TableB.IsElemAbelian.comm hBsel hX hY)
  let A : Subgroup ↥(unitarySU 2 f K n) :=
    { carrier := {X | X ^ p = 1 ∧ ψ₁ X ∈ Bs}
      mul_mem' := fun {X Y} hX hY => ⟨by
        rw [(show Commute X Y from hcomm X Y hX.1 hX.2 hY.2).mul_pow, hX.1, hY.1, one_mul], by
          rw [map_mul]; exact Bs.mul_mem hX.2 hY.2⟩
      one_mem' := ⟨one_pow p, by rw [map_one]; exact Bs.one_mem⟩
      inv_mem' := fun {X} hX => ⟨by rw [inv_pow, hX.1, inv_one], by
        rw [map_inv]; exact Bs.inv_mem hX.2⟩ }
  have hmemA : ∀ X, X ∈ A ↔ X ^ p = 1 ∧ ψ₁ X ∈ Bs := fun X => Iff.rfl
  have hA : MaxElemAb p A :=
    { prime := hp
      ne_two := hp2
      not_dvd := hpq
      pow := fun a ha => ((hmemA a).mp ha).1
      comm := fun a ha b hb => hcomm a b ((hmemA a).mp ha).1 ((hmemA a).mp ha).2
        ((hmemA b).mp hb).2
      max := fun g hgp hga => by
        refine (hmemA g).mpr ⟨hgp, hmax (ψ₁ g) (Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, ?_⟩)
          (by rw [← map_pow, hgp, map_one])⟩
        refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
        obtain ⟨X, hXp, rfl⟩ := hlift b hb
        rw [← map_mul, ← map_mul, hga X ((hmemA X).mpr ⟨hXp, hb⟩)] }
  have huniq : ∀ X ∈ A, ∀ X' ∈ A, ψ₁ X = ψ₁ X' → X = X' := by
    intro X hX X' hX' hXX'
    have hz : ψ₁ (X⁻¹ * X') = 1 := by rw [map_mul, map_inv, hXX', inv_mul_cancel]
    have hzp : (X⁻¹ * X') ^ p = 1 := hA.pow _ (A.mul_mem (A.inv_mem hX) hX')
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · apply Subtype.ext
      apply Units.ext
      ext x
      exact isEmptyElim x
    · obtain ⟨c, hc⟩ := hFk _ hz
      exact inv_mul_eq_one.mp (SUNS.eq_one_of_scalar_mem h hp hpq i hc hzp)
  obtain ⟨F, hFm⟩ := hmove f n K h p A hA
  have hιA : ∀ s, F.ι s ∈ A := fun s => by
    have h1 : F.ι s ∈ F.ι.range := ⟨s, rfl⟩
    rwa [F.ι_range] at h1
  have hBsι : (ψ₁.comp F.ι).range = Bs := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ((hmemA _).mp (hιA s)).2
    · intro hz
      obtain ⟨X, hXp, hXz⟩ := hlift z hz
      have hX : X ∈ F.ι.range := by
        rw [F.ι_range]
        exact (hmemA X).mpr ⟨hXp, hXz ▸ hz⟩
      obtain ⟨s, hs⟩ := hX
      exact ⟨s, by rw [MonoidHom.comp_apply, hs, hXz]⟩
  have hinj : Function.Injective (ψ₁.comp F.ι) := fun s s' hss' =>
    F.ι_injective (huniq _ (hιA s) _ (hιA s') hss')
  have hr : 4 ≤ F.r := by
    have hcardι : Nat.card (ψ₁.comp F.ι).range = p ^ F.r := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card (α := Fin F.r), Fintype.card_fin]
    rw [hBsι] at hcardι
    rw [hcardι] at hcard4
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard4
  refine ⟨F.r, ψ₁.comp F.ι, hinj, hBsι, fun π η hη hprod => ?_, ?_, ?_⟩
  ·
    obtain ⟨w, hw⟩ := hFm π η hη hprod
    have hw' : ∀ s : Fin F.r → ZMod p, (ψ₁ w)⁻¹ * (ψ₁.comp F.ι) (ofAdd s) * ψ₁ w =
        (ψ₁.comp F.ι) (ofAdd fun i => (η i : ZMod p) * s (π i)) := fun s => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hw s, map_mul, map_mul, map_inv]
    refine ⟨ψ₁ w, Subgroup.mem_inf.mpr ⟨⟨w, rfl⟩, ?_⟩, hw'⟩
    rw [← hBsι]
    exact CoordSL.mem_normalizer_range_of_conj π η hw'
  ·
    intro b L₁ _ _ hL₁ hcard β hβ
    rw [← hβ] at hL₁
    rw [← hBsι] at hcard
    exact hcomp G f n K h p A hA F hFm hr ψ₁ hFk L₁ β hL₁ hcard
  ·
    intro E J hE hJ hJc
    rw [← hBsι] at hE hJc
    exact hshape G f n K h p A hA F hFm hr ψ₁ hFk E J hE hJ hJc

theorem ggStepTwoCoordModelOn_PSU_of_piece
    (hmove : GGSUPieceMoveInput) (hcomp : GGSUPieceCompInput) (hshape : GGSUPieceShapeInput) :
    GGStepTwoCoordModelOn .PSU :=
  ggStepTwoCoordModelOn_PSU_of_coord (ggSUNsCoordInput_of_piece hmove hcomp hshape)

end CFSG.StandardType
