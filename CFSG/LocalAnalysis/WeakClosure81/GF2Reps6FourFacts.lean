module

public import Mathlib.GroupTheory.OrderOfElement
import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

@[expose] def commY {X : Type*} [Group X] (B : Subgroup (MulAut X)) (β : MulAut X) :
    Subgroup X :=
  Subgroup.closure {w | ∃ y : X, β y = y ∧ ∃ b ∈ B, w = y * (b y)⁻¹}

@[expose] def FourGen {X : Type*} [Group X] (B : Subgroup (MulAut X)) (β : MulAut X) (x : X) :
    Prop :=
  ∃ k : X, MulAut.conj k * β * (MulAut.conj k)⁻¹ =
      β * (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) ^
        (orderOf (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) / 2) ∧
    commY B β ⊔ (commY B β).map (MulAut.conj k).toMonoidHom = ⊤

@[expose] def FourFacts (X : Type*) [Group X] : Prop :=
  ∀ B : Subgroup (MulAut X), Nat.card B = 4 → (∀ b ∈ B, b * b = 1) →
    ¬ B ≤ (MulAut.conj : X →* MulAut X).range →
    ∃ β ∈ B, ∃ x : X,
      Even (orderOf (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹))) ∧
      4 ≤ orderOf (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) ∧
      FourGen B β x ∧ FourGen B β x⁻¹

theorem commY_map {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (B : Subgroup (MulAut X)) (β : MulAut X) :
    commY (B.map (MulAut.congr e).toMonoidHom) (MulAut.congr e β) =
      (commY B β).map e.toMonoidHom := by
  set E : MulAut X ≃* MulAut X' := MulAut.congr e
  have hE : ∀ (σ : MulAut X) (y : X), E σ (e y) = e (σ y) := by
    intro σ y
    simp [E, MulAut.congr_apply]
  have hgen : e.toMonoidHom '' {w : X | ∃ y : X, β y = y ∧ ∃ b ∈ B, w = y * (b y)⁻¹} =
      {w : X' | ∃ y : X', E β y = y ∧
        ∃ b ∈ B.map E.toMonoidHom, w = y * (b y)⁻¹} := by
    ext w
    constructor
    · rintro ⟨w₀, ⟨y, hy, b, hb, rfl⟩, rfl⟩
      refine ⟨e y, ?_, E b, ⟨b, hb, rfl⟩, ?_⟩
      · rw [hE β y, hy]
      · simp [map_mul, map_inv, hE b y]
    · rintro ⟨y', hy', b', hb', rfl⟩
      rw [Subgroup.mem_map] at hb'
      obtain ⟨b, hb, rfl⟩ := hb'
      refine ⟨e.symm y' * (b (e.symm y'))⁻¹, ⟨e.symm y', ?_, b, hb, rfl⟩, ?_⟩
      · apply e.injective
        rw [← hE β (e.symm y'), e.apply_symm_apply, hy']
      · rw [map_mul, map_inv]
        change e (e.symm y') * (e (b (e.symm y')))⁻¹ = y' * (E b y')⁻¹
        rw [e.apply_symm_apply, ← hE b (e.symm y'), e.apply_symm_apply]
  unfold commY
  rw [MonoidHom.map_closure, hgen]

@[expose] def FourGenWith {X : Type*} [Group X] (H : Subgroup X) (β : MulAut X) (x : X) : Prop :=
  ∃ k : X, MulAut.conj k * β * (MulAut.conj k)⁻¹ =
      β * (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) ^
        (orderOf (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) / 2) ∧
    H ⊔ H.map (MulAut.conj k).toMonoidHom = ⊤

private lemma map_conj_map {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (H : Subgroup X)
    (k : X) :
    ((H.map (MulAut.conj k).toMonoidHom).map e.toMonoidHom) =
      ((H.map e.toMonoidHom).map (MulAut.conj (e k)).toMonoidHom) := by
  rw [← CFSG.map_mulAut_congr e (MulAut.conj k) H, CFSG.mulAut_congr_conj e k]

theorem FourGenWith.map {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') {H : Subgroup X}
    {β : MulAut X} {x : X} (h : FourGenWith H β x) :
    FourGenWith (H.map e.toMonoidHom) (MulAut.congr e β) (e x) := by
  let inner : MulAut X := β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)
  let inner' : MulAut X' := MulAut.congr e β *
      (MulAut.conj (e x) * MulAut.congr e β * (MulAut.conj (e x))⁻¹)
  have hEelem : MulAut.congr e inner = inner' := by
    simp [inner, inner', map_mul, map_inv, CFSG.mulAut_congr_conj e x]
  obtain ⟨k, hk, hsup⟩ := h
  have hk' : MulAut.conj k * β * (MulAut.conj k)⁻¹ = β * inner ^ (orderOf inner / 2) :=
    hk
  refine ⟨e k, ?_, ?_⟩
  · have h := congrArg (MulAut.congr e) hk'
    have hleft : MulAut.congr e (MulAut.conj k * β * (MulAut.conj k)⁻¹) =
        MulAut.conj (e k) * MulAut.congr e β * (MulAut.conj (e k))⁻¹ := by
      simp [map_mul, map_inv, CFSG.mulAut_congr_conj e k]
    have hord : orderOf inner = orderOf inner' := by
      rw [← hEelem, MulEquiv.orderOf_eq]
    have hright : MulAut.congr e (β * inner ^ (orderOf inner / 2)) =
        MulAut.congr e β * inner' ^ (orderOf inner' / 2) := by
      rw [map_mul, map_pow, hEelem, hord]
    rw [hleft, hright] at h
    exact h
  · have h := congrArg (fun K : Subgroup X => K.map e.toMonoidHom) hsup
    rw [Subgroup.map_sup, map_conj_map,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h
    exact h

theorem FourGen.map {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    {B : Subgroup (MulAut X)} {β : MulAut X} {x : X} (h : FourGen B β x) :
    FourGen (B.map (MulAut.congr e).toMonoidHom) (MulAut.congr e β) (e x) := by
  have h' := FourGenWith.map e (show FourGenWith (commY B β) β x from h)
  rw [← commY_map] at h'
  exact h'

theorem FourFacts.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : FourFacts X) : FourFacts X' := by
  intro B' hcard' hinv' hnot'
  let E : MulAut X ≃* MulAut X' := MulAut.congr e
  let B : Subgroup (MulAut X) := B'.comap E.toMonoidHom
  have hBmap : B.map E.toMonoidHom = B' :=
    Subgroup.map_comap_eq_self_of_surjective E.surjective B'
  have hcard : Nat.card B = 4 := by
    have hc := Subgroup.card_map_of_injective (K := B) (f := E.toMonoidHom) E.injective
    rw [hBmap, hcard'] at hc
    exact hc.symm
  have hinv : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    have hb' : E b ∈ B' := hb
    apply E.injective
    rw [map_mul, map_one]
    exact hinv' (E b) hb'
  have hmaprange : (MulAut.conj : X →* MulAut X).range.map E.toMonoidHom =
      (MulAut.conj : X' →* MulAut X').range := by
    have hcomp : E.toMonoidHom.comp (MulAut.conj : X →* MulAut X) =
        (MulAut.conj : X' →* MulAut X').comp e.toMonoidHom :=
      MonoidHom.ext fun x => CFSG.mulAut_congr_conj e x
    calc (MulAut.conj : X →* MulAut X).range.map E.toMonoidHom
        = ((⊤ : Subgroup X).map (MulAut.conj : X →* MulAut X)).map
            E.toMonoidHom := by
          rw [MonoidHom.range_eq_map]
      _ = (⊤ : Subgroup X).map
            (E.toMonoidHom.comp (MulAut.conj : X →* MulAut X)) := by
          rw [Subgroup.map_map]
      _ = (⊤ : Subgroup X).map
            ((MulAut.conj : X' →* MulAut X').comp e.toMonoidHom) := by
          rw [hcomp]
      _ = ((⊤ : Subgroup X).map e.toMonoidHom).map
            (MulAut.conj : X' →* MulAut X') := by
          rw [Subgroup.map_map]
      _ = (⊤ : Subgroup X').map (MulAut.conj : X' →* MulAut X') := by
          rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      _ = (MulAut.conj : X' →* MulAut X').range := by
          rw [MonoidHom.range_eq_map]
  have hnot : ¬ B ≤ (MulAut.conj : X →* MulAut X).range := by
    intro hB
    have hle : B.map E.toMonoidHom ≤ (MulAut.conj : X' →* MulAut X').range := by
      calc B.map E.toMonoidHom ≤
            (MulAut.conj : X →* MulAut X).range.map E.toMonoidHom :=
            Subgroup.map_mono hB
        _ = (MulAut.conj : X' →* MulAut X').range := hmaprange
    exact hnot' (by rwa [hBmap] at hle)
  obtain ⟨β, hβ, x, heven, h4, hgen, hgeninv⟩ := h B hcard hinv hnot
  have hEelem : E (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) =
      E β * (MulAut.conj (e x) * E β * (MulAut.conj (e x))⁻¹) := by
    simp [E, map_mul, map_inv, CFSG.mulAut_congr_conj e x]
  refine ⟨E β, ?_, e x, ?_, ?_, ?_, ?_⟩
  · rw [← hBmap]
    exact Subgroup.mem_map_of_mem E.toMonoidHom hβ
  · rw [← hEelem, MulEquiv.orderOf_eq]
    exact heven
  · rw [← hEelem, MulEquiv.orderOf_eq]
    exact h4
  · have hgen' : FourGen (B.map (MulAut.congr e).toMonoidHom) (MulAut.congr e β) (e x) :=
      FourGen.map e hgen
    rw [hBmap] at hgen'
    exact hgen'
  · have hgen' : FourGen (B.map (MulAut.congr e).toMonoidHom) (MulAut.congr e β)
        (e (x⁻¹)) := FourGen.map e hgeninv
    rw [hBmap, map_inv] at hgen'
    exact hgen'

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
