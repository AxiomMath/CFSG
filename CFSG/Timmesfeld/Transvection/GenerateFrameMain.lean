module

public import CFSG.Timmesfeld.Transvection.GenerateFrameRel
public import CFSG.Timmesfeld.Transvection.GenerateFrameB5
public import CFSG.Timmesfeld.Transvection.RankTwoRelMain

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
  CFSG.LieType.BorelTits

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

private theorem exists_units_ne_one {f : ℕ} (hf : 2 ≤ f) : ∃ μ : (GaloisField 2 f)ˣ, μ ≠ 1 := by
  by_contra! h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ 2 ^ f := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Subsingleton (GaloisField 2 f)ˣ := ⟨fun a b => (h a).trans (h b).symm⟩
  have hunits := Nat.card_units (α := GaloisField 2 f)
  rw [Nat.card_of_subsingleton (1 : (GaloisField 2 f)ˣ)] at hunits
  omega

namespace IsMaxFrame

variable [Finite H] {r : ℕ} {P Q : Fin r → Subgroup H}

private theorem exists_spRelations_of_aligned [Finite H]
    (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hiso : NoIsolated Δ) (hml : MeetsLines Δ) (hthick : ThickLines Δ)
    (hq : ∀ l, 4 ≤ Nat.card (P l)) {f : ℕ} (φ : ∀ l, SL2Coords (P l) (Q l) f)
    {μ : (GaloisField 2 f)ˣ} (hμ1 : μ ≠ 1) {o o₁ : Fin r}
    (hal : ∀ i j : Fin r, i < j → (φ i).Aligned Δ (φ j))
    (hcardX : ∀ i j : Fin r, i < j →
      Nat.card (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) =
        Nat.card (shortRootGroup Δ (Q o) (P o) (P o₁) (Q o₁)))
    (hne : 2 ^ f ≠ (2 ^ f) ^ 2)
    (hd : Nat.card (shortRootGroup Δ (Q o) (P o) (P o₁) (Q o₁)) = 2 ^ f) :
    ∃ R : SpRelations r (GaloisField 2 f) H, R.HasFrameImages Δ P Q := by
  have hsp : ∀ i j : Fin r, i < j → ∃ β : GaloisField 2 f → H,
      PairRelations (RingEquiv.refl _) (RingHom.id _) Δ (P i) (Q i) (P j) (Q j)
        (fun t => (φ i).elt (lowerElt _ t)) (fun t => (φ j).elt (lowerElt _ t))
        ((φ i).elt (weylElt _)) ((φ j).elt (weylElt _)) (φ i).torusElt (φ j).torusElt β := by
    intro i j h
    rcases (hfr.toIsFrame.toPairFrame h.ne).exists_pairRelations hΔ hpts hml hthick (hq i)
      (φ i) (φ j) (hal i j h) with ⟨-, hβ⟩ | ⟨hc, -⟩
    · exact hβ
    · exact absurd (hc.symm.trans ((hcardX i j h).trans hd)) (Ne.symm hne)
  let β : Fin r → Fin r → GaloisField 2 f → H := fun i j =>
    if h : i < j then (hsp i j h).choose else fun _ => 1
  refine hfr.exists_spRelations_hasFrameImages hΔ hiso hpts hml hq φ hμ1 (β := β)
    fun i j h => ?_
  have : β i j = (hsp i j h).choose := dite_eq_left h
  rw [this]
  exact (hsp i j h).choose_spec

private theorem exists_suRelations_of_aligned [Finite H]
    (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hiso : NoIsolated Δ) (hml : MeetsLines Δ) (hthick : ThickLines Δ)
    (hq : ∀ l, 4 ≤ Nat.card (P l)) {f : ℕ} (hf : 2 ≤ f)
    (φ : ∀ l, SL2Coords (P l) (Q l) f) {μ : (GaloisField 2 f)ˣ} (hμ1 : μ ≠ 1)
    {o o₁ : Fin r} (hal : ∀ i j : Fin r, i < j → (φ i).Aligned Δ (φ j))
    (hcardX : ∀ i j : Fin r, i < j →
      Nat.card (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) =
        Nat.card (shortRootGroup Δ (Q o) (P o) (P o₁) (Q o₁)))
    (hd : ¬ Nat.card (shortRootGroup Δ (Q o) (P o) (P o₁) (Q o₁)) = 2 ^ f)
    {ι : GaloisField 2 f →+* GaloisField 2 (2 * f)}
    (hι : ∀ z, unitaryInvolution (GaloisField 2 (2 * f)) 2 f z = z ↔ ∃ c, ι c = z) :
    ∃ R : SURelations r (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) H,
      R.HasFrameImages Δ P Q := by
  have hsu : ∀ i j : Fin r, i < j → ∃ β : GaloisField 2 (2 * f) → H,
      PairRelations (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) ι Δ (P i) (Q i) (P j) (Q j)
        (fun t => (φ i).elt (lowerElt _ t)) (fun t => (φ j).elt (lowerElt _ t))
        ((φ i).elt (weylElt _)) ((φ j).elt (weylElt _)) (φ i).torusElt (φ j).torusElt β := by
    intro i j h
    rcases (hfr.toIsFrame.toPairFrame h.ne).exists_pairRelations hΔ hpts hml hthick (hq i)
      (φ i) (φ j) (hal i j h) with ⟨hc, -⟩ | ⟨-, hβ⟩
    · exact absurd (hc.symm.trans (hcardX i j h)).symm hd
    · exact hβ ι hι
  let β : Fin r → Fin r → GaloisField 2 (2 * f) → H := fun i j =>
    if h : i < j then (hsu i j h).choose else fun _ => 1
  have hF2 := card_galoisField_two_mul (by omega : 1 ≤ f)
  refine hfr.exists_suRelations_hasFrameImages hΔ hiso hpts hml hq φ hμ1
    (unitaryInvolution_involutive hF2) (exists_unitaryInvolution_ne hF2) hι (β := β)
    fun i j h => ?_
  have : β i j = (hsu i j h).choose := dite_eq_left h
  rw [this]
  exact (hsu i j h).choose_spec

theorem exists_relations_hasFrameImages (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hiso : NoIsolated Δ) (hml : MeetsLines Δ) (hthick : ThickLines Δ) {f : ℕ} (hf : 2 ≤ f)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ f) (hr : 2 ≤ r)
    (hfr : IsMaxFrame Δ P Q) :
    (∃ R : SpRelations r (GaloisField 2 f) H, R.HasFrameImages Δ P Q) ∨
      ∃ R : SURelations r (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) H,
        R.HasFrameImages Δ P Q := by
  classical
  have hF := hfr.toIsFrame
  have h4 : 4 ≤ 2 ^ f := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq : ∀ l, 4 ≤ Nat.card (P l) := fun l => (hcard _ (hF.memP l)).symm ▸ h4
  let φ₀ : ∀ l, SL2Coords (P l) (Q l) f := fun l => (nonempty_sl2Coords hΔ.root (hF.memP l)
    (hF.memQ l) (hF.opposite l).symm (hcard _ (hF.memP l))).some
  let o : Fin r := ⟨0, by omega⟩
  have hτ : ∀ l, l ≠ o → ∃ τ : GaloisField 2 f ≃+* GaloisField 2 f,
      (φ₀ o).Aligned Δ ((φ₀ l).map τ) := fun l hl =>
    (hF.toPairFrame (Ne.symm hl)).exists_aligned_of_meetsLines hΔ hpts hml hthick (hq o)
      (φ₀ o) (φ₀ l)
  let φ : ∀ l, SL2Coords (P l) (Q l) f := fun l =>
    if hl : l = o then φ₀ l else (φ₀ l).map (hτ l hl).choose
  have hφo : φ o = φ₀ o := dite_eq_left rfl
  have hal0 : ∀ l, l ≠ o → (φ o).Aligned Δ (φ l) := fun l hl => by
    rw [hφo]
    have : φ l = (φ₀ l).map (hτ l hl).choose := dite_eq_right hl
    rw [this]
    exact (hτ l hl).choose_spec
  obtain ⟨μ, hμ1⟩ := exists_units_ne_one hf
  have hal : ∀ i j : Fin r, i < j → (φ i).Aligned Δ (φ j) := by
    intro i j hij
    have hjo : j ≠ o := fun h => by
      rw [h] at hij
      exact absurd (Fin.lt_def.1 hij) (Nat.not_lt_zero _)
    by_cases hio : i = o
    · rw [hio]
      exact hal0 j hjo
    exact hfr.aligned_of_aligned_of_coords hΔ hiso hpts hml hq φ hμ1 (Ne.symm hio) (Ne.symm hjo)
      hij.ne (hal0 i hio) (hal0 j hjo)
      ((hF.toPairFrame (Ne.symm hio)).exists_ne_one_of_thickLines hΔ hpts hml (hq o) hthick)
  let o₁ : Fin r := ⟨1, by omega⟩
  have ho₁ : o < o₁ := Fin.mk_lt_mk.2 Nat.zero_lt_one
  have hcardX : ∀ i j : Fin r, i < j → Nat.card (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) =
      Nat.card (shortRootGroup Δ (Q o) (P o) (P o₁) (Q o₁)) := fun i j h =>
    hfr.card_shortRootGroup_eq hΔ hiso hpts hml hthick hq φ hμ1 h.ne ho₁.ne
  have hne : 2 ^ f ≠ (2 ^ f) ^ 2 := by
    intro h
    have : 2 ^ f * 1 = 2 ^ f * 2 ^ f := by rw [mul_one, ← pow_two]; exact h
    have := Nat.eq_of_mul_eq_mul_left (by positivity) this
    omega
  by_cases hd : Nat.card (shortRootGroup Δ (Q o) (P o) (P o₁) (Q o₁)) = 2 ^ f
  · exact Or.inl (exists_spRelations_of_aligned hfr hΔ hpts hiso hml hthick hq φ hμ1 hal hcardX
      hne hd)
  · obtain ⟨ι, hι⟩ := QuadForm.exists_ringHom_galoisField (by omega : 1 ≤ f)
    exact Or.inr (exists_suRelations_of_aligned hfr hΔ hpts hiso hml hthick hq hf φ hμ1 hal
      hcardX hd hι)

end IsMaxFrame

end CFSG.Timmesfeld.Transvection
