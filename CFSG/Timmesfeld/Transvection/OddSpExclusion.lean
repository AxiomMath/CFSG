module

public import CFSG.Timmesfeld.Transvection.OddCPart
public import CFSG.Timmesfeld.Transvection.OddResidueOrder

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}

section Certificates

theorem IsMaxFrame.card_shortRootGroup_of_not_isSmallFrame (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) (hns : ¬ IsSmallFrame Δ P Q k) :
    Nat.card ↥(shortRootGroup Δ (Q j) (P j) (P k) (Q k)) = Nat.card (P k) ^ 2 := by
  haveI : Finite H := h.finite
  have hline := (hF.toPairFrame hjk).ncard_lineOf h.cls
    (h.cls.noIsolated h.points h.rank) h.points hML (hq (P j) (hF.memP j))
  have hspan := hF.ncard_lineOf_eq_of_mem_rankTwoResidue h hML hq hjk hns
    (hF.toIsFrame.memP_rankTwoResidue_left j k)
    (hF.toIsFrame.memP_rankTwoResidue_right j k)
    (hF.toIsFrame.P_ne hjk) (hF.toIsFrame.commuting_PP hjk)
  omega

theorem IsMaxFrame.card_shortRootGroup_flip_of_not_isSmallFrame (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) (hns : ¬ IsSmallFrame Δ P Q k) :
    Nat.card ↥(shortRootGroup Δ (P j) (Q j) (P k) (Q k)) = Nat.card (P k) ^ 2 := by
  haveI : Finite H := h.finite
  have hline := (hF.toPairFrame hjk).flip.ncard_lineOf h.cls
    (h.cls.noIsolated h.points h.rank) h.points hML (hq (Q j) (hF.memQ j))
  have hspan := hF.ncard_lineOf_eq_of_mem_rankTwoResidue h hML hq hjk hns
    (hF.toIsFrame.memQ_rankTwoResidue_left j k)
    (hF.toIsFrame.memP_rankTwoResidue_right j k)
    (hF.toIsFrame.Q_ne_P hjk) (hF.toIsFrame.commuting_QP hjk)
  omega

theorem IsMaxFrame.sq_card_le_of_spRelations (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k)
    (hns : ¬ IsSmallFrame Δ P Q k) {K : Type} [Field K] [Finite K] {R : SpRelations r K H}
    (hR : R.HasFrameImages Δ P Q) : Nat.card (P k) ^ 2 ≤ Nat.card K := by
  have hsurj : Function.Surjective (fun c : K =>
      (⟨R.ξ (Sum.inr j) (Sum.inl k) c, by
        simpa [framePt] using
          (hR.short (Sum.inr j) (Sum.inl k) (by simpa using hjk)
            (R.ξ (Sum.inr j) (Sum.inl k) c)).2 ⟨c, rfl⟩⟩ :
        ↥(shortRootGroup Δ (Q j) (P j) (P k) (Q k)))) := by
    intro x
    obtain ⟨c, hc⟩ := (hR.short (Sum.inr j) (Sum.inl k) (by simpa using hjk) (x : H)).1
      (by simpa [framePt] using x.2)
    exact ⟨c, Subtype.ext hc⟩
  calc Nat.card (P k) ^ 2
      = Nat.card ↥(shortRootGroup Δ (Q j) (P j) (P k) (Q k)) :=
        (hF.card_shortRootGroup_of_not_isSmallFrame h hML hq hjk hns).symm
    _ ≤ Nat.card K := Nat.card_le_card_of_surjective _ hsurj

theorem IsMaxFrame.exists_suRelations_of_not_isSmallFrame (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hr : 2 ≤ r) (hF : IsMaxFrame Δ P Q)
    {k : Fin r} (hns : ¬ IsSmallFrame Δ P Q k) :
    ∃ f, 2 ≤ f ∧ (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧
      ∃ R : SURelations r (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) H,
        R.HasFrameImages Δ P Q := by
  obtain ⟨f, hf, hcard, hSp | hSU⟩ := hF.exists_cPart h hML hq hr
  · obtain ⟨R, hR⟩ := hSp
    haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
    obtain ⟨j, hjk⟩ := exists_ne k
    have hle := hF.sq_card_le_of_spRelations h hML hq hjk hns hR
    have hqk : Nat.card (P k) = 2 ^ f := hcard (P k) (hF.memP k)
    have hK : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card (p := 2) (n := f) (by omega)
    rw [hqk, hK] at hle
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
    have hmono : 2 ^ f * 4 ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_left _ h4
    have hsquare : 2 ^ f * 2 ^ f ≤ 2 ^ f := by simpa [pow_two] using hle
    have hcontra : 2 ^ f * 4 ≤ 2 ^ f := le_trans hmono hsquare
    have hlt : 2 ^ f < 2 ^ f * 4 := by
      calc 2 ^ f = 2 ^ f * 1 := (Nat.mul_one _).symm
        _ < 2 ^ f * 4 := Nat.mul_lt_mul_of_pos_left (by norm_num) hpos
    exact (not_le_of_gt hlt hcontra).elim
  · exact ⟨f, hf, hcard, hSU⟩

end Certificates

end CFSG.Timmesfeld.Transvection
