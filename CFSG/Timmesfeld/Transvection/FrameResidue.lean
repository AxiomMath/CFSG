module

public import CFSG.Timmesfeld.Transvection.FrameExists

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

@[expose] def frameResidue (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H)
    (k : Fin r) : Set (Subgroup H) :=
  {X | X ∈ Δ ∧ ∀ i, i ≠ k → Commuting X (P i) ∧ Commuting X (Q i)}

@[expose] def residueGroup (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H)
    (k : Fin r) : Subgroup H :=
  ⨆ X ∈ frameResidue Δ P Q k, X

variable {r : ℕ} {P Q : Fin r → Subgroup H} {k : Fin r}

theorem IsFrame.memP_frameResidue (hF : IsFrame Δ P Q) (k : Fin r) :
    P k ∈ frameResidue Δ P Q k :=
  ⟨hF.memP k, fun i hi => ⟨(hF.commuting k i (Ne.symm hi)).mono le_sup_left le_sup_left,
    (hF.commuting k i (Ne.symm hi)).mono le_sup_left le_sup_right⟩⟩

theorem IsFrame.memQ_frameResidue (hF : IsFrame Δ P Q) (k : Fin r) :
    Q k ∈ frameResidue Δ P Q k :=
  ⟨hF.memQ k, fun i hi => ⟨(hF.commuting k i (Ne.symm hi)).mono le_sup_right le_sup_left,
    (hF.commuting k i (Ne.symm hi)).mono le_sup_right le_sup_right⟩⟩

theorem isSmallFrame_iff (hF : IsFrame Δ P Q) :
    IsSmallFrame Δ P Q k ↔ ∀ X ∈ frameResidue Δ P Q k, X ≤ P k ⊔ Q k :=
  ⟨fun h X hX => h.residue X hX.1 hX.2, fun h => ⟨hF, fun X hX hc => h X ⟨hX, hc⟩⟩⟩

theorem IsMaxFrame.opposite_of_mem_frameResidue (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {X Y : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) (hY : Y ∈ frameResidue Δ P Q k) (hXY : X ≠ Y) :
    Opposite X Y :=
  hF.opposite_of_mem_residue hΔ hML k hX.1 hY.1 hX.2 hY.2 hXY

theorem commuting_residueGroup {i : Fin r} (hi : i ≠ k) :
    Commuting (residueGroup Δ P Q k) (P i ⊔ Q i) := by
  refine Commuting.symm (commuting_iff_le_centralizer.2 (iSup₂_le fun X hX => ?_))
  exact commuting_iff_le_centralizer.1 ((hX.2 i hi).1.sup_right (hX.2 i hi).2).symm

theorem conjSub_mem_frameResidue (hΔ : IsTransvectionClass Δ) {X : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) {g : H} (hg : g ∈ residueGroup Δ P Q k) :
    conjSub X g ∈ frameResidue Δ P Q k := by
  refine ⟨hΔ.root.conjSub_mem hX.1 g, fun i hi => ?_⟩
  have hc := commuting_residueGroup (Δ := Δ) (P := P) (Q := Q) hi
  have hfix : ∀ {B : Subgroup H}, B ≤ P i ⊔ Q i → conjSub B g = B := fun hB =>
    conjSub_eq_self_iff.2 (Subgroup.centralizer_le_normalizer _
      (commuting_iff_le_centralizer.1 (hc.mono le_rfl hB).symm hg))
  refine ⟨?_, ?_⟩
  · simpa only [hfix le_sup_left] using (hX.2 i hi).1.conjSub g
  · simpa only [hfix le_sup_right] using (hX.2 i hi).2.conjSub g

end CFSG.Timmesfeld.Transvection
