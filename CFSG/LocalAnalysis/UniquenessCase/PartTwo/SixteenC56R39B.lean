module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Norm
public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.LocalAnalysis.WeakClosure81.SixSix
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E3Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_gammaSet_mono {V X : Subgroup G} (hV : IsElemAbelian 2 V) {j n : ℕ}
    (hjn : j ≤ n) (hn : n ≤ rk ↥V) {I : Subgroup G} (hI : I ∈ E3.gammaSet V j X) :
    ∃ I' ∈ E3.gammaSet V n X, I' ≤ I := by
  obtain ⟨hIX, h, hIh, hmI⟩ := hI
  have hVh : IsElemAbelian 2 (conjSubgroup V h) := E3.isElemAbelian_conjSubgroup hV h
  have hIel : IsElemAbelian 2 I := B2F.isElemAbelian_mono hIh hVh
  have hrk : rk ↥(conjSubgroup V h) = rk ↥V := by
    unfold rk
    rw [E3.card_conjSubgroup]
  have hrkI : rk ↥(conjSubgroup V h) = E3.mQuot (conjSubgroup V h) I + rk ↥I :=
    c8_rk_eq_mQuot_add hIh
  have hc : n - j ≤ rk ↥I := by omega
  obtain ⟨I', hI'I, hmI'⟩ := WeakClosure81.exists_le_mQuot_eq hIel hc
  refine ⟨I', ⟨hI'I.trans hIX, h, hI'I.trans hIh, ?_⟩, hI'I⟩
  rw [E3.mQuot_add hI'I hIh, hmI', hmI]
  omega

theorem inCalO2_mono_index {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {j n : ℕ}
    (hjn : j ≤ n) (hn : n ≤ rk ↥V) {g : G} (h : InCalO2 j M V₀ V g) : InCalO2 n M V₀ V g := by
  obtain ⟨⟨⟨hO1, hO2, hO3⟩, ⟨hD1, hD2, hD3⟩⟩, hT1, hT2, hnp⟩ := h
  have hrk : rk ↥(conjSubgroup V g) = rk ↥V := by
    unfold rk
    rw [E3.card_conjSubgroup]
  refine ⟨⟨⟨hO1, hO2.trans hjn, hO3⟩, ⟨hD1, hD2.trans hjn, hD3⟩⟩, ?_, ?_, hnp⟩
  · obtain ⟨I, hI, hne⟩ := hT1
    obtain ⟨I', hI', hI'I⟩ := exists_gammaSet_mono hV hjn hn hI
    exact ⟨I', hI', fun hle =>
      hne ((inf_le_inf_left _ (Subgroup.centralizer_le hI'I)).trans hle)⟩
  · obtain ⟨I, hI, hne⟩ := hT2
    obtain ⟨I', hI', hI'I⟩ := exists_gammaSet_mono (E3.isElemAbelian_conjSubgroup hV g) hjn
      (hrk ▸ hn) hI
    exact ⟨I', hI', fun hle =>
      hne ((inf_le_inf_left _ (Subgroup.centralizer_le hI'I)).trans hle)⟩

theorem calO2_mono_index {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {j n : ℕ}
    (hjn : j ≤ n) (hn : n ≤ rk ↥V) : calO2 j M V₀ V ⊆ calO2 n M V₀ V := by
  rintro X ⟨g, rfl, h⟩
  exact ⟨g, rfl, inCalO2_mono_index hV hjn hn h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
