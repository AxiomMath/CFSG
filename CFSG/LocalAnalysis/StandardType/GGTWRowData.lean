module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHL
public import CFSG.LocalAnalysis.StandardType.GGHLAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggTWR_ggTorM_A {n rank : ℕ} :
    ggTorM (⟨.A, rank, n⟩ : LargeEvenLabel) = 2 ^ n - 1 := by
  have htag : (⟨.A, rank, n⟩ : LargeEvenLabel).tag = .A := rfl
  unfold ggTorM
  rw [htag]
  rw [if_neg (by decide : ¬ ((.A : LargeEvenLieTag) = .twA ∨
    (.A : LargeEvenLieTag) = .twE6))]

lemma ggTWR_ggTorM_twA {n rank : ℕ} :
    ggTorM (⟨.twA, rank, n⟩ : LargeEvenLabel) = 2 ^ n + 1 := by
  have htag : (⟨.twA, rank, n⟩ : LargeEvenLabel).tag = .twA := rfl
  unfold ggTorM
  rw [htag]
  rw [if_pos (by decide : ((.twA : LargeEvenLieTag) = .twA ∨
    (.twA : LargeEvenLieTag) = .twE6))]

theorem ggTWR_iso_eq {lab labX : LargeEvenLabel} (hiso : GGLabelIso lab labX)
    (htag : labX.tag = .A ∨ labX.tag = .twA) (hrank : 4 ≤ labX.rank) : lab = labX := by
  rcases hiso with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · rcases htag with hA | hA
    · rw [hA] at h2; exact absurd h2 (by decide)
    · rw [hA] at h2; exact absurd h2 (by decide)
  · rw [h2] at hrank
    have h0 : (⟨.A, 3, lab.n⟩ : LargeEvenLabel).rank = 3 := rfl
    rw [h0] at hrank; omega
  · rw [h2] at htag
    have h0 : (⟨.D, 3, lab.n⟩ : LargeEvenLabel).tag = .D := rfl
    rw [h0] at htag
    rcases htag with hA | hA <;> exact absurd hA (by decide)
  · rw [h2] at hrank
    have h0 : (⟨.twA, 3, lab.n⟩ : LargeEvenLabel).rank = 3 := rfl
    rw [h0] at hrank; omega
  · rw [h2] at htag
    have h0 : (⟨.twD, 3, lab.n⟩ : LargeEvenLabel).tag = .twD := rfl
    rw [h0] at htag
    rcases htag with hA | hA <;> exact absurd hA (by decide)
  · rw [h2] at hrank
    have h0 : (⟨.A, 1, 2 * lab.n⟩ : LargeEvenLabel).rank = 1 := rfl
    rw [h0] at hrank; omega
  · rw [h1] at hrank
    have h0 : (⟨.twD, 2, labX.n⟩ : LargeEvenLabel).rank = 2 := rfl
    rw [h0] at hrank; omega

theorem ggTWR_iso_eq_fst {lab labX : LargeEvenLabel} (hiso : GGLabelIso lab labX)
    (htag : lab.tag = .A ∨ lab.tag = .twA) (hrank : 4 ≤ labX.rank) : lab = labX := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · rcases htag with ht | ht
    · rw [ht] at h; simp at h
    · rw [ht] at h; simp at h
  · rw [h.2] at hrank; simp at hrank
  · rw [h.2] at hrank; simp at hrank
  · rw [h.2] at hrank; simp at hrank
  · rw [h.2] at hrank; simp at hrank
  · rw [h.2] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank

theorem ggTWR_iso_eq_fst' {lab labX : LargeEvenLabel} (hiso : GGLabelIso lab labX)
    (htag : lab.tag = .A ∨ lab.tag = .twA) (hrank : 4 ≤ lab.rank) : lab = labX := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · rcases htag with ht | ht
    · rw [ht] at h; simp at h
    · rw [ht] at h; simp at h
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.2] at hrank; simp at hrank

theorem ggTWR_iso_eq_D4 {lab labX : LargeEvenLabel} (hiso : GGLabelIso lab labX)
    (hlab : lab = ⟨.D, 4, lab.n⟩) : lab = labX := by
  have hlt : lab.tag = .D := by simpa using congrArg LargeEvenLabel.tag hlab
  have hlr : lab.rank = 4 := by simpa using congrArg LargeEvenLabel.rank hlab
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · rcases h.1 with hb | hc
    · rw [hlt] at hb; exact absurd hb (by decide)
    · rw [hlt] at hc; exact absurd hc (by decide)
  · have h3 : lab.rank = 3 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : lab.tag = .A := by simpa using congrArg LargeEvenLabel.tag h.1
    rw [hlt] at ht; exact absurd ht (by decide)
  · have h3 : lab.rank = 3 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : lab.tag = .twA := by simpa using congrArg LargeEvenLabel.tag h.1
    rw [hlt] at ht; exact absurd ht (by decide)
  · have h2 : lab.rank = 2 := by simpa using congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : lab.tag = .A := by simpa using congrArg LargeEvenLabel.tag h.2
    rw [hlt] at ht; exact absurd ht (by decide)

end CFSG.StandardType
