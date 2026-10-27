module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGK1ScMain
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacV2
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableCl
public import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem cgen_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

private theorem cgen_not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
  have hge : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at *

private theorem cgen_dvd_sq_sub_one {p n : ℕ} (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    p ∣ 2 ^ (2 * n) - 1 := by
  have hfac : (2:ℕ) ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h1 : (2:ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    rw [h1]
    have h3 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [h3]
    ring
  rw [hfac]
  rcases h with h | h
  · exact dvd_mul_of_dvd_left h _
  · exact dvd_mul_of_dvd_right h _

theorem cgen_dvd_sub_or_add_of_dvd_sq_sub_one {p n : ℕ} (hp : p.Prime)
    (h : p ∣ 2 ^ (2 * n) - 1) : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
  have hfac : (2:ℕ) ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h1 : (2:ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    rw [h1]
    have h3 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [h3]
    ring
  rw [hfac] at h
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem cgen_dvd_of_halfSplit_A1 {p m : ℕ} {c : Prop} (hm : 2 ≤ m)
    (h : LargeEvenHalfSplit p ⟨.A, 1, m⟩ c) : p ∣ 2 ^ m - 1 := by
  unfold LargeEvenHalfSplit LargeEvenSplit LargeEvenUntwisted at h
  rcases h with h | h | h | h | h | h
  · rcases h with ⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd hu (by simp)
    · exact absurd ht (by simp)
    · dsimp only at h1
      exact absurd h1 (by omega)
  · obtain ⟨ht, -⟩ := h; exact absurd ht (by simp)
  · obtain ⟨ht, -⟩ := h; exact absurd ht (by simp)
  · obtain ⟨-, hr, -, -, -⟩ := h; simp at hr
  · obtain ⟨-, hr, -, -⟩ := h; simp at hr
  · obtain ⟨ht, -⟩ := h; exact absurd ht (by simp)

private theorem cgen_dvd_of_halfSplit_twD2 {p n : ℕ} {c : Prop}
    (h : LargeEvenHalfSplit p ⟨.twD, 2, n⟩ c) : p ∣ 2 ^ (2 * n) - 1 := by
  unfold LargeEvenHalfSplit LargeEvenSplit LargeEvenUntwisted at h
  rcases h with h | h | h | h | h | h
  · rcases h with ⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, h⟩ | ⟨h1, h2⟩
    · exact absurd hu (by simp)
    · exact cgen_dvd_sq_sub_one (Or.inr h)
    · exact cgen_dvd_sq_sub_one (Or.inl h)
    · dsimp only at h1; rw [h1, h2]; norm_num
  · obtain ⟨ht, -⟩ := h; exact absurd ht (by simp)
  · obtain ⟨ht, -⟩ := h; exact absurd ht (by simp)
  · obtain ⟨-, hr, -, -, -⟩ := h; simp at hr
  · obtain ⟨-, hr, -, -⟩ := h; simp at hr
  · obtain ⟨ht, -⟩ := h; exact absurd ht (by simp)

theorem cgen_dvd_two_pow_of_halfSplit_iso_A1 {p m : ℕ} {c : Prop} {labm : LargeEvenLabel}
    (hΛm : LargeEvenInLambda2 labm) (hhalf : LargeEvenHalfSplit p labm c)
    (hiso : GGLabelIso labm ⟨.A, 1, m⟩) : p ∣ 2 ^ m - 1 := by
  obtain ⟨t, r, s⟩ := labm
  rcases hiso with h | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · obtain ⟨rfl, rfl, hm⟩ := LargeEvenLabel.mk.injEq .. |>.mp h
    subst hm
    exact cgen_dvd_of_halfSplit_A1 (hΛm.2.2 rfl) hhalf
  · obtain ⟨-, hb, -⟩ := hBC; simp at hb
  · obtain ⟨-, h2⟩ := hDA; simp at h2
  · obtain ⟨-, h2⟩ := hAD; simp at h2
  · obtain ⟨-, h2⟩ := hD3A3; simp at h2
  · obtain ⟨-, h2⟩ := hA3D3; simp at h2
  · obtain ⟨h1, h2⟩ := hD2A1
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    obtain ⟨-, -, hm⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    rw [hm]
    exact cgen_dvd_of_halfSplit_twD2 hhalf
  · obtain ⟨h1, -⟩ := hA1D2; simp at h1

theorem cgen_genericCl_of_ggLabelIso {a b : LargeEvenLabel} {p : ℕ}
    (hΛa : LargeEvenInLambda2 a) (h : GGLabelIso a b) (hb : GGKacGenericCl b p)
    (hfix : a = ⟨.twD, 2, a.n⟩ → b = ⟨.A, 1, 2 * a.n⟩ →
      p ∣ 2 ^ a.n - 1 ∨ p ∣ 2 ^ a.n + 1) :
    GGKacGenericCl a p := by
  obtain ⟨hp, hp2, hdvd, htag, hnotA, hnottwA⟩ := hb
  obtain ⟨t, l, n⟩ := a
  obtain ⟨t', l', n'⟩ := b
  rcases h with h | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · cases h
    exact ⟨hp, hp2, hdvd, htag, hnotA, hnottwA⟩
  · obtain ⟨ha, hb', hr, hn⟩ := hBC
    dsimp only at ha hb' hr hn
    refine ⟨hp, hp2, ?_, ?_, ?_, ?_⟩
    · rw [hn]; exact hdvd
    · rcases ha with ha | ha <;> simp [ha]
    · rintro ⟨hA, -⟩; rcases ha with ha | ha <;> rw [ha] at hA <;> simp at hA
    · rintro ⟨hA, -⟩; rcases ha with ha | ha <;> rw [ha] at hA <;> simp at hA
  · obtain ⟨h1, h2⟩ := hDA
    dsimp only at h1 h2
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    obtain ⟨rfl, rfl, hn2⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    subst hn2
    exact ⟨hp, hp2, hdvd, by simp, by rintro ⟨hA, -⟩; simp at hA,
      by rintro ⟨hA, -⟩; simp at hA⟩
  · obtain ⟨h1, h2⟩ := hAD
    dsimp only at h1 h2
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    obtain ⟨rfl, rfl, hn2⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    subst hn2
    exact ⟨hp, hp2, hdvd, by simp, by rintro ⟨-, hd, -⟩; exact cgen_not_dvd_four hp hp2 hd,
      by rintro ⟨hA, -⟩; simp at hA⟩
  · obtain ⟨h1, h2⟩ := hD3A3
    dsimp only at h1 h2
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    obtain ⟨rfl, rfl, hn2⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    subst hn2
    exact ⟨hp, hp2, hdvd, by simp, by rintro ⟨hA, -⟩; simp at hA,
      by rintro ⟨hA, -⟩; simp at hA⟩
  · obtain ⟨h1, h2⟩ := hA3D3
    dsimp only at h1 h2
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    obtain ⟨rfl, rfl, hn2⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    subst hn2
    exact ⟨hp, hp2, hdvd, by simp, by rintro ⟨hA, -⟩; simp at hA,
      by rintro ⟨-, hd, -⟩; exact cgen_not_dvd_four hp hp2 hd⟩
  · obtain ⟨h1, h2⟩ := hD2A1
    have hdiv := hfix h1 h2
    dsimp only at h1 h2
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    obtain ⟨rfl, rfl, hn2⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    subst hn2
    exact ⟨hp, hp2, hdiv, by simp, by rintro ⟨hA, -⟩; simp at hA,
      by rintro ⟨hA, -⟩; simp at hA⟩
  · obtain ⟨h1, h2⟩ := hA1D2
    dsimp only at h1 h2
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    obtain ⟨rfl, rfl, hn2⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    subst hn2
    exact ⟨hp, hp2, Or.inl (cgen_dvd_sq_sub_one hdvd), by simp,
      by rintro ⟨-, hd, -⟩; exact cgen_not_dvd_two hp hp2 hd,
      by rintro ⟨hA, -⟩; simp at hA⟩

theorem ggClGenRK_of_regime
    {R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hJ : ∀ p n labJ labX, R p n labJ labX →
      ∀ lab, GGLabelIso lab labJ → ¬ GGTPNPRankOne p lab) : GGClGenRK R := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hR hhJ hhX
  obtain ⟨hRreg, hgen⟩ := hR
  obtain ⟨hloc, hflat, hcard, hrank, hnum, hself, honly, hm⟩ := hd.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hK0 : GGK0MainBS GGKacGenericCl GGMultValidCl := ggK0MainBS_cl
  have hS : GGK0Schur GGKacGenericCl := ggK0Schur_cl
  have hperf : commutator X = ⊤ := by
    have hm0 := hm
    unfold GGTPNMarked at hm0
    exact hm0.1
  have hm' : GGTPNMarked p (fun q lab => ∃ c : Prop, LargeEvenHalfSplit q lab c) A := by
    obtain ⟨hX, lab, hlab, hraw⟩ := hm
    exact ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, h1, h2, h3⟩ => ⟨hs, hna, θ, ⟨_, h2⟩, h2, h3⟩) hraw⟩
  obtain ⟨-, labm, hΛm, hrawm⟩ := hm
  have hmHas : GGHasLabel labm (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hrawm
  obtain ⟨Rm, xm, Im, Fm, hQm⟩ := largeEvenRawDatum_exists hrawm
  obtain ⟨-, -, θm, -, hhalfm, -⟩ := hQm
  have hisom : GGLabelIso labm labX :=
    hrig labm labX (X ⧸ Subgroup.center X) hΛm hΛX hmHas hhX
  have hgen' : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      GGKacGenericCl lab p := by
    intro lab hlab hhas
    have hiso : GGLabelIso lab labX :=
      hrig lab labX (X ⧸ Subgroup.center X) hlab hΛX hhas hhX
    have hfix : lab = ⟨.twD, 2, lab.n⟩ → labX = ⟨.A, 1, 2 * lab.n⟩ →
        p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
      intro _ h2
      exact cgen_dvd_sub_or_add_of_dvd_sq_sub_one hp
        (cgen_dvd_two_pow_of_halfSplit_iso_A1 hΛm hhalfm (h2 ▸ hisom))
    exact cgen_genericCl_of_ggLabelIso hlab hiso hgen hfix
  obtain ⟨lab, hΛlab, hSlab, -, hXlab, D, hD, hrZ, -, o, hDo, hqs, -, hoΛ, hJo⟩ :=
    exists_ggKacDatum_of_ggK0MainBS hK0 hS hloc hself hk honly hm' hgen'
  obtain ⟨c, hc⟩ := hSlab
  have hEq : GGLabelIso o.lab labJ :=
    hrig o.lab labJ (↥J ⧸ Subgroup.center ↥J) hoΛ hΛJ hJo hhJ
  have hrk : ¬ GGTPNPRankOne p o.lab := hJ p n labJ labX hRreg o.lab hEq
  have hXnot : ¬ GGLabelIso o.lab lab := by
    intro hiso
    exact not_ggHasLabel_of_le_ggAutFixedSubgroup hperf hloc.2.2.1 hloc.2.2.2.1.1 hXlab
      (largeEvenRawDatum_of_ggLabelIso hiso hJo)
  obtain ⟨-, labJ', labX', hiso1, hiso2, hΛJ', hΛX', hrow⟩ :=
    ggTablePRow_of_ggMultValidCl hΛlab hc hD hrZ hDo hqs hXnot hrk
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    largeEvenRawDatum_of_ggLabelIso hiso1 hJo,
    largeEvenRawDatum_of_ggLabelIso hiso2 hXlab⟩

end CFSG.StandardType

end
