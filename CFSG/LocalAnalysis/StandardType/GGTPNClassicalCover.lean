module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def tcl_cov (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGKacGenericCl lab p ∨ GGKacRA lab p ∨ (p = 7 ∧ lab = ⟨.A, 8, 1⟩) ∨
    (p = 5 ∧ lab = ⟨.A, 5, 2⟩)

private theorem tcl_cover_lift {p : ℕ} {lab : LargeEvenLabel}
    (h : GGKacGenericCl lab p ∨ GGKacRA lab p) : tcl_cov p lab :=
  h.elim Or.inl fun hr => Or.inr (Or.inl hr)

private theorem tcl_generic_of_clTag {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hcl : GGTPNClTag lab.tag)
    (hdvd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    (hnotA : lab.tag ≠ .A) (hnotTwA : lab.tag ≠ .twA) :
    GGKacGenericCl lab p :=
  ⟨hp, hp2, hdvd, hcl, (fun h => hnotA h.1), fun h => hnotTwA h.1⟩

private theorem tcl_generic_or_RA_of_tagA {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hA : lab.tag = .A)
    (hdvd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) :
    GGKacGenericCl lab p ∨ GGKacRA lab p := by
  by_cases hsub : p ∣ 2 ^ lab.n - 1
  · by_cases hdiv : p ∣ lab.rank + 1
    · exact Or.inr (Or.inl ⟨hA, hdiv, hsub⟩)
    · refine Or.inl ⟨hp, hp2, Or.inl hsub, Or.inl hA, (fun h => hdiv h.2.1), ?_⟩
      intro h
      rw [hA] at h
      exact nomatch h.1
  · have hadd : p ∣ 2 ^ lab.n + 1 := by
      rcases hdvd with h | h
      · exact absurd h hsub
      · exact h
    refine Or.inl ⟨hp, hp2, Or.inr hadd, Or.inl hA, (fun h => hsub h.2.2), ?_⟩
    intro h
    rw [hA] at h
    exact nomatch h.1

private theorem tcl_generic_or_RA_of_tagTwA {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hA : lab.tag = .twA)
    (hdvd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) :
    GGKacGenericCl lab p ∨ GGKacRA lab p := by
  by_cases hadd : p ∣ 2 ^ lab.n + 1
  · by_cases hdiv : p ∣ lab.rank + 1
    · exact Or.inr (Or.inr ⟨hA, hdiv, hadd⟩)
    · refine Or.inl ⟨hp, hp2, Or.inr hadd, Or.inr (Or.inl hA), ?_,
        (fun h => hdiv h.2.1)⟩
      intro h
      rw [hA] at h
      exact nomatch h.1
  · have hsub : p ∣ 2 ^ lab.n - 1 := by
      rcases hdvd with h | h
      · exact h
      · exact absurd h hadd
    refine Or.inl ⟨hp, hp2, Or.inl hsub, Or.inr (Or.inl hA), ?_,
      (fun h => hadd h.2.2)⟩
    intro h
    rw [hA] at h
    exact nomatch h.1

private theorem tcl_generic_or_RA_of_clTag {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hcl : GGTPNClTag lab.tag)
    (hdvd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) :
    GGKacGenericCl lab p ∨ GGKacRA lab p := by
  rcases hcl with hA | hA | hB | hC | hD | hD
  · exact tcl_generic_or_RA_of_tagA hp hp2 hA hdvd
  · exact tcl_generic_or_RA_of_tagTwA hp hp2 hA hdvd
  · exact Or.inl (tcl_generic_of_clTag hp hp2 (Or.inr (Or.inr (Or.inl hB))) hdvd
      (by intro h; rw [hB] at h; nomatch h) (by intro h; rw [hB] at h; nomatch h))
  · exact Or.inl (tcl_generic_of_clTag hp hp2
      (Or.inr (Or.inr (Or.inr (Or.inl hC)))) hdvd
      (by intro h; rw [hC] at h; nomatch h) (by intro h; rw [hC] at h; nomatch h))
  · exact Or.inl (tcl_generic_of_clTag hp hp2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hD))))) hdvd
      (by intro h; rw [hD] at h; nomatch h) (by intro h; rw [hD] at h; nomatch h))
  · exact Or.inl (tcl_generic_of_clTag hp hp2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hD))))) hdvd
      (by intro h; rw [hD] at h; nomatch h) (by intro h; rw [hD] at h; nomatch h))

private theorem tcl_eq_of_iso_of_exc {lab lab' : LargeEvenLabel}
    (hex : lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩) (h : GGLabelIso lab lab') : lab' = lab := by
  obtain ⟨t', r', n'⟩ := lab'
  rcases hex with rfl | rfl
  · unfold GGLabelIso at h
    rcases h with h | h | h | h | h | h | h | h <;> simp_all
  · unfold GGLabelIso at h
    rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem tcl_cover_of_iso {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab₁ labX : LargeEvenLabel} {c : Prop} (hΛ₁ : LargeEvenInLambda2 lab₁)
    (hcl : GGTPNClTag labX.tag) (hiso : GGLabelIso lab₁ labX)
    (hhalf : LargeEvenHalfSplit p lab₁ c)
    (hdvd₁ : p ∣ 2 ^ lab₁.n - 1 ∨ p ∣ 2 ^ lab₁.n + 1) : tcl_cov p labX := by
  rcases hiso with hEq | hBC | hDA | hAD | h2DA | h2AD | hD2A1 | hA1D2
  ·
    subst hEq
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl hdvd₁)
  ·
    obtain ⟨-, _, -, hn⟩ := hBC
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl
      (by simpa [hn] using hdvd₁))
  ·
    obtain ⟨-, h2lab⟩ := hDA
    have hn : labX.n = lab₁.n := by rw [h2lab]
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl
      (by simpa [hn] using hdvd₁))
  ·
    obtain ⟨-, h2lab⟩ := hAD
    have hn : labX.n = lab₁.n := by rw [h2lab]
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl
      (by simpa [hn] using hdvd₁))
  ·
    obtain ⟨-, h2lab⟩ := h2DA
    have hn : labX.n = lab₁.n := by rw [h2lab]
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl
      (by simpa [hn] using hdvd₁))
  ·
    obtain ⟨-, h2lab⟩ := h2AD
    have hn : labX.n = lab₁.n := by rw [h2lab]
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl
      (by simpa [hn] using hdvd₁))
  ·
    obtain ⟨-, h2lab⟩ := hD2A1
    have hdvdX : p ∣ 2 ^ labX.n - 1 ∨ p ∣ 2 ^ labX.n + 1 := by
      left
      have hfac : 2 ^ (2 * lab₁.n) - 1 = (2 ^ lab₁.n - 1) * (2 ^ lab₁.n + 1) := by
        rw [show 2 * lab₁.n = lab₁.n * 2 by omega, pow_mul, pow_two, mul_self_tsub_one,
          mul_comm]
      rw [h2lab, hfac]
      rcases hdvd₁ with h | h
      · exact dvd_mul_of_dvd_left h _
      · exact dvd_mul_of_dvd_right h _
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl hdvdX)
  ·
    obtain ⟨h2lab, h1lab⟩ := hA1D2
    have hsub : p ∣ 2 ^ (2 * labX.n) - 1 := by
      rcases hhalf with hh | hh | hh | hh | hh | hh
      ·
        rcases hh with hh | hh | hh | hh
        ·
          rw [h1lab] at hh
          exact hh.2
        ·
          exact absurd hh.1 (by rw [h1lab]; simp [LargeEvenUntwisted])
        ·
          rcases hh.1 with h | h
          · rw [h1lab] at h; nomatch h
          · rw [h1lab] at h; nomatch h
        ·
          obtain ⟨hn1, -⟩ := hh
          have hn1' : 2 * labX.n = 1 := by simpa [h1lab] using hn1
          exact absurd hn1' (by omega)
      ·
        rcases hh.1 with h | h | h | h | h <;> (rw [h1lab] at h; nomatch h)
      ·
        rcases hh.1 with h | h
        · rw [h1lab] at h; nomatch h.1
        · rw [h1lab] at h; nomatch h
      ·
        obtain ⟨-, hr, -⟩ := hh
        have hr' : (1 : ℕ) = 5 := by simpa [h1lab] using hr
        exact absurd hr' (by omega)
      ·
        obtain ⟨-, hr, -⟩ := hh
        have hr' : (1 : ℕ) = 8 := by simpa [h1lab] using hr
        exact absurd hr' (by omega)
      ·
        rw [h1lab] at hh
        nomatch hh.1
    have hdvdX : p ∣ 2 ^ labX.n - 1 ∨ p ∣ 2 ^ labX.n + 1 := by
      have hfac : 2 ^ (2 * labX.n) - 1 = (2 ^ labX.n - 1) * (2 ^ labX.n + 1) := by
        rw [show 2 * labX.n = labX.n * 2 by omega, pow_mul, pow_two, mul_self_tsub_one,
          mul_comm]
      rw [hfac] at hsub
      exact (Nat.Prime.dvd_mul hp).mp hsub
    exact tcl_cover_lift (tcl_generic_or_RA_of_clTag hp hp2 hcl hdvdX)

theorem ggTPN_classicalCover
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    (hm : GGTPNMarked p (fun _ _ => True) A) {labX : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 labX) (hhX : GGHasLabel labX (X ⧸ Subgroup.center X))
    (hcl : GGTPNClTag labX.tag) :
    GGKacGenericCl labX p ∨ GGKacRA labX p ∨ (p = 7 ∧ labX = ⟨.A, 8, 1⟩) ∨
      (p = 5 ∧ labX = ⟨.A, 5, 2⟩) := by
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨-, lab₁, hΛ₁, hraw⟩ := hm
  have h₁ : GGHasLabel lab₁ (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  have hhalf : LargeEvenHalfSplit p lab₁ (Subgroup.center X = ⊥) := by
    have hraw' : LargeEvenRawDatum lab₁ (fun R _ I F =>
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : X ⧸ Subgroup.center X ≃* R,
            LargeEvenHalfSplit p lab₁ (Subgroup.center X = ⊥)) :=
      largeEvenRawDatum_mono (fun R _ I F hQ => by
        obtain ⟨hs, hna, θ, -, h2, -⟩ := hQ
        exact ⟨hs, hna, θ, h2⟩) hraw
    obtain ⟨_, _, _, _, _, _, _, h2⟩ := largeEvenRawDatum_exists hraw'
    exact h2
  have hiso : GGLabelIso lab₁ labX :=
    hrig lab₁ labX (X ⧸ Subgroup.center X) hΛ₁ hΛ h₁ hhX
  rcases largeEvenHalfSplit_dvd hΛ₁ hhalf with hsq | hexc
  · have hdvd₁ : p ∣ 2 ^ lab₁.n - 1 ∨ p ∣ 2 ^ lab₁.n + 1 := by
      have hfac : (2 ^ lab₁.n) ^ 2 - 1 = (2 ^ lab₁.n - 1) * (2 ^ lab₁.n + 1) := by
        rw [pow_two, mul_self_tsub_one, mul_comm]
      rw [hfac] at hsq
      exact (Nat.Prime.dvd_mul hp).mp hsq
    exact tcl_cover_of_iso hp hp2 hΛ₁ hcl hiso hhalf hdvd₁
  · obtain ⟨h7, hexlab⟩ := hexc
    rcases hexlab with hlab | hlab
    · have hXeq : labX = lab₁ :=
        tcl_eq_of_iso_of_exc (lab := lab₁) (lab' := labX) (Or.inl hlab) hiso
      exact Or.inr (Or.inr (Or.inl ⟨h7, hXeq.trans hlab⟩))
    · exfalso
      have hXeq : labX = lab₁ :=
        tcl_eq_of_iso_of_exc (lab := lab₁) (lab' := labX) (Or.inr hlab) hiso
      rw [hXeq, hlab] at hcl
      simp [GGTPNClTag] at hcl

end CFSG.StandardType

end
