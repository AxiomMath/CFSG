module

public import CFSG.LocalAnalysis.StandardType.GGFieldTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldTwoTable
public import CFSG.LocalAnalysis.StandardType.GGFieldTwoAb
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacQsOne
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem fts_iso_eq_of_tag_A_rank {lab labX : LargeEvenLabel}
    (htag : lab.tag = .A) (hr : 5 ≤ lab.rank) (h : GGLabelIso lab labX) : labX = lab := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  · rcases h.1 with hB | hC
    · exact absurd (hB ▸ htag) (by simp)
    · exact absurd (hC ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · have : lab.rank = 3 := by rw [h.1]
    omega
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · have : lab.rank = 1 := by rw [h.2]
    omega

private theorem fts_n_eq_one_or_A12 {lab labX : LargeEvenLabel} (h : GGLabelIso lab labX)
    (hnX : labX.n = 1) : lab.n = 1 ∨ lab = ⟨.A, 1, 2⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl (by rw [h, hnX])
  · exact Or.inl (by rw [h.2.2.2, hnX])
  · have h2' : labX.n = lab.n := by simpa using congrArg LargeEvenLabel.n h.2
    exact Or.inl (by omega)
  · have h2' : labX.n = lab.n := by simpa using congrArg LargeEvenLabel.n h.2
    exact Or.inl (by omega)
  · have h2' : labX.n = lab.n := by simpa using congrArg LargeEvenLabel.n h.2
    exact Or.inl (by omega)
  · have h2' : labX.n = lab.n := by simpa using congrArg LargeEvenLabel.n h.2
    exact Or.inl (by omega)
  · have h2' : labX.n = 2 * lab.n := by simpa using congrArg LargeEvenLabel.n h.2
    exact Or.inl (by omega)
  · exact Or.inr (by rw [h.2, hnX])

theorem ggFieldTwoClGen_holds :
    GGTablePKnownR fun p n labJ labX => GGRegimeFieldTwo p n labJ labX ∧ GGKacGenericCl labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hR hhJ hhX
  obtain ⟨hRreg, hgen⟩ := hR
  obtain ⟨hloc, hflat, hcard, hrank, hnum, hself, honly, hm⟩ := hd.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hK0 : GGK0MainB GGKacGenericCl GGMultValidCl := ggK0MainBS_cl.toB
  have hS : GGK0Schur GGKacGenericCl := ggK0Schur_cl
  have hp3 : p = 3 := by
    have hdvd := hgen.2.2.1
    rw [hRreg.2.1] at hdvd
    norm_num at hdvd
    rcases hdvd with h | h
    · exact absurd h hp.ne_one
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  have hJ2 : 2 ≤ labJ.n := hRreg.1
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
  obtain ⟨lab, hΛlab, hSlab, hgenlab, hXlab, hZ, D, hD, hJonly, o, hDo, hqso, huniq,
      hdvd, hoΛ, hJo⟩ :=
    exists_ggKacDatum_of_ggK0MainB_qsOne hK0 hS hloc honly hm' hgen'
  have hEq : GGLabelIso o.lab labJ :=
    hrig o.lab labJ (↥J ⧸ Subgroup.center ↥J) hoΛ hΛJ hJo hhJ
  have hiso : GGLabelIso lab labX :=
    hrig lab labX (X ⧸ Subgroup.center X) hΛlab hΛX hXlab hhX
  have hn : lab.n = 1 ∨ lab = ⟨.A, 1, 2⟩ := fts_n_eq_one_or_A12 hiso hRreg.2.1
  have hXnot : ¬ GGLabelIso o.lab lab := by
    intro hiso'
    exact not_ggHasLabel_of_le_ggAutFixedSubgroup hperf hloc.2.2.1 hloc.2.2.2.1.1 hXlab
      (largeEvenRawDatum_of_ggLabelIso hiso' hJo)
  rcases ggFieldTwoTable_outcome hΛlab hn (hp3 ▸ hD) hDo hqso huniq hEq hJ2 hXnot with h24 | hA
  · exact (ggFieldTwoL24_false (hp3 ▸ hd.1)
      (largeEvenRawDatum_of_ggLabelIso h24 hJo)).elim
  · obtain ⟨htag, hr⟩ := hA
    have hXeq : labX = lab := fts_iso_eq_of_tag_A_rank htag hr hiso
    exact absurd (by rw [hXeq]; exact ⟨htag, hp3, hr⟩) hRreg.2.2

end CFSG.StandardType

end
