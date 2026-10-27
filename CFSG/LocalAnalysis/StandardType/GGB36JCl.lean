module

public import CFSG.LocalAnalysis.StandardType.GGB36JNonExc
public import CFSG.LocalAnalysis.StandardType.GGALocalRank
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRAC4
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacV2
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableCl
public import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem twoLocalRank_le_of_ggTPNNum_three {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} (hAbA : Ab ≤ A) (hrank : GGTPNRank 3 X Ab)
    (hnum : GGTPNNum 3 (3 ^ 6) A Ab) :
    LargeEvenTwoLocalRank 3 X ≤ 5 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) := by
  obtain ⟨hnum1, -⟩ := hnum
  have hcardA : Nat.card A ≤ 3 ^ 5 := by
    have h36 : (3 : ℕ) ^ 6 = 3 * 3 ^ 5 := by norm_num
    rw [h36] at hnum1
    exact Nat.le_of_mul_le_mul_left hnum1 (by norm_num)
  have hcardAb : Nat.card Ab ≤ 3 ^ 5 := (Subgroup.card_le_of_le hAbA).trans hcardA
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm5 : m ≤ 5 := by
    rw [hmcard] at hcardAb
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcardAb
  omega

theorem rank_le_five_of_ggKacRA_of_ggTPNNum
    {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} (hAbA : Ab ≤ A) (hrank : GGTPNRank 3 X Ab)
    (hnum : GGTPNNum 3 (3 ^ 6) A Ab) (hperf : commutator X = ⊤) {labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hRA : GGKacRA labX 3)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : labX.rank ≤ 5 := by
  by_contra h
  have h3 : 3 ∣ labX.rank + 1 := by
    rcases hRA with ⟨-, hdvd, -⟩ | ⟨-, hdvd, -⟩ <;> exact hdvd
  have h9 : 9 ≤ labX.rank + 1 := by omega
  have hq : (labX.tag = .A ∧ 3 ∣ 2 ^ labX.n - 1) ∨ (labX.tag = .twA ∧ 3 ∣ 2 ^ labX.n + 1) := by
    rcases hRA with ⟨ht, -, hq⟩ | ⟨ht, -, hq⟩
    · exact Or.inl ⟨ht, hq⟩
    · exact Or.inr ⟨ht, hq⟩
  have h6 := ggALocalRankThree_holds X labX hΛX hq h3 h9 hhX hperf
  have h5 := twoLocalRank_le_of_ggTPNNum_three hAbA hrank hnum
  omega

private theorem ggKacGenericCl_three_of_ggLabelIso_n {a b : LargeEvenLabel}
    (h : a = b ∨ ((a.tag = .B ∨ a.tag = .C) ∧ (b.tag = .B ∨ b.tag = .C) ∧
      a.rank = b.rank ∧ a.n = b.n)) (hb : GGKacGenericCl b 3) :
    GGKacGenericCl a 3 := by
  rcases h with rfl | hBC
  · exact hb
  · obtain ⟨h1, -, -, hn⟩ := hBC
    obtain ⟨hb1, hb2, hb3, -, -, -⟩ := hb
    refine ⟨hb1, hb2, ?_, ?_, ?_, ?_⟩
    · rwa [hn]
    · rcases h1 with h1 | h1 <;> simp [h1]
    · rintro ⟨ha, -⟩
      rcases h1 with h1 | h1 <;> rw [h1] at ha <;> simp at ha
    · rintro ⟨ha, -⟩
      rcases h1 with h1 | h1 <;> rw [h1] at ha <;> simp at ha

private theorem ggKacGenericCl_three_of_ggLabelIso_twD2 {a b : LargeEvenLabel}
    (h : (a = ⟨.twD, 2, a.n⟩ ∧ b = ⟨.A, 1, 2 * a.n⟩) ∨
      (b = ⟨.twD, 2, b.n⟩ ∧ a = ⟨.A, 1, 2 * b.n⟩)) :
    GGKacGenericCl a 3 := by
  obtain ⟨t, l, n⟩ := a
  obtain ⟨t', l', n'⟩ := b
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
  · dsimp only at h1
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    refine ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add n, by simp, ?_, ?_⟩
    · rintro ⟨ha, -⟩; simp at ha
    · rintro ⟨ha, -⟩; simp at ha
  · dsimp only at h2
    obtain ⟨rfl, rfl, hn⟩ := LargeEvenLabel.mk.injEq .. |>.mp h2
    subst hn
    refine ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add (2 * n'), by simp,
      ?_, ?_⟩
    · rintro ⟨-, hdvd, -⟩; norm_num at hdvd
    · rintro ⟨ha, -⟩; simp at ha

private theorem ggKacGenericCl_three_of_ggLabelIso {a b : LargeEvenLabel}
    (h : GGLabelIso a b) (hb : GGKacGenericCl b 3) : GGKacGenericCl a 3 := by
  obtain ⟨t, l, n⟩ := a
  obtain ⟨t', l', n'⟩ := b
  rcases h with h | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · exact ggKacGenericCl_three_of_ggLabelIso_n (Or.inl h) hb
  · exact ggKacGenericCl_three_of_ggLabelIso_n (Or.inr hBC) hb
  · obtain ⟨h1, -⟩ := hDA
    dsimp only at h1
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    refine ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add n, by simp, ?_, ?_⟩
    · rintro ⟨ha, -⟩; simp at ha
    · rintro ⟨ha, -⟩; simp at ha
  · obtain ⟨h1, -⟩ := hAD
    dsimp only at h1
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    refine ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add n, by simp, ?_, ?_⟩
    · rintro ⟨-, hdvd, -⟩; norm_num at hdvd
    · rintro ⟨ha, -⟩; simp at ha
  · obtain ⟨h1, -⟩ := hD3A3
    dsimp only at h1
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    refine ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add n, by simp, ?_, ?_⟩
    · rintro ⟨ha, -⟩; simp at ha
    · rintro ⟨ha, -⟩; simp at ha
  · obtain ⟨h1, -⟩ := hA3D3
    dsimp only at h1
    obtain ⟨rfl, rfl, -⟩ := LargeEvenLabel.mk.injEq .. |>.mp h1
    refine ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add n, by simp, ?_, ?_⟩
    · rintro ⟨ha, -⟩; simp at ha
    · rintro ⟨-, hdvd, -⟩; norm_num at hdvd
  · exact ggKacGenericCl_three_of_ggLabelIso_twD2 (Or.inl hD2A1)
  · exact ggKacGenericCl_three_of_ggLabelIso_twD2 (Or.inr hA1D2)

private theorem eq_of_ggLabelIso_of_b36JLabel {labL labJ a : LargeEvenLabel}
    (hIso : GGLabelIso a labJ) (hJ : GGB36JLabel labL labJ) : a = labJ := by
  unfold GGB36JLabel at hJ
  dsimp only at hJ
  obtain ⟨t, l, m⟩ := a
  rcases hJ with ⟨-, -, h | h | h | h | h⟩ | ⟨-, -, h | h | ⟨-, h⟩⟩ |
    ⟨-, -, h | h⟩ | ⟨-, -, h | h | h | h | h | ⟨-, h⟩⟩
  all_goals
    subst h
    rcases hIso with h' | h' | h' | h' | h' | h' | h' | h' <;> simp_all [GGLabelIso]

private theorem three_not_dvd_pow_three_mul_add_one {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    ¬ 3 ∣ 2 ^ (3 * n) + 1 := by
  obtain ⟨k, hk⟩ := h
  have hk' : 2 ^ n = 3 * k + 1 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  have hcube : 2 ^ (3 * n) = (3 * k + 1) ^ 3 := by
    rw [show 3 * n = n * 3 by omega, pow_mul, hk']
  intro hd
  obtain ⟨m, hm⟩ := hd
  rw [hcube] at hm
  have hform : (3 * k + 1) ^ 3 + 1 = 3 * (9 * k ^ 3 + 9 * k ^ 2 + 3 * k) + 2 := by ring
  omega

private theorem three_dvd_pow_three_mul_add_one_of_add_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    3 ∣ 2 ^ (3 * n) + 1 := by
  obtain ⟨k, hk⟩ := h
  have hk1 : 1 ≤ k := by
    have : 0 < 2 ^ n + 1 := by positivity
    omega
  have hk' : 2 ^ n = 3 * (k - 1) + 2 := by omega
  have hcube : 2 ^ (3 * n) = (3 * (k - 1) + 2) ^ 3 := by
    rw [show 3 * n = n * 3 by omega, pow_mul, hk']
  have hform : (3 * (k - 1) + 2) ^ 3 + 1 =
      3 * (9 * (k - 1) ^ 3 + 18 * (k - 1) ^ 2 + 12 * (k - 1) + 3) := by ring
  rw [hcube, hform]
  exact dvd_mul_right 3 _

private theorem three_not_dvd_pow_three_mul_sub_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    ¬ 3 ∣ 2 ^ (3 * n) - 1 := by
  have hpos := three_dvd_pow_three_mul_add_one_of_add_one h
  have h1 : 1 ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
  intro hd
  have h2 : 3 ∣ (2 ^ (3 * n) + 1) - (2 ^ (3 * n) - 1) := Nat.dvd_sub hpos hd
  have h3 : (2 ^ (3 * n) + 1) - (2 ^ (3 * n) - 1) = 2 := by omega
  rw [h3] at h2
  omega

private theorem not_rankOne_A2_three_mul {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    ¬ GGTPNPRankOne 3 ⟨.A, 2, 3 * n⟩ := by
  intro hrk
  unfold GGTPNPRankOne at hrk
  rcases hrk with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨-, -, h1⟩ | ⟨h1, -, -⟩
  · simp at h1
  · simp at h1
  · exact three_not_dvd_pow_three_mul_add_one h h1
  · simp at h1

private theorem not_rankOne_twA2_three_mul {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    ¬ GGTPNPRankOne 3 ⟨.twA, 2, 3 * n⟩ := by
  intro hrk
  unfold GGTPNPRankOne at hrk
  rcases hrk with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h1⟩
  · simp at h1
  · simp at h1
  · simp at h1
  · exact three_not_dvd_pow_three_mul_sub_one h h1

private theorem not_rankOne_A2_two : ¬ GGTPNPRankOne 3 ⟨.A, 2, 2⟩ := by
  intro hrk
  unfold GGTPNPRankOne at hrk
  rcases hrk with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨-, -, h1⟩ | ⟨h1, -, -⟩
  · simp at h1
  · simp at h1
  · norm_num at h1
  · simp at h1

private theorem not_ggTPNPRankOne_three_of_b36JLabel {labL labJ : LargeEvenLabel}
    (hJ : GGB36JLabel labL labJ) : ¬ GGTPNPRankOne 3 labJ := by
  unfold GGB36JLabel at hJ
  dsimp only at hJ
  rcases hJ with ⟨-, hdvd, h | h | h | h | h⟩ | ⟨-, hdvd, h | h | ⟨-, h⟩⟩ |
    ⟨-, hdvd, h | h⟩ | ⟨-, hdvd, h | h | h | h | h | ⟨-, h⟩⟩
  all_goals
    subst h
    first
      | exact not_rankOne_A2_three_mul hdvd
      | exact not_rankOne_twA2_three_mul hdvd
      | exact not_rankOne_A2_two
      | simp [GGTPNPRankOne]

theorem ggTPNRow_b36JCl_generic
    (hK0 : GGK0MainBS GGKacGenericCl GGMultValidCl) (hS : GGK0Schur GGKacGenericCl)
    {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} (hloc : GGTPNLocalCore 3 A σ J) (ha : GGTPNSelfCent 3 A)
    (hk : GGTPNKernel A σ J) (h8 : GGTPNOnlyComp 3 σ J) (hm : GGTPNMarked 3 S A)
    {labJ labX : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ) (hΛX : LargeEvenInLambda2 labX)
    (hJ : ∃ labL : LargeEvenLabel, (labL.tag = .E6 ∨ labL.tag = .twE6) ∧ GGB36JLabel labL labJ)
    (hgen : GGKacGenericCl labX 3) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    GGTPNRow 3 J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hperf : commutator X = ⊤ := by
    obtain ⟨hcomm, -⟩ := hm
    exact hcomm
  have hm' : GGTPNMarked 3 (fun q lab => ∃ c : Prop, LargeEvenHalfSplit q lab c) A := by
    obtain ⟨hX, lab, hlab, hraw⟩ := hm
    exact ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, h1, h2, h3⟩ => ⟨hs, hna, θ, ⟨_, h2⟩, h2, h3⟩) hraw⟩
  have hgen' : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      GGKacGenericCl lab 3 := by
    intro lab hlab hhas
    exact ggKacGenericCl_three_of_ggLabelIso
      (hrig lab labX (X ⧸ Subgroup.center X) hlab hΛX hhas hhX) hgen
  obtain ⟨lab, hΛlab, hSlab, -, hXlab, D, hD, hrZ, -, o, hDo, hqs, -, hoΛ, hJo⟩ :=
    exists_ggKacDatum_of_ggK0MainBS hK0 hS hloc ha hk h8 hm' hgen'
  obtain ⟨c, hc⟩ := hSlab
  obtain ⟨labL, -, hJlabel⟩ := hJ
  have hEq : o.lab = labJ :=
    eq_of_ggLabelIso_of_b36JLabel
      (hrig o.lab labJ (↥J ⧸ Subgroup.center ↥J) hoΛ hΛJ hJo hhJ) hJlabel
  have hrk : ¬ GGTPNPRankOne 3 o.lab := by
    rw [hEq]
    exact not_ggTPNPRankOne_three_of_b36JLabel hJlabel
  have hXnot : ¬ GGLabelIso o.lab lab := by
    intro hiso
    exact not_ggHasLabel_of_le_ggAutFixedSubgroup hperf hloc.2.2.1 hloc.2.2.2.1.1 hXlab
      (largeEvenRawDatum_of_ggLabelIso hiso hJo)
  obtain ⟨-, labJ', labX', hiso1, hiso2, hΛJ', hΛX', hrow⟩ :=
    ggTablePRow_of_ggMultValidCl hΛlab hc hD hrZ hDo hqs hXnot hrk
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    largeEvenRawDatum_of_ggLabelIso hiso1 hJo,
    largeEvenRawDatum_of_ggLabelIso hiso2 hXlab⟩

theorem ggB36JClassicalRK_holds
    (hK0 : GGK0MainBS GGKacGenericCl GGMultValidCl) (hS : GGK0Schur GGKacGenericCl) :
    GGB36JClassicalRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, hn, hJ⟩, htag⟩ := hr
  subst hp3
  subst hn
  obtain ⟨hloc, hflat, -, hrank, hnum, hself, honly, hm⟩ := hd.1
  have hperf : commutator X = ⊤ := by
    have hm' := hm
    unfold GGTPNMarked at hm'
    exact hm'.1
  by_cases hRA : GGKacRA labX 3
  · exact ggTPNRow_b36JCl_ra hloc honly hm hΛJ hΛX hJ hRA
      (rank_le_five_of_ggKacRA_of_ggTPNNum hflat.1 hrank hnum hperf hΛX hRA hhX) hhJ hhX
  · exact ggTPNRow_b36JCl_generic hK0 hS hloc hself hk honly hm hΛJ hΛX hJ
      ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add labX.n, htag,
        fun h => hRA (Or.inl h), fun h => hRA (Or.inr h)⟩ hhJ hhX

end CFSG.StandardType

end
