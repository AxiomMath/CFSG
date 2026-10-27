module

public import CFSG.LocalAnalysis.StandardType.GGAm2Defs
public import CFSG.LocalAnalysis.StandardType.GGAm2Table
public import CFSG.LocalAnalysis.StandardType.GGAm2Ab
public import CFSG.LocalAnalysis.StandardType.GGOmegaTwoThree
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacQsOne
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGExcGen
public import CFSG.LocalAnalysis.StandardType.GGTPNExcTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGE6TwoLocalRank
public import CFSG.LocalAnalysis.StandardType.GGE6TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGE78LocalRank
public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankHolds
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggAm2ClGen_holds :
    GGTablePKnownR fun p n labJ labX => GGRegimeAm2 p n labJ labX ∧ GGKacGenericCl labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hR hhJ hhX
  obtain ⟨hRreg, hgen⟩ := hR
  obtain ⟨hloc, hflat, hcard, hrank, hnum, hself, honly, hm⟩ := hd.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hK0 : GGK0MainB GGKacGenericCl GGMultValidCl := ggK0MainBS_cl.toB
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
  obtain ⟨lab, hΛlab, -, -, hXlab, hZ, D, hD, -, o, ho, hqs, huniq, hdvd, hoΛ, hJo⟩ :=
    exists_ggKacDatum_of_ggK0MainB_qsOne hK0 hS hloc honly hm' hgen'
  have hp3 : p = 3 := hRreg.1
  rcases labJ with ⟨tJ, rJ, nJ⟩
  have htagJ : tJ = .A := hRreg.2.1
  have hnJ : nJ = 1 := hRreg.2.2.1
  have hrJ : 3 ≤ rJ := hRreg.2.2.2
  have hEq : GGLabelIso o.lab ⟨tJ, rJ, nJ⟩ :=
    hrig o.lab ⟨tJ, rJ, nJ⟩ (↥J ⧸ Subgroup.center ↥J) hoΛ hΛJ hJo hhJ
  have hJ : GGLabelIso o.lab ⟨.A, rJ, 1⟩ := by
    have h := hEq
    rw [htagJ, hnJ] at h
    exact h
  have ho1 : o.lab.n = 1 := by
    by_contra hne
    have ho2 : 2 ≤ o.lab.n := by have := hoΛ.1; omega
    exact ltqSl_iso_n_le_one ho2 hEq hnJ
      (by rintro ⟨hD, -⟩; rw [htagJ] at hD; simp at hD)
  have hn : lab.n = 1 := by
    have h1 : lab.n ∣ 1 := by simpa [ho1] using hdvd
    exact Nat.dvd_one.mp h1
  have hXnot : ¬ GGLabelIso o.lab lab := by
    intro hiso
    exact not_ggHasLabel_of_le_ggAutFixedSubgroup hperf hloc.2.2.1 hloc.2.2.2.1.1 hXlab
      (largeEvenRawDatum_of_ggLabelIso hiso hJo)
  have hD3 : GGMultValidCl lab 3 D := by simpa [hp3] using hD
  rcases ggAm2Table_outcome hΛlab hn hD3 ho hqs huniq hJ hrJ hXnot with
    ⟨labJ', labX', hiso1, hiso2, hΛJ', hΛX', hrow⟩ | ⟨hlabD5, hoA3⟩ | ⟨hlabtwD6, hoA3⟩
  · exact ⟨labJ', labX', hΛJ', hΛX', by rw [hp3]; exact hrow,
      largeEvenRawDatum_of_ggLabelIso hiso1 hJo,
      largeEvenRawDatum_of_ggLabelIso hiso2 hXlab⟩
  · exfalso
    have hJ3 : GGHasLabel ⟨.A, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
      rw [← hoA3]
      exact hJo
    have hAb3 : GGTPNBasicB 3 n (fun _ _ => True) A Ab σ J := by simpa [hp3] using hd.1
    have hAble : Nat.card Ab ≤ 3 ^ 3 := ggAm2Ab_card_le hAb3 hJ3
    have hrank3 : GGTPNRank 3 X Ab := by simpa [hp3] using hrank
    obtain ⟨μ, hcardμ, hμle⟩ := hrank3
    have hle : 3 ^ μ ≤ 3 ^ 3 := by rw [← hcardμ]; exact hAble
    have hμ3 : μ ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    have hZ3 : (Nat.card (Subgroup.center X)).Coprime 3 := by simpa [hp3] using hZ
    have hnotdvd : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
      fun h3 => (Nat.prime_three.coprime_iff_not_dvd).mp hZ3.symm h3
    have hle3 : LargeEvenTwoLocalRank 3 X ≤ 3 := by
      rw [if_neg hnotdvd, add_zero] at hμle
      omega
    have h4 : 4 ≤ LargeEvenTwoLocalRank 3 X :=
      ggTwoLocalRank_D5_two_three hperf (by simpa [hlabD5] using hXlab)
    omega
  · exfalso
    have hJ3 : GGHasLabel ⟨.A, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
      rw [← hoA3]
      exact hJo
    have hAb3 : GGTPNBasicB 3 n (fun _ _ => True) A Ab σ J := by simpa [hp3] using hd.1
    have hAble : Nat.card Ab ≤ 3 ^ 3 := ggAm2Ab_card_le hAb3 hJ3
    have hrank3 : GGTPNRank 3 X Ab := by simpa [hp3] using hrank
    obtain ⟨μ, hcardμ, hμle⟩ := hrank3
    have hle : 3 ^ μ ≤ 3 ^ 3 := by rw [← hcardμ]; exact hAble
    have hμ3 : μ ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    have hZ3 : (Nat.card (Subgroup.center X)).Coprime 3 := by simpa [hp3] using hZ
    have hnotdvd : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
      fun h3 => (Nat.prime_three.coprime_iff_not_dvd).mp hZ3.symm h3
    have hle3 : LargeEvenTwoLocalRank 3 X ≤ 3 := by
      rw [if_neg hnotdvd, add_zero] at hμle
      omega
    have h4 : 4 ≤ LargeEvenTwoLocalRank 3 X :=
      ggTwoLocalRank_twD6_two_three hperf (by simpa [hlabtwD6] using hXlab)
    omega

private theorem am2b_iso_n_eq_one {l labJ : LargeEvenLabel}
    (h : GGLabelIso l labJ) (htag : labJ.tag = .A) (hn : labJ.n = 1)
    (hr : labJ.rank ≠ 1) : l.n = 1 := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · rw [h, hn]
  · rw [h.2.2.2, hn]
  · exact (congrArg LargeEvenLabel.n h.2).symm.trans hn
  · exact absurd (htag.symm.trans (congrArg LargeEvenLabel.tag h.2)) (by dsimp; decide)
  · exact absurd (htag.symm.trans (congrArg LargeEvenLabel.tag h.2)) (by dsimp; decide)
  · exact absurd (htag.symm.trans (congrArg LargeEvenLabel.tag h.2)) (by dsimp; decide)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) hr
  · exact absurd (htag.symm.trans (congrArg LargeEvenLabel.tag h.1)) (by dsimp; decide)

theorem ggAm2ExcBig_holds
    (hTCJ : GGTCJKnown) : GGAm2ExcBig := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hR hhJ hhX
  obtain ⟨hRreg, hpair, h2n⟩ := hR
  obtain ⟨hp3, htagJ, hnJ, hrJ⟩ := hRreg
  obtain ⟨hloc, -, -, -, -, -, -, hm⟩ := hd.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hcomm, labm, hΛm, hrawm⟩ := hm
  have hmHas : GGHasLabel labm (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hrawm
  have htagX : labX.tag = .E6 ∨ labX.tag = .twE6 ∨ labX.tag = .E7 ∨ labX.tag = .E8 ∨
      labX.tag = .F4 := hpair.2.2.2
  have hisom : GGLabelIso labm labX :=
    hrig labm labX (X ⧸ Subgroup.center X) hΛm hΛX hmHas hhX
  have hlabm_eq : labm = labX := excg_labelIso_eq_of_exc hisom htagX
  have hrawTCJ := hTCJ p hp hp2 labm hΛm _ hrawm
  obtain ⟨R, hR, I, F, hP⟩ := largeEvenRawDatum_exists hrawTCJ
  letI := hR
  obtain ⟨hQ, hPK0⟩ := hP
  obtain ⟨-, -, θ, -, -, hind⟩ := hQ
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
    exact θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center X := by
    change (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker ≤
      Subgroup.center X
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X)) θ.toMonoidHom
      θ.injective, QuotientGroup.ker_mk']
  have hσp : σ ^ p = 1 := hloc.1.2 σ hloc.2.1
  have hIndOf : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l) := by
    intro a ha
    exact ⟨ggInducedAut θ a, hind a ha, fun l => by
      simpa [ψ, QuotientGroup.mk'_apply] using ggInducedAut_apply θ a l⟩
  obtain ⟨o, hoΛ, hndvd, hJo⟩ :=
    hPK0 X ψ hψsurj hψker hcomm σ hσp (hIndOf σ hloc.2.1) J hloc.2.2.2.1
  have hEq : GGLabelIso o labJ := hrig o labJ (↥J ⧸ Subgroup.center ↥J) hoΛ hΛJ hJo hhJ
  have hon : o.n = 1 := by
    have h1 : 1 ≤ o.n := hoΛ.1
    by_contra hne
    have h2 : 2 ≤ o.n := by omega
    exact ltqSl_iso_n_le_one h2 hEq hnJ (by rintro ⟨hD, -⟩; rw [htagJ] at hD; simp at hD)
  have hlabm_n : labm.n = labX.n := congrArg LargeEvenLabel.n hlabm_eq
  have h2 : 2 ≤ labm.n := by omega
  have hdvd1 : labm.n ∣ 1 := by rwa [hon] at hndvd
  have hle1 : labm.n ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd1
  exfalso
  omega

theorem am2_a3_exc_E6_false
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} {n : ℕ} {labX : LargeEvenLabel}
    (hd : GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J)
    (hhJ : GGHasLabel (⟨.A, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hΛX : LargeEvenInLambda2 labX) (htagX : labX.tag = .E6) (hnX : labX.n = 1)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : False := by
  have hlabX : labX = ⟨.E6, 0, 1⟩ :=
    ltqSl_labelX_eq htagX hΛX hnX (Or.inl rfl)
  subst labX
  obtain ⟨-, -, -, hrank, -, -, -, hm⟩ := hd.1
  obtain ⟨hcomm, -, -, -⟩ := hm
  have hAb : Nat.card Ab ≤ 3 ^ 3 := ggAm2Ab_card_le hd.1 hhJ
  obtain ⟨m, hcardm, hmle⟩ := hrank
  have hle : 3 ^ m ≤ 3 ^ 3 := by rw [← hcardm]; exact hAb
  have hm3 : m ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hZ : Subgroup.center X = ⊥ := ggE6TwoCenterBot_holds X hcomm hhX
  have hle3 : LargeEvenTwoLocalRank 3 X ≤ 3 := by
    rw [hZ, Subgroup.card_bot, if_neg (by decide : ¬ 3 ∣ (1 : ℕ)), add_zero] at hmle
    omega
  have h4 : 4 ≤ LargeEvenTwoLocalRank 3 X := ggE6TwoLocalRankThree_holds X hcomm hhX
  omega

theorem am2_a3_exc_E78_false
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} {n : ℕ} {labX : LargeEvenLabel}
    (hd : GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J)
    (hhJ : GGHasLabel (⟨.A, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hΛX : LargeEvenInLambda2 labX) (htagX : labX.tag = .E7 ∨ labX.tag = .E8)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨-, -, -, hrank, -, -, -, hm⟩ := hd.1
  obtain ⟨hcomm, -, -, -⟩ := hm
  have hAb : Nat.card Ab ≤ 3 ^ 3 := ggAm2Ab_card_le hd.1 hhJ
  obtain ⟨m, hcardm, hmle⟩ := hrank
  have hle : 3 ^ m ≤ 3 ^ 3 := by rw [← hcardm]; exact hAb
  have hm3 : m ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have h6 := ggE78LocalRankThree_holds X labX hΛX htagX hhX hcomm
  omega

theorem am2_a3_exc_twE6_false
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} {n : ℕ} {labX : LargeEvenLabel}
    (hd : GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J)
    (hhJ : GGHasLabel (⟨.A, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hΛX : LargeEvenInLambda2 labX) (htagX : labX.tag = .twE6) (hnX : labX.n = 1)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨-, -, -, hrank, -, -, -, hm⟩ := hd.1
  have hAb : Nat.card Ab ≤ 3 ^ 3 := ggAm2Ab_card_le hd.1 hhJ
  obtain ⟨m, hcardm, hmle⟩ := hrank
  have hle : 3 ^ m ≤ 3 ^ 3 := by rw [← hcardm]; exact hAb
  have hm3 : m ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hle4 : LargeEvenTwoLocalRank 3 X ≤ 4 := by
    have hε : (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ 1 := by
      split_ifs <;> omega
    omega
  obtain ⟨hcomm, labm, hΛm, hrawm⟩ := hm
  have hmHas : GGHasLabel labm (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hrawm
  have hisom : GGLabelIso labm labX :=
    ggLabelRigidInput_holds labm labX (X ⧸ Subgroup.center X) hΛm hΛX hmHas hhX
  have hlabm_eq : labm = labX := excg_labelIso_eq_of_exc hisom (Or.inr (Or.inl htagX))
  subst labm
  have hsplit : LargeEvenSplit 3 labX :=
    Or.inr (Or.inr (Or.inr ⟨hnX, rfl⟩))
  change LargeEvenRawDatum labX
    (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* R,
        (True ∧ LargeEvenHalfSplit 3 labX (Subgroup.center X = ⊥) ∧
          GGInducedInn A θ I)) at hrawm
  have hrawS : LargeEvenRawDatum labX
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R,
          labX.tag = .twE6 ∧ LargeEvenSplit 3 labX) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨hs, hna, θ, -⟩ := hQ
      exact ⟨hs, hna, θ, ⟨htagX, hsplit⟩⟩) hrawm
  have hAll := largeEvenLabelAll_twE6_rank ggTwE6LocalRankInput_holds hΛX htagX hsplit
  obtain ⟨R, hR, I, F, hQ, hguard⟩ := largeEvenRawDatum_exists (hAll _ hrawS)
  letI := hR
  obtain ⟨hs, hna, θ, -⟩ := hQ
  have hrankX : GGTwE6LocalRank R := hguard hs hna
  obtain ⟨U, hU, hU2, E, hEU, hE, hcard⟩ := hrankX X hcomm θ
  rcases hcard with h5 | ⟨h4, hbot⟩
  · by_cases h3Z : 3 ∣ Nat.card (Subgroup.center X)
    · have h5le : 5 ≤ LargeEvenTwoLocalRank 3 X :=
        le_twoLocalRank_of_normalizes Nat.prime_three hU hU2 hE hEU h5
      omega
    · have hle3 : LargeEvenTwoLocalRank 3 X ≤ 3 := by
        rw [if_neg h3Z, add_zero] at hmle
        omega
      have h5le : 5 ≤ LargeEvenTwoLocalRank 3 X :=
        le_twoLocalRank_of_normalizes Nat.prime_three hU hU2 hE hEU h5
      omega
  · by_cases h3Z : 3 ∣ Nat.card (Subgroup.center X)
    · obtain ⟨z, hzord⟩ :=
        exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 h3Z
      have hzX : (z : X) ^ 3 = 1 := by
        have hord : orderOf (z : X) = 3 := by
          rw [Subgroup.orderOf_coe, hzord]
        have := pow_orderOf_eq_one (z : X)
        rwa [hord] at this
      have hzE : (z : X) ∉ E := by
        intro hzmem
        have hzbot : (z : X) ∈ (⊥ : Subgroup X) := by
          rw [← hbot]
          exact ⟨hzmem, z.2⟩
        have hz1 : (z : X) = 1 := by simpa using hzbot
        have : orderOf (z : X) = 1 := by rw [hz1, orderOf_one]
        have hz3 : orderOf (z : X) = 3 := by rw [Subgroup.orderOf_coe, hzord]
        omega
      have hzcomm : ∀ e ∈ E, e * (z : X) = (z : X) * e := by
        intro e he
        exact Subgroup.mem_center_iff.mp z.2 e
      obtain ⟨hEab, hEcard⟩ :=
        isElemAbelian_sup_zpowers_of_card Nat.prime_three hE h4 hzX hzE hzcomm
      have hzN : Subgroup.zpowers (z : X) ≤ Subgroup.normalizer (U : Set X) := by
        rw [Subgroup.zpowers_le]
        apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact Subgroup.mem_center_iff.mp z.2 u
      have h5le : 5 ≤ LargeEvenTwoLocalRank 3 X :=
        le_twoLocalRank_of_normalizes Nat.prime_three hU hU2 hEab (sup_le hEU hzN)
          (by simpa using hEcard)
      omega
    · have hle3 : LargeEvenTwoLocalRank 3 X ≤ 3 := by
        rw [if_neg h3Z, add_zero] at hmle
        omega
      have h4le : 4 ≤ LargeEvenTwoLocalRank 3 X :=
        le_twoLocalRank_of_normalizes Nat.prime_three hU hU2 hE hEU h4
      omega

private theorem am2r_iso_A_of_tag_A {labJ l : LargeEvenLabel} (htag : labJ.tag = .A)
    (h : GGLabelIso labJ l) (hl : l.tag = .A) : labJ = l := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h.1 with hB | hC
    · exact absurd (hB ▸ htag) (by simp)
    · exact absurd (hC ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.2 ▸ hl) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.1 ▸ hl) (by simp)

private theorem am2r_not_iso_A {labJ l : LargeEvenLabel} (htag : labJ.tag = .A)
    (hr : 3 ≤ labJ.rank) (h : GGLabelIso labJ l) (hl : l.tag ≠ .A)
    (h4 : l.tag ≠ .D ∨ l.rank ≠ 3) : False := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact hl (h ▸ htag)
  · rcases h.1 with hB | hC
    · exact absurd (hB ▸ htag) (by simp)
    · exact absurd (hC ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · rcases h4 with hD | hr3
    · exact hD (by rw [h.2])
    · exact hr3 (by rw [h.2])
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · exact absurd (h.1 ▸ htag) (by simp)
  · exfalso
    have hrk := congrArg LargeEvenLabel.rank h.2
    simp at hrk
    omega

theorem ggAm2RA_holds :
    GGTablePKnownR fun p n labJ labX => GGRegimeAm2 p n labJ labX ∧ GGKacRA labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, htagJ, hnJ, hrankJ⟩, hRA⟩ := hr
  subst hp3
  obtain ⟨⟨hloc, _, _, _, _, _, h8, hm⟩, _⟩ := hd
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hm' : GGTPNMarked 3 (fun _ lab => lab = labX) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  have htagX : labX.tag = .A ∨ labX.tag = .twA := by
    rcases hRA with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases split_or_fieldType_of_ggKacRA Nat.prime_three hloc h8 hRA hm' with
    ⟨a, ds, hsum, hne, hlen, hmem, hbr⟩ | ⟨hge, hcardA, hbr⟩
  · rcases hbr with ⟨hΛ', hJ'⟩ | ⟨htwA, hA2, hΛ', hJ'⟩
    · rcases htagX with htA | htT
      ·
        have hΛl : LargeEvenInLambda2 (⟨.A, a - 1, labX.n⟩ : LargeEvenLabel) := by
          simpa [htA] using hΛ'
        have hJl : GGHasLabel (⟨.A, a - 1, labX.n⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) := by simpa [htA] using hJ'
        have hiso : GGLabelIso labJ (⟨.A, a - 1, labX.n⟩ : LargeEvenLabel) :=
          hrig labJ _ _ hΛJ hΛl hhJ hJl
        have heq := am2r_iso_A_of_tag_A htagJ hiso rfl
        have hnX1 : labX.n = 1 := by
          have hn := congrArg LargeEvenLabel.n heq
          simp at hn
          omega
        have hq : 3 ∣ 2 ^ labX.n - 1 := by
          rcases hRA with ⟨-, -, hq⟩ | ⟨hbad, -⟩
          · exact hq
          · exact absurd (hbad.symm.trans htA) (by decide)
        exact absurd hq (by rw [hnX1]; norm_num)
      ·
        have hΛl : LargeEvenInLambda2 (⟨.twA, a - 1, labX.n⟩ : LargeEvenLabel) := by
          simpa [htT] using hΛ'
        have hJl : GGHasLabel (⟨.twA, a - 1, labX.n⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) := by simpa [htT] using hJ'
        exact (am2r_not_iso_A htagJ hrankJ (hrig labJ _ _ hΛJ hΛl hhJ hJl)
          (by simp) (Or.inl (by simp))).elim
    ·
      have hiso : GGLabelIso labJ (⟨.A, 1, labX.n⟩ : LargeEvenLabel) :=
        hrig labJ _ _ hΛJ hΛ' hhJ hJ'
      have heq := am2r_iso_A_of_tag_A htagJ hiso rfl
      have hrk := congrArg LargeEvenLabel.rank heq
      simp at hrk
      omega
  ·
    rcases hbr with ⟨-, hΛ', hJ'⟩ | ⟨-, -, hΛ', hJ'⟩
    · have hΛl : LargeEvenInLambda2
          (⟨.A, (labX.rank + 1) / 3 - 1, 3 * labX.n⟩ : LargeEvenLabel) := hΛ'
      have hJl : GGHasLabel (⟨.A, (labX.rank + 1) / 3 - 1, 3 * labX.n⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := hJ'
      have hiso : GGLabelIso labJ
          (⟨.A, (labX.rank + 1) / 3 - 1, 3 * labX.n⟩ : LargeEvenLabel) :=
        hrig labJ _ _ hΛJ hΛl hhJ hJl
      have heq := am2r_iso_A_of_tag_A htagJ hiso rfl
      have hn := congrArg LargeEvenLabel.n heq
      simp at hn
      have hnX1 : 1 ≤ labX.n := by simpa using hΛX.1
      omega
    · have hΛl : LargeEvenInLambda2
          (⟨.twA, (labX.rank + 1) / 3 - 1, 3 * labX.n⟩ : LargeEvenLabel) := hΛ'
      have hJl : GGHasLabel (⟨.twA, (labX.rank + 1) / 3 - 1, 3 * labX.n⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := hJ'
      exact (am2r_not_iso_A htagJ hrankJ (hrig labJ _ _ hΛJ hΛl hhJ hJl)
        (by simp) (Or.inl (by simp))).elim

end CFSG.StandardType

end
