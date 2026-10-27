module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggKacRA_n_eq_one_of_labelIso_twA {lab : LargeEvenLabel} {r : ℕ}
    (h : GGLabelIso lab ⟨.twA, r, 1⟩) : lab.n = 1 := by
  rcases h with h | h | h | h | h | h | h | h
  · rw [h]
  · exact h.2.2.2
  · obtain ⟨h1, h2⟩ := h; rw [h1]; simpa using h2
  · obtain ⟨h1, h2⟩ := h; rw [h1]; simpa using h2
  · obtain ⟨h1, h2⟩ := h; rw [h1]
    have := congrArg LargeEvenLabel.n h2
    simpa using this.symm
  · obtain ⟨-, h2⟩ := h; simp at h2
  · obtain ⟨-, h2⟩ := h; simp at h2
  · obtain ⟨h1, -⟩ := h; simp at h1

private theorem ggKacRA_le_twoLocalRank_of_torusLift {X R : Type} [Group X] [Finite X] [Group R]
    {r : ℕ} (hT : GGTorusLift 3 r R) (e : X ⧸ Subgroup.center X ≃* R)
    (hcomm : commutator X = ⊤) : r ≤ LargeEvenTwoLocalRank 3 X := by
  let ψ : X →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      change e (QuotientGroup.mk' (Subgroup.center X) x) = 1 at hx
      rw [QuotientGroup.mk'_apply] at hx
      have h1 : QuotientGroup.mk x = 1 := e.injective (by rw [hx, map_one])
      rwa [QuotientGroup.eq_one_iff] at h1
    · intro hx
      have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      show e (QuotientGroup.mk' (Subgroup.center X) x) = 1
      rw [h1, map_one]
  obtain ⟨U, E, hUne, hU2, hEU, hEab, hEcard, -⟩ := hT X ψ hψs hker.le hcomm
  exact TableB.le_twoLocalRank (p := 3) (by norm_num) ⟨U, hUne, hU2, rfl⟩
    (TableB.le_pRank_of_le (by norm_num) hEU hEab hEcard)

private lemma ggKacRA_split_label_n_eq_one (hrig : GGLabelRigidInput) {X : Type} [Group X]
    {J : Subgroup X} {labJ labX : LargeEvenLabel} {a : ℕ} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) (hJ2 : 2 ≤ labJ.n)
    (htag : labX.tag = .twA) (hX1 : labX.n = 1)
    (hlabel : (LargeEvenInLambda2 ⟨labX.tag, a - 1, labX.n⟩ ∧
        GGHasLabel ⟨labX.tag, a - 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (labX.tag = .twA ∧ a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, labX.n⟩ ∧
        GGHasLabel ⟨.A, 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J))) : False := by
  rcases hlabel with ⟨hΛ', hJ'⟩ | ⟨-, -, hΛ', hJ'⟩
  · have hΛ'' : LargeEvenInLambda2 ⟨.twA, a - 1, 1⟩ := by
      simpa [htag, hX1] using hΛ'
    have hJ'' : GGHasLabel ⟨.twA, a - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
      simpa [htag, hX1] using hJ'
    have hiso := hrig labJ ⟨.twA, a - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) hΛJ hΛ'' hJ hJ''
    have hn1 := ggKacRA_n_eq_one_of_labelIso_twA hiso
    omega
  · rw [hX1] at hΛ'
    simp [LargeEvenInLambda2] at hΛ'

private lemma ggKacRA_nonsplit_rank_bound
    {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {labX : LargeEvenLabel} {N b : ℕ}
    (hperf : commutator X = ⊤) (hAb : Ab ≤ A) (hrank : GGTPNRank 3 X Ab)
    (hΛX : LargeEvenInLambda2 labX) (htag : labX.tag = .twA) (hX1 : labX.n = 1)
    (hN : N = labX.rank + 1) (hN3 : 3 * b = N) (hcardA : Nat.card A ≤ 3 ^ (b + 1))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : b ≤ 2 := by
  have h3N : 3 ∣ N := by rw [← hN3]; exact dvd_mul_right 3 b
  have hpq : 3 ∣ 2 ^ labX.n + 1 := by rw [hX1]; norm_num
  have hAll := largeEvenLabelAll_torusLift_twA (p := 3) hΛX htag Nat.prime_three hpq
  have hRaw := hAll (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hhX
  obtain ⟨R, hR, I, F, ⟨⟨e⟩, hT⟩⟩ := largeEvenRawDatum_exists hRaw
  letI := hR
  have hT' : GGTorusLift 3 (N - 3) R := by
    have hrankEq : ggUnitaryTorusRank 3 (labX.rank + 1) = N - 3 := by
      rw [ggUnitaryTorusRank, if_pos (by rw [← hN]; exact h3N), hN]
    rwa [hrankEq] at hT
  have hlift := ggKacRA_le_twoLocalRank_of_torusLift (r := N - 3) hT' e hperf
  obtain ⟨m, hcardAb, hrankle⟩ := hrank
  have hrm : N - 3 ≤ m + 1 := by
    have hε : (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  have hmle : m ≤ b + 1 := by
    have h3m : 3 ^ m ≤ 3 ^ (b + 1) := by
      calc 3 ^ m = Nat.card Ab := hcardAb.symm
        _ ≤ Nat.card A := Subgroup.card_le_of_le hAb
        _ ≤ 3 ^ (b + 1) := hcardA
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3m
  omega

private lemma ggKacRA_nonsplit_b_two {X : Type} [Group X] {J : Subgroup X}
    (hcor : GGTPNCorners 3 J) {labX : LargeEvenLabel} {b : ℕ} (htag : labX.tag = .twA)
    (hX1 : labX.n = 1) (hN6 : labX.rank + 1 = 6) (hb2 : b = 2)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X))
    (hlabel : ((labX.tag = .A ∨ b = 2) ∧
        LargeEvenInLambda2 ⟨.A, b - 1, 3 * labX.n⟩ ∧
        GGHasLabel ⟨.A, b - 1, 3 * labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (labX.tag = .twA ∧ 3 ≤ b ∧ LargeEvenInLambda2 ⟨.twA, b - 1, 3 * labX.n⟩ ∧
        GGHasLabel ⟨.twA, b - 1, 3 * labX.n⟩ (↥J ⧸ Subgroup.center ↥J))) : False := by
  have hlabX : labX = ⟨.twA, 5, 1⟩ := by
    cases labX with
    | mk tag rank n =>
      simp only at htag hX1 hN6 ⊢
      subst htag
      subst hX1
      have h5 : rank = 5 := by omega
      subst h5
      rfl
  rcases hlabel with ⟨-, hΛA, hJA⟩ | ⟨-, h3b, -⟩
  · have hΛA' : LargeEvenInLambda2 ⟨.A, 1, 3⟩ := by
      simpa [hb2, hX1] using hΛA
    have hJA' : GGHasLabel ⟨.A, 1, 3⟩ (↥J ⧸ Subgroup.center ↥J) := by
      simpa [hb2, hX1] using hJA
    have hhX' : GGHasLabel ⟨.twA, 5, 1⟩ (X ⧸ Subgroup.center X) := by
      rwa [hlabX] at hhX
    exact (hcor.2 rfl 1 hhX' ⟨.A, 1, 3⟩ hΛA' hJA') (Or.inl ⟨rfl, rfl⟩)
  · omega

theorem not_ggHasLabel_fieldTwo_of_ggKacRA
    (hrig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} (hloc : GGTPNLocalCore 3 A σ J) (hAb : Ab ≤ A)
    (hrank : GGTPNRank 3 X Ab) (h8 : GGTPNOnlyComp 3 σ J) (hm : GGTPNMarked 3 S A)
    (hcor : GGTPNCorners 3 J) {labJ labX : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hΛX : LargeEvenInLambda2 labX) (hRA : GGKacRA labX 3) (hX1 : labX.n = 1)
    (hJ2 : 2 ≤ labJ.n) (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    ¬ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
  intro hJ
  have htag : labX.tag = .twA := by
    rcases hRA with ⟨-, -, hdvd⟩ | h
    · rw [hX1] at hdvd
      norm_num at hdvd
    · exact h.1
  have hm' : GGTPNMarked 3 (fun _ lab => lab = labX) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  rcases split_or_fieldType_of_ggKacRA Nat.prime_three hloc h8 hRA hm' with
    ⟨a, ds, -, -, -, -, hlabel⟩ | ⟨hb2, hcardA, hlabel⟩
  · exact ggKacRA_split_label_n_eq_one hrig hΛJ hJ hJ2 htag hX1 hlabel
  ·
    set N := labX.rank + 1 with hN
    have h3N : 3 ∣ N := by
      rcases hRA with ⟨hA, -, -⟩ | ⟨-, hdvd, -⟩
      · rw [htag] at hA
        exact absurd hA (by simp)
      · exact hdvd
    set b := N / 3 with hb
    have hb2' : 2 ≤ b := by simpa [hb, hN] using hb2
    have hcardA' : Nat.card A ≤ 3 ^ (b + 1) := by simpa [hb, hN] using hcardA
    have hN3 : 3 * b = N := by
      rw [hb]
      exact Nat.mul_div_cancel' h3N
    have hble : b ≤ 2 :=
      ggKacRA_nonsplit_rank_bound hm.1 hAb hrank hΛX htag hX1 hN hN3 hcardA' hhX
    have hb_eq : b = 2 := by omega
    have hN6 : labX.rank + 1 = 6 := by omega
    exact ggKacRA_nonsplit_b_two hcor htag hX1 hN6 hb_eq hhX hlabel

theorem ggTablePKnownR_fieldTwoRA
    (hrig : GGLabelRigidInput) :
    GGTablePKnownR GGRegimeFieldTwoRA := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hJ2, hX1, -⟩, hRA⟩ := hr
  have hp3 : p = 3 := by
    rcases hRA with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · rw [hX1] at h; norm_num at h; exact absurd h hp.ne_one
    · rw [hX1] at h; norm_num at h
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  subst hp3
  obtain ⟨⟨hloc, ⟨hAb, -⟩, -, hrank, -, -, h8, hm⟩, hcor⟩ := hd
  exact (not_ggHasLabel_fieldTwo_of_ggKacRA hrig hloc hAb hrank h8 hm hcor hΛJ hΛX hRA hX1 hJ2
    hhX hhJ).elim

end CFSG.StandardType

end
