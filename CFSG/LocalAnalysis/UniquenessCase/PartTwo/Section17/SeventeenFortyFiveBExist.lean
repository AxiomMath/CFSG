module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveANormT
public import CFSG.LocalAnalysis.WeakClosure81.InFDihedralFrobenius
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveCaseThree
public import CFSG.Quasithin.Background.SmithD321SzK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_45_ABTStructure (D : Data G) : Prop :=
  ∀ (V₀ V L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
    (A₀ A : Subgroup G) (y : G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X →
    (F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X) →
    CFSG.ABGLocalTools.IsSylowOf r A X → Permutes A D.T →
    GapWitness D X p y → ⁅A, Subgroup.zpowers y⁆ = A →
    A ≤ Subgroup.zpowers y ⊔ normalizer (D.T : Set G) →
    Gap17_45_BorelData D X p r →
    ∃ (R : Subgroup (Bar2 (A ⊔ Subgroup.zpowers y ⊔ D.T)))
      (b t : Bar2 (A ⊔ Subgroup.zpowers y ⊔ D.T)),
      R.Normal ∧ IsMulCommutative R ∧ IsPGroup r R ∧ orderOf b = p ∧ orderOf t = 2 ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (Subgroup.zpowers t) ⊤ ∧
        t * b * t⁻¹ = b⁻¹ ∧ ⁅R, Subgroup.zpowers b⁆ = R ∧
        R ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers t = ⊤

theorem gap17_45_inFSqAB {D : Data G} {V₀ V L X : Subgroup G} {p n l r : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} {x : G} {A₀ A : Subgroup G} {y : G}
    (hstruct : Gap17_45_ABTStructure D)
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h8100 : F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T)
    (hy : GapWitness D X p y) (hAB : ⁅A, Subgroup.zpowers y⁆ = A)
    (hANT : A ≤ Subgroup.zpowers y ⊔ normalizer (D.T : Set G))
    (hdata : Gap17_45_BorelData D X p r) :
    Gap17_45_InFSq A (Subgroup.zpowers y) D.T := by
  obtain ⟨R, b, t, hRnorm, hRabel, hRr, hb, ht, hSyl, htb, hcomm, hgen⟩ :=
    hstruct V₀ V L X p n l r C Dc Gamma x A₀ A y ctx h8100 hc hAsyl hAT hy hAB hANT hdata
  obtain ⟨-, -, hshapeN, hr, hrdvd, -, -, -, -, -⟩ := h8100
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshapeN 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hrdvd
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have hn0 : n ≠ 0 := by
    intro hn
    rw [hn] at hshape0
    rcases hshape0 with hL2 | hSz
    · have hcard := card_of_isL2 hL2
      norm_num at hcard
      exact Nat.card_pos.ne' hcard
    · have h3 := (CFSG.Quasithin.SmithD321.odd_of_isSz
        (CFSG.Blueprint.LieModel.suzukiModel hSz).2).2
      omega
  have hpowodd : Odd (2 ^ n - 1) := by
    have h2 : Even (2 ^ n) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      exact ⟨2 ^ k, by rw [pow_succ']; ring⟩
    exact Nat.Even.sub_odd Nat.one_le_two_pow h2 (by norm_num)
  have hr2 : r ≠ 2 := by
    intro h
    have hdvd : 2 ∣ 2 ^ n - 1 := h ▸ hrdvd
    exact (Nat.not_even_iff_odd.mpr hpowodd) (even_iff_two_dvd.mpr hdvd)
  exact CFSG.LocalAnalysis.WeakClosure81.inF_one_of_dihedral_frobenius hr hr2 hp hp2
    hRnorm hRabel hRr hb ht hSyl htb hcomm hgen

theorem eq_five_of_isSz_five {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : IsSz X n) (h5 : IsSz X 5) : n = 5 := by
  obtain ⟨-, hn3⟩ := CFSG.Quasithin.SmithD321.odd_of_isSz
    (CFSG.Blueprint.LieModel.suzukiModel hn).2
  have hcard : Nat.card X = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) :=
    CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel hn).2
  have h5card : Nat.card X = 32537600 := by
    rw [CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel h5).2]
    norm_num
  have hdvd : 2 ^ (2 * n) ∣ Nat.card X := by
    rw [hcard, show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul]; ring_nf]
    exact ⟨((2 ^ n) ^ 2 + 1) * (2 ^ n - 1), by ring⟩
  have hdvd' : 2 ^ (2 * n) ∣ 32537600 := by
    rwa [← h5card]
  have h2n : 2 * n ≤ 10 := by
    by_contra h
    have h11 : 11 ≤ 2 * n := by omega
    have h211 : 2 ^ 11 ∣ 2 ^ (2 * n) := Nat.pow_dvd_pow 2 h11
    exact (by norm_num : ¬ 2 ^ 11 ∣ 32537600) (h211.trans hdvd')
  have hnle : n ≤ 5 := by omega
  interval_cases n <;> norm_num at hcard h5card <;> omega

theorem s17_45_b_exists {D : Data G} {V₀ V L X : Subgroup G} {p n l r : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} {x : G} {A₀ : Subgroup G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h8100 : F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X)
    (hrank : CFSG.Open.pRank p (F08.CentOverO2 D.M X) ≤ 1)
    (hy : ∃ y ∈ D.M, y ∉ X ⊔ F08.CentOverO2 D.M X ∧ orderOf y = p)
    (hK : CFSG.Open.IsKGroup ↥D.M)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hdata : Gap17_45_BorelData D X p r) :
    ∃ A : Subgroup G, ∃ y : G, CFSG.ABGLocalTools.IsSylowOf r A X ∧ Permutes A D.T ∧
      GapWitness D X p y ∧ Nat.card (Subgroup.zpowers y) = p ∧
      Subgroup.zpowers y ≤ D.M ∧ Permutes (Subgroup.zpowers y) D.T ∧
      ⁅A, Subgroup.zpowers y⁆ = A ∧
      A ≤ Subgroup.zpowers y ⊔ normalizer (D.T : Set G) := by
  classical
  obtain ⟨-, -, hshapeN, hr, hrdvd, -, -, -, -, -⟩ := h8100
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshapeN 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hrdvd
  have hrdvd' : r ∣ 2 ^ n - 1 := hrdvd
  rcases hc with h3 | h4
  · obtain ⟨-, hL2raw, hp3, -, φ, hφ, hker⟩ := h3
    have hL2 : IsL2 (Bar2 L) 3 := hL2raw
    subst p
    have hn3 : n = 3 := by
      rcases hshape0 with hN | hN
      · exact isL2_field_unique hN hL2
      · exact (P2214S.false_of_isSz_of_isL2 hN hL2).elim
    have hr7 : r = 7 := by
      have hdvd7 : r ∣ 7 := by simpa [hn3] using hrdvd'
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h | h
      · exact absurd h hr.ne_one
      · exact h
    exact s17_45_exists_B_le' ctx (Or.inl ⟨hL2, rfl, hr7⟩) φ hφ hker hrank hy hK hKF hdata
  · obtain ⟨-, hSzraw, hp5, -, φ, hφ, hker⟩ := h4
    have hSz : IsSz (Bar2 L) 5 := hSzraw
    subst p
    have hn5 : n = 5 := by
      rcases hshape0 with hN | hN
      · exact (P2214S.false_of_isSz_of_isL2 hSz hN).elim
      · exact eq_five_of_isSz_five hN hSz
    have hr31 : r = 31 := by
      have hdvd31 : r ∣ 31 := by simpa [hn5] using hrdvd'
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd31 with h | h
      · exact absurd h hr.ne_one
      · exact h
    exact s17_45_exists_B_le' ctx (Or.inr ⟨hSz, rfl, hr31⟩) φ hφ hker hrank hy hK hKF hdata

@[expose] def Gap17_45_BorelDataCtx (D : Data G) : Prop :=
  ∀ (V₀ V L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
    (A₀ : Subgroup G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X →
    (F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X) →
    Gap17_45_BorelData D X p r

@[expose] def Gap17_45_PRanCtxAt (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
    (A₀ : Subgroup G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X →
    (F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X) →
    CFSG.Open.pRank p (F08.CentOverO2 D.M X) ≤ 1 ∧
      CFSG.Open.pRank p (X ⊔ F08.CentOverO2 D.M X) ≤ 3

theorem gap17_45_orderP (D : Data G) (hx : DataExt D) {V₀ V : Subgroup G}
    (hPRan : Gap17_45_PRanCtxAt D V₀ V) :
    ∀ (L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
      (A₀ : Subgroup G),
    Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X →
    (F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X) →
    ∃ y ∈ D.M, y ∉ X ⊔ F08.CentOverO2 D.M X ∧ orderOf y = p := by
  intro L X p n l r C Dc Gamma x A₀ ctx h8100 hc
  obtain ⟨-, hrankN⟩ := hPRan L X p n l r C Dc Gamma x A₀ ctx h8100 hc
  obtain ⟨-, -, -, -, -, hpSig, -, -, -, -⟩ := h8100
  have hp : p.Prime := (D.sig_prime p hpSig).1
  have hG4 : 3 < CFSG.Open.evenRank G := by
    rcases hc with h | h
    · exact h.2.2.2.1
    · exact h.2.2.2.1
  have h4 : 4 ≤ CFSG.Open.pRank p D.M := hx.four_le (by omega) p hpSig
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt D.M
  have hEN : ¬ E ≤ X ⊔ F08.CentOverO2 D.M X := by
    intro hle
    have hle' : CFSG.Open.pRank p D.M ≤ CFSG.Open.pRank p (X ⊔ F08.CentOverO2 D.M X) :=
      CFSG.SectionRank.le_pRank hp.one_lt hle hEel hEcard
    omega
  have hy : ∃ y, y ∈ E ∧ y ∉ X ⊔ F08.CentOverO2 D.M X := by
    by_contra h
    push Not at h
    exact hEN h
  obtain ⟨y, hyE, hyN⟩ := hy
  have hy1 : y ≠ 1 := by
    intro h
    exact hyN (h ▸ (X ⊔ F08.CentOverO2 D.M X).one_mem)
  have hypow : y ^ p = 1 := hEel.2 y hyE
  exact ⟨y, hEM hyE, hyN, @orderOf_eq_prime G _ y p ⟨hp⟩ hypow hy1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
