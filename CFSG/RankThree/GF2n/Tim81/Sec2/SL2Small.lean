module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Quasithin.Background.SmithB45L2Herm
public import CFSG.Timmesfeld.Bridge.RootStructR2HigmanIrr

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.B45L2 CFSG.Timmesfeld.Bridge.Higman
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[expose] def IsOrthModule {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))
    (ρ : Representation (ZMod 2) SL(2, F) W) : Prop :=
  ∃ (j : ℕ) (β : W ≃+ ↥(CFSG.Quasithin.JonesParshall.hermA l F)), ∀ g w,
    β (ρ g w) =
      CFSG.Quasithin.JonesParshall.hermAct l
        (CFSG.Quasithin.JonesParshall.sig_sig hF) (fieldAut F j g) (β w)

private theorem four_mul_le_two_pow {k : ℕ} (hk : 4 ≤ k) : 4 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have h2 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith

private theorem eq_one_of_two_pow_lt_four {k : ℕ} (hk : 1 ≤ k) (h : 2 ^ k < 4) : k = 1 := by
  by_contra hne
  have h2 : 2 ≤ k := Nat.succ_le_of_lt (lt_of_le_of_ne hk (Ne.symm hne))
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2
  exact (not_le_of_gt h) h4

private theorem dvd_of_shift_card_one {n d : ℕ} {J : Finset ℕ} (hJ : J.card = 1)
    (hJn : ∀ i ∈ J, i < n) (hshift : J.image (fun i => (i + d) % n) = J) : n ∣ d := by
  classical
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
  have hj : j < n := hJn j (Finset.mem_singleton_self j)
  have hjd : (j + d) % n = j := by
    simpa using hshift
  have h1 : (j + d) % n = (j + 0) % n := by
    rw [hjd, add_zero, Nat.mod_eq_of_lt hj]
  exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j h1)

private theorem eq_two_mul_of_shift_card_two {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) {J : Finset ℕ}
    (hJ : J.card = 2) (hJne : J.Nonempty) (hJn : ∀ i ∈ J, i < n)
    (hshift : J.image (fun i => (i + d) % n) = J) (hlt : d < n) : n = 2 * d := by
  classical
  set g := Nat.gcd n d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d hn
  have hgd : g ≤ d := Nat.le_of_dvd hd (Nat.gcd_dvd_right n d)
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgle := le_card_mul_gcd_of_shift hn hJne hJn hshift
  rw [hJ] at hgle
  have hge : g = d := by
    by_contra hne
    have hltgd : g < d := lt_of_le_of_ne hgd hne
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_right n d
    have ht1 : 1 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · rw [h0, mul_zero] at ht
        omega
      · rcases Nat.lt_or_ge t 2 with h | h
        · have ht' : t = 1 := by omega
          rw [ht', mul_one] at ht
          omega
        · exact h
    have h2g : 2 * g ≤ d := by
      rw [ht]
      nlinarith [hg0]
    omega
  have hdn : d ∣ n := by
    rw [← hge]
    exact hgn
  obtain ⟨m, hm⟩ := hdn
  have hm1 : 1 < m := by
    by_contra hmle
    push Not at hmle
    have : d * m ≤ d * 1 := Nat.mul_le_mul_left d hmle
    rw [← hm, mul_one] at this
    omega
  have hm2 : m ≤ 2 := by
    have : d * m ≤ d * 2 := by
      rw [← hm]
      omega
    exact Nat.le_of_mul_le_mul_left this hd
  have hm3 : m = 2 := by omega
  rw [hm, hm3]
  ring

private theorem eq_three_mul_of_shift_card_three {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) {J : Finset ℕ}
    (hJ : J.card = 3) (hJne : J.Nonempty) (hJn : ∀ i ∈ J, i < n)
    (hshift : J.image (fun i => (i + d) % n) = J) (hlt : 2 * d < n) : n = 3 * d := by
  classical
  set g := Nat.gcd n d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d hn
  have hgd : g ≤ d := Nat.le_of_dvd hd (Nat.gcd_dvd_right n d)
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgle := le_card_mul_gcd_of_shift hn hJne hJn hshift
  rw [hJ] at hgle
  have hge : g = d := by
    by_contra hne
    have hltgd : g < d := lt_of_le_of_ne hgd hne
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_right n d
    have ht1 : 1 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · rw [h0, mul_zero] at ht
        omega
      · rcases Nat.lt_or_ge t 2 with h | h
        · have ht' : t = 1 := by omega
          rw [ht', mul_one] at ht
          omega
        · exact h
    have h2g : 2 * g ≤ d := by
      rw [ht]
      nlinarith [hg0]
    omega
  have hdn : d ∣ n := by
    rw [← hge]
    exact hgn
  obtain ⟨m, hm⟩ := hdn
  have hm1 : 2 < m := by
    by_contra hmle
    push Not at hmle
    have : d * m ≤ d * 2 := Nat.mul_le_mul_left d hmle
    rw [← hm] at this
    omega
  have hm2 : m ≤ 3 := by
    have : d * m ≤ d * 3 := by
      rw [← hm]
      omega
    exact Nat.le_of_mul_le_mul_left this hd
  have hm3 : m = 3 := by omega
  rw [hm, hm3]
  ring

private theorem card_le_three_of_shift {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) {J : Finset ℕ}
    (hJne : J.Nonempty) (hJn : ∀ i ∈ J, i < n)
    (hshift : J.image (fun i => (i + d) % n) = J)
    (hlt : d * 2 ^ J.card < 4 * n) : J.card ≤ 3 := by
  have hkg := le_card_mul_gcd_of_shift hn hJne hJn hshift
  have hgd : Nat.gcd n d ≤ d := Nat.le_of_dvd hd (Nat.gcd_dvd_right n d)
  by_contra hk
  push Not at hk
  have h4k : 4 * J.card ≤ 2 ^ J.card := four_mul_le_two_pow hk
  have h1 : d * 2 ^ J.card < d * (4 * J.card) := by
    calc d * 2 ^ J.card < 4 * n := hlt
      _ ≤ 4 * (J.card * d) :=
        Nat.mul_le_mul_left 4 (hkg.trans (Nat.mul_le_mul_left J.card hgd))
      _ = d * (4 * J.card) := by ring
  have h2 : d * (4 * J.card) ≤ d * 2 ^ J.card := Nat.mul_le_mul_left d h4k
  omega

theorem card_fixedSub_eq_card_endRing (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ n) :
    Nat.card (fixedSub ρ A) = Nat.card (EndRing ρ) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨_, _, _, _, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, _⟩ := hdesc b
  have h := card_fixed_eq_of_card ρ hF b ιF ιD J hJn Φ A hA2 hA
  simpa [fixedSub] using h

theorem isNaturalModule_of_dvd {d : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (hD : Nat.card (EndRing ρ) = 2 ^ d)
    (hdim : Module.finrank (EndRing ρ) W = 2) (hnd : n ∣ d) :
    IsNaturalModule ρ := by
  have hdn : d = n := eq_of_finrank_eq_two hn hF ρ hnt hD hdim hnd
  rw [hdn] at hD
  exact exists_natural_iso hn hF ρ hnt hD hdim

theorem isNaturalModule_of_card_lt (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ n)
    (h : Nat.card W < Nat.card (fixedSub ρ A) ^ 4) : IsNaturalModule ρ := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨_, _, _, _, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  have hfix := card_fixedSub_eq_card_endRing hn hF ρ hnt A hA2 hA
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdim, ← pow_mul]
  have hk1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hfix' : Nat.card (fixedSub ρ A) ^ 4 = 2 ^ (d * 4) := by
    rw [hfix, hDcard, ← pow_mul]
  have hk : J.card = 1 := by
    rw [hWcard, hfix'] at h
    have h' : d * 2 ^ J.card < d * 4 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
    exact eq_one_of_two_pow_lt_four hk1 (by
      by_contra hge
      push Not at hge
      have hle : d * 4 ≤ d * 2 ^ J.card := Nat.mul_le_mul_left d hge
      omega)
  have hdim2 : Module.finrank (EndRing ρ) W = 2 := by rw [hdim, hk]; rfl
  have hnd : n ∣ d := dvd_of_shift_card_one hk hJn hshift
  exact isNaturalModule_of_dvd hn hF ρ hnt hDcard hdim2 hnd

theorem isNaturalModule_or_isOrthModule_or_of_card_lt (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = 2 ^ n)
    (h : Nat.card W < 2 ^ (4 * n)) :
    IsNaturalModule ρ ∨
      (∃ l, ∃ hl : Fintype.card F = 2 ^ (2 * l), n = 2 * l ∧ IsOrthModule hl ρ) ∨
      (∃ l, n = 3 * l ∧ Nat.card W = 2 ^ (8 * l) ∧
        Nat.card (fixedSub ρ A) = 2 ^ l) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨_, _, _, _, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdim, ← pow_mul]
  have hdlt : d * 2 ^ J.card < 4 * n := by
    rw [hWcard] at h
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hk1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hk3 : J.card ≤ 3 :=
    card_le_three_of_shift (by omega) hd1 hJne hJn hshift hdlt
  have hcases : J.card = 1 ∨ J.card = 2 ∨ J.card = 3 := by omega
  rcases hcases with hk | hk | hk
  · left
    have hdim2 : Module.finrank (EndRing ρ) W = 2 := by rw [hdim, hk]; rfl
    have hnd : n ∣ d := dvd_of_shift_card_one hk hJn hshift
    exact isNaturalModule_of_dvd hn hF ρ hnt hDcard hdim2 hnd
  · right; left
    have hdim4 : Module.finrank (EndRing ρ) W = 4 := by rw [hdim, hk]; rfl
    have hdn : d < n := by
      have h' := hdlt
      rw [hk] at h'
      norm_num at h'
      omega
    have hn2d : n = 2 * d :=
      eq_two_mul_of_shift_card_two (by omega) hd1 hk hJne hJn hshift hdn
    have hF2 : Fintype.card F = 2 ^ (2 * d) := by rw [hF, hn2d]
    obtain ⟨j, β, hβ⟩ := orth_iso hd1 hF2 ρ hnt hDcard hdim4
    exact ⟨d, hF2, hn2d, j, β, hβ⟩
  · right; right
    have hdim8 : Module.finrank (EndRing ρ) W = 8 := by rw [hdim, hk]; norm_num
    have h2dn : 2 * d < n := by
      have h' := hdlt
      rw [hk] at h'
      norm_num at h'
      omega
    have hn3d : n = 3 * d :=
      eq_three_mul_of_shift_card_three (by omega) hd1 hk hJne hJn hshift h2dn
    refine ⟨d, hn3d, ?_, ?_⟩
    · rw [hWcard, hk]
      norm_num
      rw [mul_comm]
    · rw [card_fixedSub_eq_card_endRing hn hF ρ hnt A hA2 hA, hDcard]

end CFSG.RankThree.GF2n.Tim81.Sec2

end
