module

public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGTPNExcTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGE6TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGE6TwoLocalRank
public import CFSG.LocalAnalysis.StandardType.GGE6CoverThreeHolds
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Core
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Hard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem line_T4_bound {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X} {n : ℕ}
    (hd : GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J) (hn : n ≤ 3 ^ 5) :
    LargeEvenTwoLocalRank 3 X ≤ 4 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) := by
  obtain ⟨-, hflat, -, hrank, hnum, -, -, -⟩ := hd.1
  obtain ⟨hAbA, -, -, -⟩ := hflat
  obtain ⟨hnum1, -⟩ := hnum
  have hcardA : Nat.card A ≤ 3 ^ 4 := by
    have h35 : (3 : ℕ) ^ 5 = 3 * 3 ^ 4 := by norm_num
    have h : 3 * Nat.card A ≤ 3 * 3 ^ 4 := by rw [← h35]; exact hnum1.trans hn
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hcardAb : Nat.card Ab ≤ 3 ^ 4 := (Subgroup.card_le_of_le hAbA).trans hcardA
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm4 : m ≤ 4 := by
    rw [hmcard] at hcardAb
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcardAb
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center X)
  · rw [ite_eq_left hZ] at hmrank ⊢
    omega
  · rw [ite_eq_right hZ] at hmrank ⊢
    omega

private theorem line_three_dvd_cube {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    3 ∣ 2 ^ (3 * n) + 1 := by
  have hx : 2 ^ n % 3 = 2 := by
    have h0 := Nat.dvd_iff_mod_eq_zero.mp h
    have hlt := Nat.mod_lt (2 ^ n) (by norm_num : 0 < 3)
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by norm_num : 1 < 3)] at h0
    interval_cases hx : 2 ^ n % 3 <;> simp_all
  rw [Nat.dvd_iff_mod_eq_zero]
  have hpow : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [mul_comm 3 n, pow_mul]
  rw [hpow]
  simp only [Nat.add_mod, Nat.pow_mod, hx, Nat.mod_eq_of_lt (by norm_num : 2 < 3),
    Nat.mod_eq_of_lt (by norm_num : 1 < 3)]

private theorem line_row_twD4_E6_qp1 {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    GGTablePRow 3 (⟨.twD, 4, n⟩ : LargeEvenLabel) ⟨.E6, 0, n⟩ := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; right; right; right; right; right; right; left
  exact ⟨rfl, h, by norm_num, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

private theorem line_row_twA5_twE6 {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    GGTablePRow 3 (⟨.twA, 5, n⟩ : LargeEvenLabel) ⟨.twE6, 0, n⟩ := by
  unfold GGTablePRow
  right; right; right; right; right; right; left
  exact ⟨rfl, h, by norm_num, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

private theorem line_row_twD4_twE6 {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    GGTablePRow 3 (⟨.twD, 4, n⟩ : LargeEvenLabel) ⟨.twE6, 0, n⟩ := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; right; right; right; right; right; left
  exact ⟨rfl, h, by norm_num, Or.inr ⟨rfl, rfl⟩⟩

private theorem line_row_twA2_twE6 {n : ℕ} (h : 3 ∣ 2 ^ (3 * n) + 1) :
    GGTablePRow 3 (⟨.twA, 2, 3 * n⟩ : LargeEvenLabel) ⟨.twE6, 0, n⟩ := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; left
  exact ⟨rfl, h, by norm_num,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))⟩

theorem ggLineE6Three_holds
    (hBS : GGK0ExcBS) : GGLineE6ThreeRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨-, hn5, T, hTJ⟩, htagX, hp3, hpair⟩ := hr
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨D, hDval, ha, hb, hc, he⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  obtain ⟨hlocCore, -, -, -, -, -, honly, hmarked⟩ := hd.1
  have hperfX : commutator X = ⊤ := hmarked.1
  have hT4 := line_T4_bound hd hn5
  have hfix : ggFixSub σ = ggAutFixedSubgroup σ := by
    ext x; simp [ggFixSub, ggAutFixedSubgroup]
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    rw [hfix]
    exact hlocCore.2.2.2.1
  obtain ⟨o, ho, hqs, hdvd, hΛo, hlabo⟩ := ha J hJfix
  obtain ⟨f, hf⟩ := he
  have hEqJ : ∀ J' (hJ' : IsComponentOf J' (ggFixSub σ)), J' = J :=
    fun J' hJ' => eq_of_isComponentOf_of_ggTPNOnlyComp honly (hfix ▸ hJ') (hc J' hJ')
  haveI : Subsingleton {J' : Subgroup X // IsComponentOf J' (ggFixSub σ)} :=
    ⟨fun a b => Subtype.ext (by rw [hEqJ a.1 a.2, hEqJ b.1 b.2])⟩
  have hpos : ∀ i j : Fin D.orbits.length, D.orbits[i].qs = true →
      D.orbits[j].qs = true → i = j := by
    intro i j hi hj
    have hsub' : Subsingleton {k : Fin D.orbits.length // D.orbits[k].qs = true} := by
      constructor
      intro a b
      have h1 : f.symm a = f.symm b := Subsingleton.elim _ _
      have h2 := congrArg f h1
      simpa using h2
    have hthis : (⟨i, hi⟩ : {k : Fin D.orbits.length // D.orbits[k].qs = true}) =
        ⟨j, hj⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val hthis
  obtain ⟨Tk, tw, hty, hDmem⟩ := hDval
  have htype := ltqE6c_typeOfLabel_eq hΛX htagX
  rw [htype] at hty
  simp only [Option.some.injEq, Prod.mk.injEq] at hty
  obtain ⟨hT, htwb⟩ := hty
  subst hT
  have htw : ggKacTypeOfLabel labX = some (.E6, tw) := by rw [htype, htwb]
  have hclass : GGB36JLabel labX o.lab ∨ o.lab = labX :=
    ltqE6c_classify hΛX htagX htw hDmem ho hqs hpos hdvd
  have hiso : GGLabelIso labJ o.lab :=
    ggLabelRigidInput_holds labJ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hTo : ggResLineJLabel T o.lab := ggResLineJLabel_of_iso hTJ hiso
  rcases hclass with hGLo | heqo
  · unfold GGB36JLabel at hGLo
    rcases hGLo with ⟨hE6t, hres, -⟩ | ⟨hE6t, hres, hJ⟩ |
      ⟨hTwt, hres, hJ⟩ | ⟨hTwt, hres, hJ⟩
    ·
      by_cases hZ : 3 ∣ Nat.card (Subgroup.center X)
      · have h6 := ggE6CoverThreeLocalRank_holds X labX hΛX hE6t hres hhX hperfX hZ
        rw [ite_eq_left hZ] at hT4
        omega
      · have h5 := ggE6TorusLiftFiveRank hperfX hE6t hres hhX
        rw [ite_eq_right hZ] at hT4
        omega
    ·
      have hlabXE6 : labX = ⟨.E6, 0, labX.n⟩ := by
        rw [ltqE6c_label_eq hΛX (Or.inl hE6t), hE6t]
      rcases hJ with hJ | hJ | ⟨hn1, hJ⟩
      ·
        refine ⟨o.lab, labX, hΛo, hΛX, ?_, hlabo, hhX⟩
        rw [hJ, hlabXE6]
        exact ltqE6c_row_A5_E6_qp1 hres
      ·
        refine ⟨o.lab, labX, hΛo, hΛX, ?_, hlabo, hhX⟩
        rw [hJ, hlabXE6]
        exact line_row_twD4_E6_qp1 hres
      ·
        rw [hJ] at hiso
        exact (ltqSl_T4 ggE6TwoCenterBot_holds ggE6TwoLocalRankThree_holds hd
          (by rw [hlabXE6, hn1] at hhX; exact hhX)
          (largeEvenRawDatum_of_ggLabelIso hiso hhJ)).elim
    ·
      have hlabXTw : labX = ⟨.twE6, 0, labX.n⟩ := by
        rw [ltqE6c_label_eq hΛX (Or.inr hTwt), hTwt]
      rcases hJ with hJ | hJ
      ·
        refine ⟨o.lab, labX, hΛo, hΛX, ?_, hlabo, hhX⟩
        rw [hJ, hlabXTw]
        exact line_row_twA5_twE6 hres
      ·
        refine ⟨o.lab, labX, hΛo, hΛX, ?_, hlabo, hhX⟩
        rw [hJ, hlabXTw]
        exact line_row_twD4_twE6 hres
    ·
      have hlabXTw : labX = ⟨.twE6, 0, labX.n⟩ := by
        rw [ltqE6c_label_eq hΛX (Or.inr hTwt), hTwt]
      rcases hJ with hJ | hJ | hJ | hJ | hJ | ⟨hn1, hJ⟩
      ·
        rw [hJ] at hTo
        cases T <;> simp [ggResLineJLabel] at hTo
      ·
        rw [hJ] at hTo
        cases T <;> simp [ggResLineJLabel] at hTo
        all_goals exact (three_not_dvd_both_pow_two hTo hres).elim
      ·
        rw [hJ] at hTo
        cases T <;> simp [ggResLineJLabel] at hTo
      ·
        rw [hJ] at hTo
        cases T <;> simp [ggResLineJLabel] at hTo
      ·
        refine ⟨o.lab, labX, hΛo, hΛX, ?_, hlabo, hhX⟩
        rw [hJ, hlabXTw]
        exact line_row_twA2_twE6 (line_three_dvd_cube hres)
      ·
        rw [hJ] at hTo
        cases T <;> simp [ggResLineJLabel] at hTo
  ·
    exfalso
    rw [heqo] at hTo
    rcases htagX with h | h
    · rw [ltqE6c_label_eq hΛX (Or.inl h), h] at hTo
      cases T <;> simp [ggResLineJLabel] at hTo
    · rw [ltqE6c_label_eq hΛX (Or.inr h), h] at hTo
      cases T <;> simp [ggResLineJLabel] at hTo

end CFSG.StandardType

end
