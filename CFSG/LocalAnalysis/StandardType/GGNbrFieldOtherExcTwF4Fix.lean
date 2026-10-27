module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwF4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

theorem twF4Fix_fixStd
    {a : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ (2 * a + 1) / p) :
    GGRawFieldFixStd p ⟨.twF4, 0, (2 * a + 1) / p⟩ (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  intro hs hna f hf hord
  have ha : 1 ≤ a := by
    have := Nat.div_le_self (2 * a + 1) p
    omega
  have hF : FQ.InnFree p (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) :=
    Y10GField.innFree_of_ggRawInnField (RawAutReeF4.ggRawInnField_twF4_of_diag ha hK
      (ggTwistedF4DiagInput_holds a ha K hK hs) hp.one_lt.ne') hs hna
  obtain ⟨b, hbp, k, _, _, _, hk, ⟨φ⟩⟩ :=
    FR.exists_fixSub_equiv_reeGamma ha hK hp hp2 _ hF f hf hord
  have hdiv : (2 * a + 1) / p = 2 * b + 1 := by rw [← hbp, Nat.mul_div_cancel _ hp.pos]
  have hb : 1 ≤ b := by omega
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma hb hk
  obtain ⟨hs₀, hna₀⟩ := Y10GField.twF4Quot_simple hb hk
  dsimp only [LargeEvenRawDatum]
  rw [show ((2 * a + 1) / p - 1) / 2 = b by omega]
  exact ⟨k, inferInstance, inferInstance, hk, hs₀, hna₀,
    ggFixGeom_of_inn hna₀ (center_eq_bot_of_simple_nonabelian hna)
      (chevIDImage_subset_inn_twF4 ha K hK) (by rintro _ ⟨r, rfl⟩; exact conj_mem_chevIDImage _ r)
      ((eR.trans φ.symm).trans (MulEquiv.subgroupCongr (Y10GField.ggFixSub_eq_fixSub f).symm))⟩

theorem ggFieldFixKnown_twF4 :
    GGFieldFixKnown fun p lab => lab.tag = .twF4 ∧ 3 ≤ lab.n / p := by
  intro p lab hp hp2 hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, h3⟩ := hS
  dsimp only at ht h3
  subst ht
  dsimp only [LargeEvenInLambda2] at hlab
  obtain ⟨-, rfl, ⟨a, rfl⟩, -⟩ := hlab
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [show (2 * a + 1 - 1) / 2 = a by omega] at hQ ⊢
  exact recipeTwF4_and (fun K _ _ hK => twF4Fix_fixStd hK hp hp2 h3) hQ

end CFSG.StandardType

end
