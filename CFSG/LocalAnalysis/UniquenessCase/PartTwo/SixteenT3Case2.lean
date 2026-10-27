module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_three_or_seven_mem_sig (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h : Concl168 D V₀ V hV L) : 3 ∈ D.sig ∨ 7 ∈ D.sig := by
  have h3 : D.sig = {3} → 3 ∈ D.sig := fun e => e ▸ Set.mem_singleton 3
  have h7 : D.sig = {7} → 7 ∈ D.sig := fun e => e ▸ Set.mem_singleton 7
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (h3 h.2.2.2)
  · exact Or.inl (h3 h.2.2)
  · exact Or.inl (h3 h.2.2)
  · obtain ⟨p, r, hp, -, -, -, hpσ⟩ := h
    rcases hp with rfl | rfl
    · exact Or.inl hpσ
    · exact Or.inr hpσ
  · exact Or.inl (h3 h.2.2.2)
  · exact Or.inl (h3 h.2.2.2)
  · exact Or.inr (h7 h.2.2.2)
  · exact Or.inl (h3 h.2.2)
  · exact Or.inr (h7 h.2.2.2.2)
  · obtain ⟨p, hp, -, -, -, hσ, -⟩ := h
    rcases hp with rfl | rfl
    · exact Or.inl (h3 hσ)
    · exact Or.inr (h7 hσ)
  · exact Or.inr (h7 h.2.2.2)

theorem s16t_case167_2_of_conj_one (D : Data G) (h1217 : R1217 D) {V₀ V L K₀ : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hKL : K₀ ≤ L)
    (hK : IsL3 ↥(barSub V₀ V hV K₀) 1)
    (hnat : BinaryNaturalSL (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 3 1)
    (hdir : IsDirectProdOfConj (lBar V₀ V hV L) (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)))
    (hr : (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard = 1)
    (hs : s15 D.M V₀ V hV L = 2) (hsig : D.sig = {7}) : Case167_2 D V₀ V hV L := by
  have hLK : lBar V₀ V hV L = barSub V₀ V hV K₀ := s15_Three_eq_of_ncard_conjSet hdir hr
  have hstar : lStar D.M V₀ V hV L = barSub (v1Sub D.M V₀ V hV L) V hV K₀ :=
    (s15_Three_barSub_star_iff D h1217 h h.le (hKL.trans h.le)).1 hLK
  have hW : commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀) = wStar D.M V₀ V hV L := by
    rw [← hstar]
    exact s15_Three_commSub_top_lStar h hV
  refine ⟨?_, ?_, hs, hsig⟩
  · show IsL3 ↥(barSub V₀ V hV L) 1
    exact (congrArg (fun X : Subgroup (MulAut (Vtil V₀ V hV)) => IsL3 ↥X 1) hLK).mpr hK
  · rw [hW, ← hstar] at hnat
    exact hnat

theorem s16t_false_of_two_conj (D : Data G) {V₀ V L K₀ : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Concl168 D V₀ V hV L) (hK : IsL3 ↥(barSub V₀ V hV K₀) 1)
    (hdir : IsDirectProdOfConj (lBar V₀ V hV L) (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)))
    (hr : (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard = 2)
    (hs : s15 D.M V₀ V hV L = 1) (hsig : D.sig = {7}) : False := by
  obtain ⟨Y₁, Y₂, hne, hset⟩ := Set.ncard_eq_two.1 hr
  have hm₁ : Y₁ ∈ conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)) := by
    rw [hset]
    exact Set.mem_insert _ _
  have hm₂ : Y₂ ∈ conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)) := by
    rw [hset]
    exact Set.mem_insert_of_mem _ rfl
  have hcard : ∀ Y ∈ conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)),
      Nat.card ↥Y = 168 := by
    rintro Y ⟨n, -, rfl⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact Om8Excl.card_isL3_one hK
  have hle₁ : Y₁ ≤ lBar V₀ V hV L := hdir.1 Y₁ hm₁
  have hle₂ : Y₂ ≤ lBar V₀ V hV L := hdir.1 Y₂ hm₂
  have h3 : D.sig ≠ {3} := by
    rw [hsig]
    simp
  rcases hc with h | h | h | h | h | h | h | h | h | h | h
  · exact h3 h.2.2.2
  · exact h3 h.2.2
  · exact h3 h.2.2
  · obtain ⟨p, r, hp, -, hL, -, hpσ⟩ := h
    have hp7 : p = 7 := by
      rcases hp with rfl | rfl
      · rw [hsig] at hpσ
        simp at hpσ
      · rfl
    subst hp7
    have hdvd : Nat.card ↥Y₁ ∣ Nat.card ↥(lBar V₀ V hV L) := Subgroup.card_dvd_of_le hle₁
    rw [hcard Y₁ hm₁, s16c167_card_isElemAbelianOfRank hL] at hdvd
    have h2 : 2 ∣ 7 ^ r := (by norm_num : 2 ∣ 168).trans hdvd
    have := Nat.prime_two.dvd_of_dvd_pow h2
    omega
  · exact h3 h.2.2.2
  · exact h3 h.2.2.2
  · obtain ⟨-, hL3, -, -⟩ := h
    have hcL := Om8Excl.card_isL3_one hL3
    have e₁ : Y₁ = lBar V₀ V hV L :=
      Subgroup.eq_of_le_of_card_ge hle₁ (by rw [hcard Y₁ hm₁, hcL])
    have e₂ : Y₂ = lBar V₀ V hV L :=
      Subgroup.eq_of_le_of_card_ge hle₂ (by rw [hcard Y₂ hm₂, hcL])
    exact hne (e₁.trans e₂.symm)
  · exact h3 h.2.2
  · have := h.2.2.1
    omega
  · obtain ⟨p, -, -, -, h2, -, -⟩ := h
    omega
  · have := h.2.2.1
    omega

private theorem s16t_mul_eq_two {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (h : r * s = 2) :
    (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) := by
  have hr2 : r ≤ 2 := by nlinarith
  have hs2 : s ≤ 2 := by nlinarith
  interval_cases r <;> interval_cases s <;> omega

theorem s16t_false_of_case153_2 (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (h : Case153_2 D ⊥ V hV L) :
    False := by
  obtain ⟨K₀, p, hKL, hshape, hdir, hsig, -, hrs, hrs1⟩ := h
  haveI : Finite (MulAut (Vtil ⊥ V hV)) := MulEquiv.finite_left
  have hmSub : mSub (⊥ : Subgroup G) = 0 := rk_bot
  have hr1 : 0 < (conjSet (barSub ⊥ V hV K₀)
      (Mbar D.M ⊥ V hV ⊓ normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _))).ncard := by
    refine (Set.ncard_pos (Set.toFinite _)).2 ⟨barSub ⊥ V hV K₀, 1, Subgroup.one_mem _, ?_⟩
    ext x
    simp
  have hs1 : 0 < s15 D.M ⊥ V hV L := by
    refine (Set.ncard_pos (Set.toFinite _)).2 ⟨barSub ⊥ V hV L, 1, Subgroup.one_mem _, ?_⟩
    ext x
    simp
  have hrs2 : (conjSet (barSub ⊥ V hV K₀)
      (Mbar D.M ⊥ V hV ⊓ normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _))).ncard *
      s15 D.M ⊥ V hV L = 2 := by
    have hpos := Nat.mul_pos hr1 hs1
    by_contra hne
    have h1 : (conjSet (barSub ⊥ V hV K₀)
        (Mbar D.M ⊥ V hV ⊓ normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _))).ncard *
        s15 D.M ⊥ V hV L = 1 := by omega
    have := hrs1 h1
    rw [hmSub] at this
    omega
  rcases hshape with ⟨rfl, -, -⟩ | ⟨rfl, hK, hnat⟩
  · rcases s16t_three_or_seven_mem_sig D hc.concl168 with h3 | h7
    · rw [hsig] at h3
      simp at h3
    · rw [hsig] at h7
      simp at h7
  · rcases s16t_mul_eq_two hr1 hs1 hrs2 with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · exact hc.not_concl (Or.inr (Or.inl
        (s16t_case167_2_of_conj_one D h1217 hc.setting.hyp151 hV hKL hK hnat hdir hr hs hsig)))
    · exact s16t_false_of_two_conj D hc.concl168 hK hdir hr hs hsig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
