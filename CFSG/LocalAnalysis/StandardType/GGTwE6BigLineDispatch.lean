module

public import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1D4
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1A5
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1Mark

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.SCFourCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

private theorem ggTwE6BigD_of_mark_omega {lab : LargeEvenLabel}
    (ht : markTag lab = .POmegaPlus) (hr : markRank lab = 4) (hd : markDeg lab = 1) :
    GGTwE6BigLabel lab := by
  obtain ⟨t, r, m⟩ := lab
  cases t <;> dsimp only [markTag, markRank, markDeg] at ht hr hd
  case D =>
    by_cases h3 : r = 3
    · rw [if_pos h3] at ht
      exact absurd ht (by decide)
    · rw [if_neg h3] at hr
      subst hr hd
      exact Or.inl rfl
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

private theorem ggTwE6BigD_of_mark_triD4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : markTag lab = .trialityD4) (hd : markDeg lab = 1) : GGTwE6BigLabel lab := by
  obtain ⟨t, r, m⟩ := lab
  cases t <;> dsimp only [markTag, markDeg] at ht hd
  case triD4 =>
    have hr : r = 0 := hlab.2
    subst hr hd
    exact Or.inr (Or.inl rfl)
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

private theorem ggTwE6BigD_of_mark_PSU6 {lab : LargeEvenLabel}
    (ht : markTag lab = .PSU) (hc : markChar lab = 2) (hr : markRank lab = 6)
    (hd : markDeg lab = 1) : GGTwE6BigLabel lab := by
  obtain ⟨t, l, m⟩ := lab
  cases t <;> dsimp only [markTag, markRank, markChar, markDeg] at ht hc hr hd
  case twA =>
    obtain rfl : l = 5 := by omega
    subst hd
    exact Or.inr (Or.inr (Or.inl rfl))
  case twD =>
    split_ifs at ht hr <;> first | exact absurd ht (by decide) | omega
  case G2der => exact absurd hc (by decide)
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

private theorem ggTwE6BigD_marking_omega
    {X : Type} [Group X] (hX : commutator X = ⊤)
    (h : LieModel (X ⧸ Subgroup.center X) .POmegaPlus 4 2 1) :
    LargeEvenMarking X fun lab' _ _ _ _ _ => GGTwE6BigLabel lab' := by
  obtain ⟨hX', lab, hlab, hraw⟩ := largeEvenMarking_of_lieModel_centerQuot hX h
  refine ⟨hX', lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ht, hr, hc, hf⟩
  exact ⟨hs, hna, θ, ggTwE6BigD_of_mark_omega ht hr hf⟩

private theorem ggTwE6BigD_marking_triD4
    {X : Type} [Group X] (hX : commutator X = ⊤)
    (h : LieModel (X ⧸ Subgroup.center X) .trialityD4 0 2 1) :
    LargeEvenMarking X fun lab' _ _ _ _ _ => GGTwE6BigLabel lab' := by
  obtain ⟨hX', lab, hlab, hraw⟩ := largeEvenMarking_of_lieModel_centerQuot hX h
  refine ⟨hX', lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ht, hr, hc, hf⟩
  exact ⟨hs, hna, θ, ggTwE6BigD_of_mark_triD4 hlab ht hf⟩

private theorem ggTwE6BigD_marking_PSU6
    {X : Type} [Group X] (hX : commutator X = ⊤)
    (h : LieModel (X ⧸ Subgroup.center X) .PSU 6 2 1) :
    LargeEvenMarking X fun lab' _ _ _ _ _ => GGTwE6BigLabel lab' := by
  obtain ⟨hX', lab, hlab, hraw⟩ := largeEvenMarking_of_lieModel_centerQuot hX h
  refine ⟨hX', lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ht, hr, hc, hf⟩
  exact ⟨hs, hna, θ, ggTwE6BigD_of_mark_PSU6 ht hc hr hf⟩

theorem ggTwE6BigLineLabels_of
    (h24 : GGTwE6BigThreeA2) (h28 : GGTwE6BigA4A1)
    (h46 : GGTwE6BigD5) : GGTwE6BigLineLabels := by
  intro K _ _ σ hK hσ h hh1 hh3 E hE hcard hfE hEI hnt J hJ
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twE6_conj_injective K σ 2 hσ hK2 (le_refl 2)
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ hK2 (le_refl 2) h hh1 hh3
  have he : D.e = 1 := by
    have h1 : 2 ^ 1 = ringChar K ^ D.e := by rw [pow_one]; exact D.hqe
    rw [hchar] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  obtain ⟨i, hqs, hJi⟩ := D.exists_rationalComponent hJ
  have hP := hqs.1.commutator_eq_top
  let eJ := (J.equivMapOfInjective D.ι D.hinj).trans (MulEquiv.subgroupCongr hJi)
  have hmem := twE6MatFixDim_mem_of_pow_three hK3 hh3 hh1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hd24 | hd28 | hd30 | hd36 | hd46
  · exact (h24 K σ hK hσ h hh1 hh3 hd24 E hE hcard hfE hEI hnt J hJ).elim
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ hl => Or.inr (Or.inr (Or.inr (Or.inl hl))))
      (h28 K σ hK hσ h hh1 hh3 hd28 J hJ)
  · rcases lieModel_rationalComponent_d4t2 D (by norm_num) hd30 i with hm | hm
    · rw [hchar, he] at hm
      exact largeEvenMarking_of_mulEquiv eJ (ggTwE6BigD_marking_omega hP hm)
    · rw [hchar, he] at hm
      exact largeEvenMarking_of_mulEquiv eJ (ggTwE6BigD_marking_triD4 hP hm)
  · have hm := statedClassicalModel_rationalComponent_a5t1 D (by norm_num) hd36 i
    rw [hchar, he] at hm
    exact largeEvenMarking_of_mulEquiv eJ
      (ggTwE6BigD_marking_PSU6 hP (Or.inl ⟨by decide, hm⟩))
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ hl => Or.inr (Or.inr (Or.inr (Or.inr hl))))
      (h46 K σ hK hσ h hh1 hh3 hd46 J hJ)

end CFSG.StandardType

end
