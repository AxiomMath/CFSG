module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneB1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneB2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneB3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneB4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SectionRank.ClassicalEven

variable {W : Type} [CommGroup W]

private instance s16h_finite_mulAut [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => (f : W → W)) (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_H5_sumOfNat_one {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hZ : Z ≤ U) (hN : N L U Z) :
    SumOfNat N L U Z 1 := by
  refine ⟨fun _ => U, ?_, ?_, ?_, ?_⟩
  · intro i; exact hZ
  · intro i
    have hsup : (⨆ (j : Fin 1) (_ : j ≠ i), U) = ⊥ := by
      rw [iSup_eq_bot]
      intro j
      rw [iSup_eq_bot]
      intro hji
      exact (hji (Subsingleton.elim j i)).elim
    rw [hsup, sup_bot_eq]
    exact inf_le_right
  · rw [iSup_const]
    exact sup_eq_right.mpr hZ
  · intro i; exact hN

private theorem s16h_H5_false_of_oddRankTwo [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) (h : CFSG.Quasithin.A3Facts.OddRankTwo ↥L) :
    False := by
  obtain ⟨q, hq, hq2, h2⟩ := h
  have h3 : CFSG.Open.pRank q (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hc.thin q hq hq2
  omega

private theorem s16h_H5_mQuot_le_three [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W}
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) :
    E3.mQuot (commSub (commSub ⊤ L) (Subgroup.zpowers t) ⊔ (commSub ⊤ L ⊓ fixV L))
      (commSub ⊤ L ⊓ fixV L) ≤ 3 := by
  set A : Subgroup W := commSub (commSub ⊤ L) (Subgroup.zpowers t)
  set U : Subgroup W := commSub ⊤ L ⊓ fixV L
  have hAU : A ≤ commSub ⊤ (Subgroup.zpowers t) := commSub_mono le_top le_rfl
  have hkey : E3.mQuot (A ⊔ U) U = E3.mQuot A (A ⊓ U) := by
    unfold E3.mQuot
    rw [Subgroup.relIndex_sup_right (H := A) (K := U),
      show A ⊓ U = U ⊓ A from inf_comm A U, Subgroup.inf_relIndex_right]
  calc E3.mQuot (A ⊔ U) U = E3.mQuot A (A ⊓ U) := hkey
    _ ≤ E3.mQuot A ⊥ := E3.mQuot_mono bot_le
    _ = rk ↥A := by unfold E3.mQuot rk; rw [Subgroup.relIndex_bot_left]
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono hAU
    _ ≤ 3 := htr

private theorem s16h_H5_two_le_pRank_three_of_rotGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {H : Subgroup (GL ι K)} {e : Fin 2 ⊕ Fin 2 → ι}
    (he : Function.Injective e) (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ∀ a b : Fin 2 ⊕ Fin 2, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  refine CFSG.Quasithin.A3Facts.two_le_pRank_of_gens (x := ⟨_, hH 0⟩) (y := ⟨_, hH 1⟩) ?_ ?_
    ?_ ?_ ?_
  · exact Subtype.ext (rotGL_pow_three _ _)
  · exact Subtype.ext (rotGL_pow_three _ _)
  · apply Subtype.ext
    exact (rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide))).eq
  · intro h
    have h1 : rotGL (e (.inl 0)) (e (.inr 0)) = 1 := congrArg Subtype.val h
    exact (mul_scalar_ne (g := 1) (c := 1) (h := rotGL (e (.inl 0)) (e (.inr 0)))
      (a := e (.inl 0)) (b := e (.inr 0)) (hne _ _ (by decide)) (Matrix.one_mulVec _)
      (rotMatrix_mulVec_left _ _) (Subgroup.one_mem _)) (by rw [h1, mul_one])
  · intro m h
    have h1 : (rotGL (e (.inl 0)) (e (.inr 0))) ^ m = rotGL (e (.inl 1)) (e (.inr 1)) :=
      congrArg Subtype.val h
    exact (mul_scalar_ne (g := (rotGL (e (.inl 0)) (e (.inr 0))) ^ m) (c := 1)
      (h := rotGL (e (.inl 1)) (e (.inr 1))) (a := e (.inl 1)) (b := e (.inr 1))
      (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m)
      (rotMatrix_mulVec_left _ _) (Subgroup.one_mem _)) (by rw [h1, mul_one])

private theorem s16h_H5_oddRankTwo_statedSL {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] : CFSG.Quasithin.A3Facts.OddRankTwo ↥(StatedSL n K) :=
  ⟨3, Nat.prime_three, by norm_num,
    s16h_H5_two_le_pRank_three_of_rotGL
      ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
      (fun _ => Subgroup.subset_closure (det_rotMatrix _ _))⟩

theorem s16h_H5_isSLn_class [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {n a : ℕ} (ha : a ≤ 3) (h : IsSLn ↥L n a) :
    (n = 3 ∧ a = 1) ∨ (n = 2 ∧ a = 2) ∨ (n = 2 ∧ a = 3) := by
  obtain ⟨K, hF, hFin, hKcard, ⟨e⟩⟩ := h
  letI := hF; letI := hFin
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · exact (s16h_H5_not_quasisimple_of_isSLn_small hc (by omega)
        ⟨K, hF, hFin, hKcard, ⟨e⟩⟩).elim
    · exact (s16h_H5_not_quasisimple_of_isSLn_small hc (by omega)
        ⟨K, hF, hFin, hKcard, ⟨e⟩⟩).elim
    · rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · interval_cases a
        · exfalso
          have h1 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
          rw [hKcard] at h1
          norm_num at h1
        · exact (s16h_H5_not_quasisimple_of_isSLn_two_one hc
            ⟨K, hF, hFin, hKcard, ⟨e⟩⟩).elim
      · rcases (by omega : a = 2 ∨ a = 3) with rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · have hn3 : n = 3 := by omega
      subst hn3
      rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · interval_cases a
        · exfalso
          have h1 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
          rw [hKcard] at h1
          norm_num at h1
        · exact Or.inl ⟨rfl, rfl⟩
      · exact (s16h_H5_false_of_oddRankTwo hc
          (CFSG.Quasithin.A3Facts.OddRankTwo.of_mulEquiv e
            (s16h_H5_oddRankTwo_statedSL_three ha2 hKcard))).elim
    · exact (s16h_H5_false_of_oddRankTwo hc
        (CFSG.Quasithin.A3Facts.OddRankTwo.of_mulEquiv e
          (s16h_H5_oddRankTwo_statedSL hn4))).elim

theorem s16h_H5_isAlt_class [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {n : ℕ} (h : UC22.IsAlt ↥L n) : n = 5 := by
  obtain ⟨e⟩ := h
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n
    · exact (s16h_H5_not_quasisimple_of_isAlt_le_four hc ⟨e⟩ (by omega)).elim
    · exact (s16h_H5_not_quasisimple_of_isAlt_le_four hc ⟨e⟩ (by omega)).elim
    · exact (s16h_H5_not_quasisimple_of_isAlt_le_four hc ⟨e⟩ (by omega)).elim
    · exact (s16h_H5_not_quasisimple_of_isAlt_le_four hc ⟨e⟩ (by omega)).elim
    · exact (s16h_H5_not_quasisimple_of_isAlt_le_four hc ⟨e⟩ (by omega)).elim
    · rfl
  · exact (s16h_H5_false_of_oddRankTwo hc ⟨3, Nat.prime_three, by norm_num, by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
      exact CFSG.Quasithin.A3Facts.two_le_pRank_alternating hn⟩).elim

theorem s16h_H5_not_thin_of_l5 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : IsLn ↥L 5 1) : False := by
  have hsc : StatedClassicalModel ↥L .PSL 5 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, K, hF, hFin, hKcard, ⟨e⟩⟩ := hsc
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact CFSG.Quasithin.A3Facts.psl_two_le_pRank_three (K := K) (n := 5) (by norm_num)
  exact s16h_H5_false_of_oddRankTwo hc ⟨3, Nat.prime_three, by norm_num, h2⟩

theorem s16h_H5_not_thin_of_l34 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : IsLn ↥L 3 2) : False := by
  have hsc : StatedClassicalModel ↥L .PSL 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, K, hF, hFin, hKcard, ⟨e⟩⟩ := hsc
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact CFSG.Quasithin.A3Facts.psl_three_four_two_le_pRank (K := K) hKcard
  exact s16h_H5_false_of_oddRankTwo hc ⟨3, Nat.prime_three, by norm_num, h2⟩

theorem s16h_H5_thin_one_case4
    [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : Conc4_135 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)
      (E3.mQuot (commSub (commSub ⊤ L) (Subgroup.zpowers t) ⊔ (commSub ⊤ L ⊓ fixV L))
        (commSub ⊤ L ⊓ fixV L))) :
    s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
      s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
      s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
      s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
      s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
      s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
      s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) := by
  set M : ℕ := E3.mQuot (commSub (commSub ⊤ L) (Subgroup.zpowers t) ⊔
    (commSub ⊤ L ⊓ fixV L)) (commSub ⊤ L ⊓ fixV L) with hM
  have hm : M ≤ 3 := by rw [hM]; exact s16h_H5_mQuot_le_three hc.tr
  have hZ : commSub ⊤ L ⊓ fixV L ≤ commSub ⊤ L := inf_le_left
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | hg2 | htri | hu43 | halt | ha7 | hsp6 | hl5 | hm22 | hl34 |
    hl32
  · rcases h with ⟨hSL, hN⟩ | ⟨hSp, hN⟩ | hO | hO2
    · obtain ⟨hn, ha⟩ | ⟨hn, ha⟩ | ⟨hn, ha⟩ := s16h_H5_isSLn_class hc hm hSL
      · subst hn; rw [ha] at hSL hN
        exact Or.inl ⟨1, by norm_num, hSL,
          s16h_H5_sumOfNat_one (N := fun H U Z => BinaryNaturalSL H U Z 3 1) hZ hN⟩
      · subst hn; rw [ha] at hSL hN
        exact Or.inr (Or.inr (Or.inl ⟨hSL, hN⟩))
      · subst hn; rw [ha] at hSL hN
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, hN⟩)))
    · obtain ⟨hn, ha⟩ | ⟨hn, ha⟩ := s16h_H5_isSpn_class hc hm hSp
      · subst hn; rw [ha] at hSp hN
        exact Or.inr (Or.inr (Or.inl (s16h_H5_rowSL2_of_isSpn_two hc hSp hN)))
      · subst hn; rw [ha] at hSp hN
        exact Or.inr (Or.inr (Or.inr (Or.inl (s16h_H5_rowSL2_of_isSpn_two hc hSp hN))))
    · exact (s16h_H5_isOmegaPlus_class hc hO.1).elim
    · obtain ⟨hn, ha⟩ := s16h_H5_isOmegaMinus_class hc hm hO2.1
      subst hn
      rcases ha with ha | ha | ha
      · rw [ha] at hO2
        exact Or.inr (Or.inl ⟨1, by norm_num, Or.inl ⟨hO2.1,
          s16h_H5_sumOfNat_one (N := fun H U Z => NatOmegaMinus H U Z 4 1) hZ hO2.2⟩⟩)
      · rw [ha] at hO2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hO2.1, hO2.2⟩))))
      · rw [ha] at hO2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hO2.1, hO2.2⟩)))))
  · rcases h with ⟨hSL, hN⟩ | ⟨hSp, hN⟩ | ⟨hO, hN⟩ | ⟨hO, hN⟩ | ⟨hSU, hN⟩
    · obtain ⟨hn, -⟩ | ⟨hn, ha⟩ | ⟨hn, ha⟩ := s16h_H5_isSLn_class hc (by norm_num) hSL
      · subst hn
        exact Or.inl ⟨1, by norm_num, hSL,
          s16h_H5_sumOfNat_one (N := fun H U Z => BinaryNaturalSL H U Z 3 1) hZ hN⟩
      · omega
      · omega
    · obtain ⟨hn, ha⟩ | ⟨hn, ha⟩ := s16h_H5_isSpn_class hc (by norm_num) hSp
      · omega
      · omega
    · exact (s16h_H5_isOmegaPlus_class hc hO).elim
    · obtain ⟨hn, -⟩ := s16h_H5_isOmegaMinus_class hc (by norm_num) hO
      subst hn
      exact Or.inr (Or.inl ⟨1, by norm_num, Or.inl ⟨hO,
        s16h_H5_sumOfNat_one (N := fun H U Z => NatOmegaMinus H U Z 4 1) hZ hN⟩⟩)
    · exact (s16h_H5_isSUn_class hc hSU).elim
  · exact (s16h_H5_not_thin_of_g2 hc hg2).elim
  · exact (s16h_H5_not_thin_of_tripleA6 hc htri).elim
  · exact (s16h_H5_not_thin_of_u43 hc hu43.1).elim
  · obtain ⟨n, hAlt, hN⟩ := halt
    obtain rfl := s16h_H5_isAlt_class hc hAlt
    exact Or.inr (Or.inl ⟨1, by norm_num, Or.inr ⟨hAlt,
      s16h_H5_sumOfNat_one (N := fun H U Z => AlternatingNatural H U Z 5) hZ hN⟩⟩)
  · exact (s16h_H5_not_thin_of_a7 hc ha7).elim
  · exact (s16h_H5_not_thin_of_sp6 hc hsp6.1).elim
  · exact (s16h_H5_not_thin_of_l5 hc hl5.1).elim
  · exact (s16h_H5_not_thin_of_m22 hc hm22.1).elim
  · exact (s16h_H5_not_thin_of_l34 hc hl34.1).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hl32.1, hl32.2⟩)))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
