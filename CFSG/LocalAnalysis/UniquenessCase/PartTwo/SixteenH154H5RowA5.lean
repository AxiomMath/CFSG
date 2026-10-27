module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumOm4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumAlt5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_card_mulAut_alt5_dvd {X : Type} [Group X] (h : UC22.IsAlt X 5) :
    Nat.card (MulAut X) ∣ 120 := by
  obtain ⟨e⟩ := h
  have hsurj : Function.Surjective
      (MulAut.conjNormal (H := alternatingGroup (Fin 5)) :
        Equiv.Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5))) := by
    intro f
    obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj (α := Fin 5)
      (by decide) f
    exact ⟨σ, by
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      exact (hσ g).symm⟩
  have hdvd := Subgroup.card_dvd_of_surjective
    (f := (MulAut.conjNormal (H := alternatingGroup (Fin 5)) :
      Equiv.Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5)))) hsurj
  calc Nat.card (MulAut X) = Nat.card (MulAut (alternatingGroup (Fin 5))) :=
        Nat.card_congr (MulAut.congr e).toEquiv
    _ ∣ Nat.card (Equiv.Perm (Fin 5)) := hdvd
    _ = 120 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num

private theorem s16h_center_eq_bot_of_isAlt5 {X : Type} [Group X] (h : UC22.IsAlt X 5) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  rw [eq_bot_iff]
  intro x hx
  have hxe : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [alternatingGroup.center_eq_bot (by norm_num)] at hxe
  exact Subgroup.mem_bot.mpr
    (e.injective ((Subgroup.mem_bot.mp hxe).trans (map_one e).symm))

private theorem s16h_not_sq_dvd_120 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 120 := by
  intro h
  have hle : q ^ 2 ≤ 120 := Nat.le_of_dvd (by norm_num) h
  have hq2le : 2 ≤ q := hq.two_le
  have hq10 : q ≤ 10 := by nlinarith
  interval_cases q
  · exact hq2 rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem s16h_H5_row_A5_rank [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
      Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 := by
  obtain ⟨k, hk, hsum | hsum⟩ := h
  · obtain ⟨hOM, hS⟩ := hsum
    have hq := hc.comp.2.2
    have hAlt : UC22.IsAlt ↥L 5 := s16k_isAlt_five_of_isOmegaMinus_four hOM
    exact s16h_H5_sum_glue hc
      (N := fun H U Z => NatOmegaMinus H U Z 4 1)
      (fun I hI => s16h_simpleScalar_natOmegaMinus4 hq hOM hI) hk hS
      (s16h_center_eq_bot_of_isAlt5 hAlt) (s16h_card_mulAut_alt5_dvd hAlt)
      (fun q hq' hq2 => s16h_not_sq_dvd_120 hq' hq2)
  · obtain ⟨hAlt, hS⟩ := hsum
    have hq := hc.comp.2.2
    exact s16h_H5_sum_glue hc
      (N := fun H U Z => AlternatingNatural H U Z 5)
      (fun I hI => s16h_simpleScalar_alt5 hq hAlt hI) hk hS
      (s16h_center_eq_bot_of_isAlt5 hAlt) (s16h_card_mulAut_alt5_dvd hAlt)
      (fun q hq' hq2 => s16h_not_sq_dvd_120 hq' hq2)

theorem s16h_H5_row_A5 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    s16h_H5Block A L :=
  s16h_H5_block_of_autSub (s16h_H5_row_A5_rank hc h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
