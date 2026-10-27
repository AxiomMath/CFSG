module

public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.CGT.Timmesfeld75

private theorem irgA1_transvection_up_eq_utriElt (F : Type) [Field F] (c : F) :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c = utriElt c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, utriElt]

private theorem irgA1_transvection_low_eq_ltriElt (F : Type) [Field F] (c : F) :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c = ltriElt c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, ltriElt]

private theorem irgA1_rootGroup_single (F : Type) [Field F] :
    SpecialLinear.rootGroup 1 F (Pi.single (0 : Fin 1) 1) = utri F := by
  have hγ : SpecialLinear.toStd 1 (Pi.single (0 : Fin 1) 1) =
      Pi.single (0 : Fin 2) 1 - Pi.single (1 : Fin 2) 1 := by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd, Pi.single_apply]
  have hroot : SpecialLinear.rootGroup 1 F (Pi.single (0 : Fin 1) 1) =
      SpecialLinear.rootSubgroup 1 F (show (0 : Fin 2) ≠ 1 by decide) :=
    SpecialLinear.rootGroup_eq 1 F (show (0 : Fin 2) ≠ 1 by decide) hγ
  rw [hroot]
  ext g
  rw [SpecialLinear.mem_rootSubgroup, mem_utri_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, irgA1_transvection_up_eq_utriElt F c⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, irgA1_transvection_up_eq_utriElt F s⟩

private theorem irgA1_rootGroup_neg_single (F : Type) [Field F] :
    SpecialLinear.rootGroup 1 F (-(Pi.single (0 : Fin 1) 1)) = ltri F := by
  have hγ : SpecialLinear.toStd 1 (-(Pi.single (0 : Fin 1) 1)) =
      Pi.single (1 : Fin 2) 1 - Pi.single (0 : Fin 2) 1 := by
    funext a
    fin_cases a <;> simp [SpecialLinear.toStd, Pi.single_apply]
  have hroot : SpecialLinear.rootGroup 1 F (-(Pi.single (0 : Fin 1) 1)) =
      SpecialLinear.rootSubgroup 1 F (show (1 : Fin 2) ≠ 0 by decide) :=
    SpecialLinear.rootGroup_eq 1 F (show (1 : Fin 2) ≠ 0 by decide) hγ
  rw [hroot]
  ext g
  rw [SpecialLinear.mem_rootSubgroup, mem_ltri_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, irgA1_transvection_low_eq_ltriElt F c⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, irgA1_transvection_low_eq_ltriElt F s⟩

theorem irg_sl2_pair {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    (P Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hP : Nat.card P = Nat.card F) (hQ : Nat.card Q = Nat.card F) (hPQ : P ⊓ Q = ⊥) :
    ∃ (β : Fin 1 → ℤ) (w : Matrix.SpecialLinearGroup (Fin 2) F),
      (β = Pi.single 0 1 ∨ β = -Pi.single 0 1) ∧
      P = ((SpecialLinear.rootDatum 1 F).rootGroup β).map (MulAut.conj w).toMonoidHom ∧
      Q = ((SpecialLinear.rootDatum 1 F).rootGroup (-β)).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨n, hnpos, hn⟩ := exists_natCard_eq_two_pow (F := F)
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := n) (hP.trans hn)
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := n) (hQ.trans hn)
  have hPidx : P.index = Nat.card F ^ 2 - 1 := by
    have h := Subgroup.card_mul_index P
    rw [hP, card_sl2] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hQidx : Q.index = Nat.card F ^ 2 - 1 := by
    have h := Subgroup.card_mul_index Q
    rw [hQ, card_sl2] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hPodd : Odd P.index := by
    rw [hPidx, hn]
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) ?_ odd_one
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hnpos.ne'⟩, two_ne_zero⟩
  have hQodd : Odd Q.index := by
    rw [hQidx, hn]
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) ?_ odd_one
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hnpos.ne'⟩, two_ne_zero⟩
  have hPodd' : ¬ 2 ∣ P.index := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hPodd
  have hQodd' : ¬ 2 ∣ Q.index := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hQodd
  obtain ⟨a, ha⟩ := exists_conjSubgroup_utri_eq_of_sylow (IsPGroup.toSylow hP2 hPodd')
  obtain ⟨b, hb⟩ := exists_conjSubgroup_utri_eq_of_sylow (IsPGroup.toSylow hQ2 hQodd')
  have ha' : conjSubgroup a (utri F) = P := by rw [ha, IsPGroup.toSylow_coe]
  have hb' : conjSubgroup b (utri F) = Q := by rw [hb, IsPGroup.toSylow_coe]
  have hPQne : P ≠ Q := by
    intro h
    have hPbot : P = ⊥ := by
      have : P ⊓ Q = P := by rw [h, inf_idem]
      rw [hPQ] at this
      exact this.symm
    have hc : Nat.card P = 1 := by rw [hPbot, Subgroup.card_bot]
    rw [hP] at hc
    omega
  have hne : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F) := by
    rw [ha', hb']; exact hPQne
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_normal_form hne
  have hPform : P = conjSubgroup g⁻¹ (utri F) := by
    calc P = conjSubgroup a (utri F) := ha'.symm
      _ = conjSubgroup (g⁻¹ * (g * a)) (utri F) := by rw [inv_mul_cancel_left]
      _ = conjSubgroup g⁻¹ (conjSubgroup (g * a) (utri F)) := by rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup g⁻¹ (utri F) := by rw [hg1]
  have hQform : Q = conjSubgroup g⁻¹ (ltri F) := by
    calc Q = conjSubgroup b (utri F) := hb'.symm
      _ = conjSubgroup (g⁻¹ * (g * b)) (utri F) := by rw [inv_mul_cancel_left]
      _ = conjSubgroup g⁻¹ (conjSubgroup (g * b) (utri F)) := by rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup g⁻¹ (ltri F) := by rw [hg2]
  refine ⟨Pi.single (0 : Fin 1) 1, g⁻¹, Or.inl rfl, ?_, ?_⟩
  · rw [show (SpecialLinear.rootDatum 1 F).rootGroup = SpecialLinear.rootGroup 1 F from rfl,
      irgA1_rootGroup_single F]
    exact hPform
  · rw [show (SpecialLinear.rootDatum 1 F).rootGroup = SpecialLinear.rootGroup 1 F from rfl,
      irgA1_rootGroup_neg_single F]
    exact hQform

end CFSG.StandardType.RCKRP
