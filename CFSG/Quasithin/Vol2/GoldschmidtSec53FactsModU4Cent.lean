module

public import CFSG.Quasithin.H13.U4ParYAmalgam
public import CFSG.Quasithin.H13.U4ParRecog
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU4
public import CFSG.Quasithin.Background.B1More8
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B1MoreSeven
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Walter.Defs

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem centerOf_perfectCore_parP_le (hm : 2 ≤ m) : centerOf (perfectCore (parP h)) ≤ zRad h := by
  rintro x ⟨hxL, hxC⟩
  have hxH : x ∈ parH h := perfectCore_parP_le_parH h hxL
  have hxC' := Subgroup.mem_centralizer_iff.mp hxC
  have hcen : rhoF h ⟨x, hxH⟩ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    rw [Subgroup.mem_center_iff]
    intro A
    have hA : levHom h A ∈ perfectCore (parP h) := levHom_range_le_perfectCore h hm ⟨A, rfl⟩
    have hcomm : levHom h A * x = x * levHom h A := hxC' _ hA
    have h1 := congrArg (rhoF h) (Subtype.ext hcomm :
      (⟨levHom h A, levHom_range_le_parH h ⟨A, rfl⟩⟩ : parH h) * ⟨x, hxH⟩ =
        ⟨x, hxH⟩ * ⟨levHom h A, levHom_range_le_parH h ⟨A, rfl⟩⟩)
    rw [map_mul, map_mul, rhoF_levHom] at h1
    exact h1
  rw [center_sl2_eq_bot h, Subgroup.mem_bot] at hcen
  have hxQ : x ∈ radQ h := U4V.mem_radQ_of_rhoF_eq_one h hcen
  have hxZ : x ∈ centerOf (radQ h) :=
    ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun q hq => hxC' q (radQ_le_perfectCore h hm hq)⟩
  rwa [centerOf_radQ] at hxZ

theorem sMat_zero_zero_zero : sMat h 0 0 0 = 1 := by
  ext i j
  simp [sMat_apply]

theorem diagonal_mul_sMat_zero (e : Ix → K) (he : ∀ i, e i ≠ 0) (c : K) :
    diagonal e * sMat h 0 0 c = sMat h 0 0 (e ie1 * (e if1)⁻¹ * c) * diagonal e := by
  have a1 := he (Sum.inl 0)
  have a2 := he (Sum.inl 1)
  have a3 := he (Sum.inr (Sum.inr 0))
  have a4 := he (Sum.inr (Sum.inr 1))
  ext i j
  rw [diagonal_mul, mul_diagonal]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    (simp [sMat_apply, one_apply, ie1, ie2, if1, if2]; try field_simp)

theorem exists_norm_eq {r : K} (hr : h.bar r = r) (hr0 : r ≠ 0) : ∃ l : Kˣ, l * h.bar l = r := by
  obtain ⟨l, hl⟩ := h.card_ker_normUnits_and_surjective.2
    (Units.mk0 (⟨r, hr⟩ : h.fixedField) (fun e => hr0 (congrArg Subtype.val e)))
  refine ⟨l, ?_⟩
  have := congrArg (fun v : h.fixedFieldˣ => ((v : h.fixedField) : K)) hl
  simpa [UnitaryFieldData.norm] using this

theorem exists_torus_norm (l : Kˣ) : ∃ t ∈ hypTorus h 2 0,
    ((t : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = l ∧
    ((t : GL Ix K) : Matrix Ix Ix K) if1 if1 = (h.bar l)⁻¹ ∧
    ∀ i j, i ≠ j → ((t : GL Ix K) : Matrix Ix Ix K) i j = 0 := by
  let a : Fin 2 → Kˣ := ![l, Units.map (h.bar : K →* K) l]
  have h0 : (l : K) ≠ 0 := l.ne_zero
  have hbb : ∀ x : K, h.bar (h.bar x) = x := h.bar_bar
  have h1 : h.bar (l : K) ≠ 0 := by simp [h0]
  have hp : torusRatio h a (isEmptyElim : Fin 0 → Kˣ) = 1 := by
    have e0 : ∏ k : Fin 0, (((isEmptyElim k : Kˣ)) : K) = 1 := Fin.prod_univ_zero _
    rw [torusRatio, e0, mul_one, Fin.prod_univ_two]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Units.coe_map, MonoidHom.coe_ofClass]
    rw [hbb]
    field_simp
  obtain ⟨g, hg, hm⟩ := torusMat_mem_hypSU h a (d := isEmptyElim) (fun k => isEmptyElim k) hp
  refine ⟨g, hg, ?_, ?_, fun i j hij => ?_⟩
  · rw [hm]
    simp [torusEntries, a, ie1]
  · rw [hm]
    simp [torusEntries, a, if1]
  · rw [hm, diagonal_apply_ne _ hij]

theorem trans_zRad {a a' : hypSU h 2 0} (ha : a ∈ zRad h) (ha' : a' ∈ zRad h) (h1 : a ≠ 1)
    (h1' : a' ≠ 1) : ∃ t ∈ parP h, t * a * t⁻¹ = a' := by
  obtain ⟨c, hc, hma⟩ := ha
  obtain ⟨c', hc', hma'⟩ := ha'
  have hc0 : c ≠ 0 := fun e => h1 (hypSU_ext h (by rw [hma, e, sMat_zero_zero_zero]; rfl))
  have hc0' : c' ≠ 0 := fun e => h1' (hypSU_ext h (by rw [hma', e, sMat_zero_zero_zero]; rfl))
  obtain ⟨l, hl⟩ := exists_norm_eq h (r := c' / c) (by rw [map_div₀, hc, hc'])
    (div_ne_zero hc0' hc0)
  obtain ⟨t, htT, ht1, ht2, ht3⟩ := exists_torus_norm h l
  have htP : t ∈ parP h :=
    UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num) (hypTorus_le_hypBorel h htT)
  have hdiag : ((t : GL Ix K) : Matrix Ix Ix K) = diagonal (fun i => ((t : GL Ix K) :
      Matrix Ix Ix K) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ht3 i j hij, diagonal_apply_ne _ hij]
  have hne : ∀ i, ((t : GL Ix K) : Matrix Ix Ix K) i i ≠ 0 := by
    obtain ⟨a₀, d, -, -, hm⟩ := htT
    intro i
    rw [hm, diagonal_apply_eq]
    rcases i with i | k | i
    · exact (a₀ i).ne_zero
    · exact (d k).ne_zero
    · simp [torusEntries]
  refine ⟨t, htP, ?_⟩
  have key : t * a = a' * t := by
    apply hypSU_ext h
    have hnc : ((t : GL Ix K) : Matrix Ix Ix K) ie1 ie1 *
        (((t : GL Ix K) : Matrix Ix Ix K) if1 if1)⁻¹ * c = c' := by
      rw [ht1, ht2, inv_inv, hl, div_mul_cancel₀ _ hc0]
    rw [coe_mul_hypSU, coe_mul_hypSU, hma, hma', hdiag,
      diagonal_mul_sMat_zero h _ hne c]
    rw [← hdiag, hnc]
  rw [key]
  group

theorem centerOf_perfectCore_parP2_eq_bot (hm : 2 ≤ m) : centerOf (perfectCore (parP2 h)) = ⊥ := by
  have := h.charP
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hxH : x ∈ parH2 h := perfectCore_parP2_le_parH2 h hxL
  have hxC' := Subgroup.mem_centralizer_iff.mp hxC
  have hcen : rho2F h ⟨x, hxH⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro A
    have hA : lev2Hom h A ∈ perfectCore (parP2 h) := lev2Hom_range_le_perfectCore h ⟨A, rfl⟩
    have hcomm : lev2Hom h A * x = x * lev2Hom h A := hxC' _ hA
    have h1 := congrArg (rho2F h) (Subtype.ext hcomm : (⟨lev2Hom h A, lev2Hom_le_parH2 h ⟨A, rfl⟩⟩ :
      parH2 h) * ⟨x, hxH⟩ = ⟨x, hxH⟩ * ⟨lev2Hom h A, lev2Hom_le_parH2 h ⟨A, rfl⟩⟩)
    rw [map_mul, map_mul, rho2F_lev2Hom] at h1
    exact h1
  rw [center_sl2_eq_bot_of_charTwo K, Subgroup.mem_bot] at hcen
  have hrho : rho2 h x = 1 := by
    have := congrArg Subtype.val hcen
    exact this
  have hxQ : x ∈ radQ2 h := mem_radQ2_of_rho2 h (parH2_le_parP2 h hxH) hrho
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_torus_param h hm
  set d : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![c, 0; 0, c⁻¹], by simp [det_fin_two_of, hc0]⟩ with hd
  have hdL : lev2Hom h d ∈ perfectCore (parP2 h) := lev2Hom_range_le_perfectCore h ⟨d, rfl⟩
  have hcomm : x * lev2Hom h d = lev2Hom h d * x := (hxC' _ hdL).symm
  exact Subgroup.mem_bot.mpr (eq_one_of_comm_lev2 h hc0 hc1 hc2 (d := d) rfl hxQ hcomm)

end CFSG.Quasithin.H13.Sec53F.Unit
