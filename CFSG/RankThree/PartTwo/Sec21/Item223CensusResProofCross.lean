module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossUnit
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofHigh
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofA9
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossLin

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace Item223CensusResProof

theorem not_prime_of_card_mul {G : Type*} [Group G] {g q M : ℕ} (hg : g ∣ 3) (hq : 2 ≤ q)
    (h : Nat.card G * g = q ^ 3 * M) : ¬ (Nat.card G).Prime := by
  intro hr
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (show q ≠ 1 by omega)
  have hp3 : p ^ 3 ∣ Nat.card G * g :=
    h ▸ (pow_dvd_pow_of_dvd hpq 3).trans (Dvd.intro _ rfl)
  have hg' : g = 1 ∨ g = 3 := by
    have := Nat.le_of_dvd (by norm_num) hg
    interval_cases g <;> simp_all
  rcases hg' with rfl | rfl
  · rw [mul_one] at hp3
    have hpr : p ∣ Nat.card G := (dvd_pow_self p (by norm_num)).trans hp3
    rw [(Nat.prime_dvd_prime_iff_eq hp hr).mp hpr] at hp3
    have := Nat.le_of_dvd hr.pos hp3
    have : Nat.card G ^ 2 ≤ Nat.card G ^ 3 := Nat.pow_le_pow_right hr.pos (by norm_num)
    nlinarith [hr.two_le]
  · by_cases hp3' : p = 3
    · subst hp3'
      have h9 : 9 ∣ Nat.card G := by
        have : 27 ∣ Nat.card G * 3 := by simpa using hp3
        omega
      have h3 : 3 ∣ Nat.card G := (Dvd.intro 3 rfl).trans h9
      have h3' := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h3
      rw [← h3'] at h9
      norm_num at h9
    · have hcop : Nat.Coprime (p ^ 3) 3 :=
        Nat.Coprime.pow_left 3 ((Nat.coprime_primes hp Nat.prime_three).mpr hp3')
      have hp3G := hcop.dvd_of_dvd_mul_right hp3
      have hpr : p ∣ Nat.card G := (dvd_pow_self p (by norm_num)).trans hp3G
      rw [(Nat.prime_dvd_prime_iff_eq hp hr).mp hpr] at hp3G
      have := Nat.le_of_dvd hr.pos hp3G
      have : Nat.card G ^ 2 ≤ Nat.card G ^ 3 := Nat.pow_le_pow_right hr.pos (by norm_num)
      nlinarith [hr.two_le]

theorem center_projectiveSL_three (K : Type) [Field K] [Finite K] :
    Subgroup.center (projectiveSL 3 K) = ⊥ := by
  have := isSimpleGroup_projectiveSL' (K := K) (n := 3) le_rfl
  refine Item223CensusProof.center_eq_bot_of_isSimpleGroup
    (not_prime_of_card_mul (g := Nat.gcd 3 (Nat.card K - 1)) (q := Nat.card K)
      (M := (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) (Nat.gcd_dvd_left 3 _)
      (two_le_card_field K) ?_)
  rw [card_projectiveSL_three_mul, card_SL_three, mul_assoc]

theorem center_unitaryPSU_three {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) : Subgroup.center (unitaryPSU h 3) = ⊥ := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hs : IsSimpleGroup (unitaryPSU h 3) := by
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f
      (by rw [h.card, ← pow_mul, mul_comm]) 3 le_rfl (by
        intro hh
        exact absurd (Prod.mk.inj hh).2 (by omega))
    exact (unitaryPSUEquiv h (by norm_num)).isSimpleGroup
  refine Item223CensusProof.center_eq_bot_of_isSimpleGroup
    (not_prime_of_card_mul (g := Nat.gcd 3 (p ^ f + 1)) (q := p ^ f)
      (M := ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) (Nat.gcd_dvd_left 3 _)
      (two_le_pow_of_unitaryFieldData h) ?_)
  rw [card_unitaryPSU_three_mul, card_unitarySU_three' h, mul_assoc]

theorem center_SL_three_ne_bot {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1) :
    Subgroup.center (SpecialLinearGroup (Fin 3) K) ≠ ⊥ := by
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root hK
  intro hbot
  let z : SpecialLinearGroup (Fin 3) K := ⟨Matrix.scalar (Fin 3) ω, by simp [hω]⟩
  have hmem : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨ω, by rw [Fintype.card_fin]; exact hω, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0)
    hmem
  simp [z] at h1
  exact hω1 h1

theorem center_unitarySU_three_ne_bot {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (h3 : 3 ∣ p ^ f + 1) : Subgroup.center (unitarySU p f K 3) ≠ ⊥ := by
  have := h.finite
  have hK : 3 ∣ Nat.card K - 1 := by
    rw [h.card, pow_mul']
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
    have : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      zify [h1, Nat.one_le_pow 2 _ h1]
      ring
    rw [this]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root hK
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  set u : Kˣ := Units.mk0 ω hω0
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [u, hω])
  have hnorm : h.norm (u : K) = 1 := by
    rw [h.norm_eq_pow]
    obtain ⟨k, hk⟩ := h3
    rw [hk, pow_mul]
    simp [u, hω]
  have hmem := scalar_mem_unitarySU h (by norm_num) hnorm hu3
  intro hbot
  have hc : (⟨_, hmem⟩ : unitarySU p f K 3) ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) u =
      GeneralLinearGroup.scalar (Fin 3) u * g
    have hz : GeneralLinearGroup.scalar (Fin 3) u ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact (Subgroup.mem_center_iff.mp hz (g : GL (Fin 3) K))
  rw [hbot, Subgroup.mem_bot] at hc
  have h1 := congrArg (fun A : unitarySU p f K 3 =>
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) hc
  simp [u] at h1
  exact hω1 h1

theorem false_of_center {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (hM : Subgroup.center M = ⊥) (hM' : Subgroup.center M' ≠ ⊥) : False := by
  apply hM'
  rw [← Sec4.map_center_mulEquiv e, hM, Subgroup.map_bot]

theorem sl3Poly_ne_su3Poly {q q' : ℕ} (hq : 2 ≤ q) (hq' : 2 ≤ q') :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≠ q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1) := by
  have hmono : ∀ {a b : ℕ}, 2 ≤ a → a ≤ b →
      a ^ 3 * (a ^ 2 - 1) * (a ^ 3 - 1) ≤ b ^ 3 * (b ^ 2 - 1) * (b ^ 3 - 1) := by
    intro a b ha hab
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (sl3Poly_lt ha hlt).le
  have h4 : 0 < q' ^ 2 - 1 := by
    have : 2 ^ 2 ≤ q' ^ 2 := Nat.pow_le_pow_left hq' 2
    omega
  have h8 : 0 < q' ^ 3 := by positivity
  rcases Nat.lt_or_ge q' q with hlt | hle
  · have h1 := hmono (a := q' + 1) (b := q) (by omega) hlt
    have e1 : q' ^ 3 < (q' + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    have e2 : q' ^ 2 - 1 ≤ (q' + 1) ^ 2 - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1
    have e3 : q' ^ 3 + 1 ≤ (q' + 1) ^ 3 - 1 := by
      have : (q' + 1) ^ 3 = q' ^ 3 + 3 * q' ^ 2 + 3 * q' + 1 := by ring
      omega
    have h2 : q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1) <
        (q' + 1) ^ 3 * ((q' + 1) ^ 2 - 1) * ((q' + 1) ^ 3 - 1) :=
      calc q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1) <
            (q' + 1) ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1) := by
            apply Nat.mul_lt_mul_of_pos_right _ (by omega)
            exact Nat.mul_lt_mul_of_pos_right e1 h4
        _ ≤ (q' + 1) ^ 3 * ((q' + 1) ^ 2 - 1) * ((q' + 1) ^ 3 - 1) := by gcongr
    exact (lt_of_lt_of_le h2 h1).ne'
  · have h1 := hmono hq hle
    have h2 : q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 - 1) < q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (Nat.mul_pos h8 h4)
    exact (lt_of_le_of_lt h1 h2).ne

theorem isEmpty_projectiveSL_three_equiv_unitaryPSU {K : Type} [Field K] [Finite K]
    (hK : 3 ∣ Nat.card K - 1) {p f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData p f K')
    (h3 : 3 ∣ p ^ f + 1) : IsEmpty (projectiveSL 3 K ≃* unitaryPSU h 3) := by
  refine ⟨fun e => ?_⟩
  have hc := Nat.card_congr e.toEquiv
  have h1 := card_projectiveSL_three_mul (K := K)
  have h2 := card_unitaryPSU_three_mul h
  rw [Nat.gcd_eq_left hK, card_SL_three] at h1
  rw [Nat.gcd_eq_left h3, card_unitarySU_three' h] at h2
  exact sl3Poly_ne_su3Poly (two_le_card_field K) (two_le_pow_of_unitaryFieldData h)
    (by rw [← h1, ← h2, hc])

theorem isEmpty_SL_three_equiv_unitarySU {K : Type} [Field K] [Finite K] {p f : ℕ} {K' : Type}
    [Field K'] (h : UnitaryFieldData p f K') :
    IsEmpty (SpecialLinearGroup (Fin 3) K ≃* unitarySU p f K' 3) := by
  refine ⟨fun e => ?_⟩
  have hc := Nat.card_congr e.toEquiv
  rw [card_SL_three, card_unitarySU_three' h] at hc
  exact sl3Poly_ne_su3Poly (two_le_card_field K) (two_le_pow_of_unitaryFieldData h) hc

theorem not_highInv_projectiveSL_three {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {Y : Type} [Group Y] (e : Y ≃* projectiveSL 3 K) (h : HighInv Y) : False :=
  h.false_of_inner e fun F hF hFi => (Item223CensusProof.card_le_nine_inner_projectiveSL3
    (Item223CensusProof.three_ne_zero_of_dvd_card_sub_one hK) F hF hFi).trans (by norm_num)

theorem not_highInv_SL_three {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {Y : Type} [Group Y] (e : Y ≃* SpecialLinearGroup (Fin 3) K) (h : HighInv Y) : False := by
  refine h.false_of_hom ((SpecialLinearGroup.toGL).comp e.toMonoidHom)
    (SpecialLinearGroup.toGL_injective.comp e.injective) fun P hPr hcomm hexp => ?_
  have : Finite P := Finite.of_injective _ Subtype.val_injective
  have h1 := Sec4.card_le_of_det_eq_one (Item223CensusProof.three_ne_zero_of_dvd_card_sub_one hK)
    0 P hcomm hexp fun x hx => by
      obtain ⟨y, rfl⟩ := hPr hx
      exact (e y).2
  simp only [Fintype.card_fin] at h1
  omega

theorem not_highInv_unitaryPSU_three {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    (h3 : 3 ∣ p ^ f + 1) {Y : Type} [Group Y] (e : Y ≃* unitaryPSU hK 3) (h : HighInv Y) :
    False := by
  have := hK.finite
  exact h.false_of_inner e fun F hF hFi => (Item223CensusProof.card_le_nine_inner_unitaryPSU
    (Item223CensusProof.three_ne_zero_of_dvd_add_one hK h3) F hF hFi).trans (by norm_num)

theorem not_highInv_unitarySU_three {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    (h3 : 3 ∣ p ^ f + 1) {Y : Type} [Group Y] (e : Y ≃* unitarySU p f K 3) (h : HighInv Y) :
    False := by
  have := hK.finite
  refine h.false_of_hom ((unitarySU p f K 3).subtype.comp e.toMonoidHom)
    (Subtype.val_injective.comp e.injective) fun P hPr hcomm hexp => ?_
  have : Finite P := Finite.of_injective _ Subtype.val_injective
  have h1 := Sec4.card_le_of_det_eq_one (Item223CensusProof.three_ne_zero_of_dvd_add_one hK h3)
    0 P hcomm hexp fun x hx => by
      obtain ⟨y, rfl⟩ := hPr hx
      exact ((mem_unitarySU_iff hK).mp (e y).2).1
  simp only [Fintype.card_fin] at h1
  omega

theorem inducedAutHom_eq_congr {G : Type} [Group G] [Finite G] (L : Subgroup G) {M M' : Type*}
    [Group M] [Group M'] (e' : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M') (x : Subgroup.normalizer (L : Set G)) :
    inducedAutHom L e x = MulAut.congr (e'.symm.trans e) (inducedAutHom L e' x) := by
  rw [inducedAutHom_apply, inducedAutHom_apply, ← congr_trans]
  congr 1
  ext z
  simp

theorem card_unitaryPSU_three_two {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f = 2) : Nat.card (unitaryPSU h 3) = 72 := by
  have h1 := card_unitaryPSU_three_mul h
  rw [card_unitarySU_three' h, hq] at h1
  norm_num at h1
  omega

end Item223CensusResProof

open Item223CensusResProof


theorem outer223Cross_holds : Outer223Cross := by
  intro G _ _ X y hL hy3 hdiag
  cases hdiag with
  | psl2 K h => exact (Item223CensusProof.not_inducesKindPSL2_diagonal hy3 h).elim
  | psp r K hr h =>
    exact (Item223CensusProof.not_inducesKindPSp_diagonal
      (by rcases hr with hr | ⟨rfl, -⟩ <;> omega) hy3 h).elim
  | psp4even F h => exact (Item223CensusProof.not_inducesKindPSp4Even_diagonal h).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | sz a K ha hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, hx, h⟩ := h
    exact h.elim
  | largeRee a ha K hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | psl n K' hn h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ n ∧ 3 ∣ Nat.card K' - 1 := by
      by_contra h3
      exact hni (Item223CensusProof.isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3 hτ
        (inducedAutHom_pow_eq_one X e' hx hy3))
    rcases (show n = 3 ∨ 6 ≤ n by obtain ⟨k, hk⟩ := h3.1; omega) with rfl | hn6
    · refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ hK e hy => ?_,
        fun p f K _ hK h3' e hy => ?_, fun p f K _ hK hq h3' e hy => ?_⟩
      · rw [inducedAutHom_eq_congr X e' e]
        exact congr_mem_linearAutGroup hK h3.2 _ hτ
      · exact (false_of_center (e'.symm.trans e) (center_projectiveSL_three K')
          (center_SL_three_ne_bot hK)).elim
      · exact ((isEmpty_projectiveSL_three_equiv_unitaryPSU h3.2 hK h3').false
          (e'.symm.trans e)).elim
      · exact (false_of_center (e'.symm.trans e) (center_projectiveSL_three K')
          (center_unitarySU_three_ne_bot hK h3')).elim
    · have hH : HighInv (X ⧸ aschbacherSolvableCore 3 X) :=
        (highInv_projectiveSL hn6 h3.2).of_mulEquiv e'
      exact ⟨fun K _ _ hK e _ => (not_highInv_projectiveSL_three hK e hH).elim,
        fun K _ _ hK e _ => (not_highInv_SL_three hK e hH).elim,
        fun p f K _ hK h3' e _ => (not_highInv_unitaryPSU_three hK h3' e hH).elim,
        fun p f K _ hK _ h3' e _ => (not_highInv_unitarySU_three hK h3' e hH).elim⟩
  | sl n K' hn h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ n ∧ 3 ∣ Nat.card K' - 1 := by
      by_contra h3
      exact hni (Item223CensusProof.isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3 hτ
        (by rw [← map_pow, inducedAutHom_pow_eq_one X e' hx hy3, map_one]))
    rcases (show n = 3 ∨ 6 ≤ n by obtain ⟨k, hk⟩ := h3.1; omega) with rfl | hn6
    · refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ hK e hy => ?_,
        fun p f K _ hK h3' e hy => ?_, fun p f K _ hK _ _ e hy => ?_⟩
      · exact (false_of_center (e.symm.trans e') (center_projectiveSL_three K)
          (center_SL_three_ne_bot h3.2)).elim
      · rw [inducedAutHom_eq_congr X e' e]
        exact descendAut_congr_mem_linearAutGroup hK h3.2 _ hτ
      · by_cases hq : 2 < p ^ f
        · exact (false_of_center (e.symm.trans e') (center_unitaryPSU_three hK hq)
            (center_SL_three_ne_bot h3.2)).elim
        · have hq2 : p ^ f = 2 := by
            have := two_le_pow_of_unitaryFieldData hK
            omega
          have h1 := Nat.card_congr (e.symm.trans e').toEquiv
          rw [card_unitaryPSU_three_two hK hq2, card_SL_three] at h1
          have h2 := sl3Poly_lt (q := 2) le_rfl
            (show 2 < Nat.card K' by have := four_le_card h3.2; omega)
          norm_num at h2
          omega
      · exact ((isEmpty_SL_three_equiv_unitarySU (K := K') hK).false (e'.symm.trans e)).elim
    · have hH : HighInv (X ⧸ aschbacherSolvableCore 3 X) := (highInv_SL hn6 h3.2).of_mulEquiv e'
      exact ⟨fun K _ _ hK e _ => (not_highInv_projectiveSL_three hK e hH).elim,
        fun K _ _ hK e _ => (not_highInv_SL_three hK e hH).elim,
        fun p f K _ hK h3' e _ => (not_highInv_unitaryPSU_three hK h3' e hH).elim,
        fun p f K _ hK _ h3' e _ => (not_highInv_unitarySU_three hK h3' e hH).elim⟩
  | @psu3 p' f' K' _ hK' hq' h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ p' ^ f' + 1 := by
      by_contra h3
      obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact hni (Item223CensusProof.isInnerAut_psuConj_of_not_dvd h3 B)
    refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ hK e hy => ?_,
      fun p f K _ hK h3' e hy => ?_, fun p f K _ hK hq h3' e hy => ?_⟩
    · exact ((isEmpty_projectiveSL_three_equiv_unitaryPSU hK hK' h3).false (e.symm.trans e')).elim
    · exact (false_of_center (e'.symm.trans e) (center_unitaryPSU_three hK' hq')
        (center_SL_three_ne_bot hK)).elim
    · rw [inducedAutHom_eq_congr X e' e]
      exact congr_mem_psuConj_range hK hK' h3' h3 hq' _ hτ
    · exact (false_of_center (e'.symm.trans e) (center_unitaryPSU_three hK' hq')
        (center_unitarySU_three_ne_bot hK h3')).elim
  | @su3 p' f' K' _ hK' hq' h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ p' ^ f' + 1 := by
      by_contra h3
      obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact hni (Item223CensusProof.isInnerAut_psuConj_of_not_dvd h3 B)
    refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ _ e hy => ?_,
      fun p f K _ hK h3' e hy => ?_, fun p f K _ hK hq h3' e hy => ?_⟩
    · exact (false_of_center (e.symm.trans e') (center_projectiveSL_three K)
        (center_unitarySU_three_ne_bot hK' h3)).elim
    · exact ((isEmpty_SL_three_equiv_unitarySU (K := K) hK').false (e.symm.trans e')).elim
    · by_cases hq : 2 < p ^ f
      · exact (false_of_center (e.symm.trans e') (center_unitaryPSU_three hK hq)
          (center_unitarySU_three_ne_bot hK' h3)).elim
      · have hq2 : p ^ f = 2 := by
          have := two_le_pow_of_unitaryFieldData hK
          omega
        have h1 := Nat.card_congr (e.symm.trans e').toEquiv
        rw [card_unitaryPSU_three_two hK hq2, card_unitarySU_three' hK'] at h1
        have h2 := su3Poly_lt (q := 2) le_rfl hq'
        norm_num at h2
        omega
    · rw [inducedAutHom_eq_congr X e' e]
      exact centerDescend_congr_mem_psuConj_range hK hK' hq hq' _ hτ

end CFSG.RankThree.PartTwo.Sec21
