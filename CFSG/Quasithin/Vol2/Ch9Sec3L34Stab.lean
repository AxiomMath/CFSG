module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34Max
public import CFSG.Quasithin.Vol2.Ch9Sec4Forms
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CoprimeProduct
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelCentralizer
public import CFSG.Quasithin.Vol2.Ch9Sec3Cart
public import CFSG.Quasithin.Vol2.Ch9Sec3Field
public import CFSG.Quasithin.Vol2.Ch9Sec3LSide

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

namespace Om4Pt

variable {K : Type} [Field K]

theorem eq_of_pow_two_pow_eq [CharP K 2] {x y : K} {k : ℕ} (h : x ^ 2 ^ k = y ^ 2 ^ k) :
    x = y := by
  have h1 : (x - y) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)

theorem eq_one_of_commute_diag [CharP K 2] [Fintype K] (hK4 : Fintype.card K = 4)
    {A B : GL (Fin 2) K} {τ : K ≃+* K} (hA : Om4.IsUT A) (hB : Om4.IsUT B) {a : Kˣ}
    (ha : a ≠ 1)
    (hcomm : (Om4.lr A B * Om4.frM τ) * Om4.rho (diagOf a, diagOf a⁻¹) =
      Om4.rho (diagOf a, diagOf a⁻¹) * (Om4.lr A B * Om4.frM τ)) {k : ℕ}
    (hk : (Om4.lr A B * Om4.frM τ) ^ 2 ^ k = 1) : Om4.lr A B * Om4.frM τ = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha' : (a : K) ≠ 1 := fun h => ha (Units.ext h)
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hainv : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := by
    intro h
    have h1 : (a : K) * a = 1 := by
      calc (a : K) * a = a * ((a⁻¹ : Kˣ) : K) := by rw [← h]
        _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h3 : ((a : K) - 1) ^ 2 = 0 := by linear_combination h1 + (1 - (a : K)) * h2
    exact ha' (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3))
  have hconj : (Om4.lr A B * Om4.frM τ) * Om4.rho (diagOf a, diagOf a⁻¹) *
      (Om4.lr A B * Om4.frM τ)⁻¹ = Om4.rho (diagOf a, diagOf a⁻¹) := by
    rw [hcomm, mul_inv_cancel_right]
  rw [Om4.rho_apply, Om4.conj_isNS] at hconj
  obtain ⟨c, hc0, hcA, hcB⟩ := Om4.exists_smul_of_lr_eq hconj
  have eA := Om4.conj_map_apply hA (isUT_diagOf a) τ
  have eB := Om4.conj_map_apply hB (isUT_diagOf a⁻¹) τ
  have hA00 := congrFun (congrFun hcA 0) 0
  have hA11 := congrFun (congrFun hcA 1) 1
  rw [Matrix.smul_apply, smul_eq_mul, eA.1] at hA00
  rw [Matrix.smul_apply, smul_eq_mul, eA.2] at hA11
  have hA00' : (a : K) = c * τ (a : K) := hA00
  have hA11' : ((a⁻¹ : Kˣ) : K) = c * τ ((a⁻¹ : Kˣ) : K) := hA11
  have hc1 : c = 1 := by
    have h4 : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h5 : τ (a : K) * τ ((a⁻¹ : Kˣ) : K) = 1 := by rw [← map_mul, h4, map_one]
    have h3 : c * c = 1 := by
      linear_combination (-(c * c)) * h5 - (c * τ (a : K)) * hA11' -
        ((a⁻¹ : Kˣ) : K) * hA00' + h4
    have h6 : (c - 1) ^ 2 = 0 := by linear_combination h3 + (1 - c) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h6)
  rw [hc1, one_mul] at hA00'
  clear hA00 hA11
  have hτ : τ = 1 := by
    by_contra hτ1
    have h3 := frob_of_ne_one hK4 hτ1 (a : K)
    rw [← hA00'] at h3
    have h4 : (a : K) * ((a : K) - 1) = 0 := by linear_combination -h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact ha0 h
    · exact ha' (sub_eq_zero.mp h)
  subst hτ
  rw [Om4.frM_one, mul_one] at hk ⊢
  rw [hc1, one_smul] at hcA
  rw [hc1, inv_one, one_smul] at hcB
  have hmap : ∀ g : GL (Fin 2) K, GeneralLinearGroup.map (1 : K ≃+* K).toRingHom g = g := by
    intro g
    ext i j
    rfl
  rw [hmap] at hcA hcB
  have hAd : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have h3 : (A : Matrix (Fin 2) (Fin 2) K) * (diagOf a : Matrix (Fin 2) (Fin 2) K) =
        (diagOf a : Matrix (Fin 2) (Fin 2) K) * A := by
      have h4 := congrArg (fun M => M * (A : Matrix (Fin 2) (Fin 2) K)) hcA
      simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h4
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        at h4
      exact h4.symm
    have h5 := congrFun (congrFun h3 0) 1
    unfold Om4.IsUT at hA
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_diagOf] at h5
    have h6 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (((a⁻¹ : Kˣ) : K) - a) = 0 := by
      rw [Units.val_inv_eq_inv_val]
      linear_combination h5
    exact (mul_eq_zero.mp h6).resolve_right (sub_ne_zero.mpr hainv.symm)
  have hBd : (B : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have h3 : (B : Matrix (Fin 2) (Fin 2) K) * (diagOf a⁻¹ : Matrix (Fin 2) (Fin 2) K) =
        (diagOf a⁻¹ : Matrix (Fin 2) (Fin 2) K) * B := by
      have h4 := congrArg (fun M => M * (B : Matrix (Fin 2) (Fin 2) K)) hcB
      simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h4
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        at h4
      exact h4.symm
    have h5 := congrFun (congrFun h3 0) 1
    unfold Om4.IsUT at hB
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_diagOf] at h5
    have h6 : (B : Matrix (Fin 2) (Fin 2) K) 0 1 * ((a : K) - ((a⁻¹ : Kˣ) : K)) = 0 := by
      rw [Units.val_inv_eq_inv_val]
      linear_combination h5
    exact (mul_eq_zero.mp h6).resolve_right (sub_ne_zero.mpr hainv)
  rw [Om4.lr_pow] at hk
  obtain ⟨c', hc'0, hA2, hB2⟩ := Om4.exists_smul_of_lr_eq_one hk
  unfold Om4.IsUT at hA hB
  have pA : ∀ m : ℕ, ((A ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(A : Matrix (Fin 2) (Fin 2) K) 0 0 ^ m, 0; 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1 ^ m] := by
    intro m
    induction m with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
    | succ m ih =>
      rw [pow_succ, Units.val_mul, ih]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA, hAd, pow_succ]
  have pB : ∀ m : ℕ, ((B ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(B : Matrix (Fin 2) (Fin 2) K) 0 0 ^ m, 0; 0, (B : Matrix (Fin 2) (Fin 2) K) 1 1 ^ m] := by
    intro m
    induction m with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
    | succ m ih =>
      rw [pow_succ, Units.val_mul, ih]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hB, hBd, pow_succ]
  rw [pA] at hA2
  rw [pB] at hB2
  have a00 := congrFun (congrFun hA2 0) 0
  have a11 := congrFun (congrFun hA2 1) 1
  have b00 := congrFun (congrFun hB2 0) 0
  have b11 := congrFun (congrFun hB2 1) 1
  simp at a00 a11 b00 b11
  have hAeq : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    eq_of_pow_two_pow_eq (a11.trans a00.symm)
  have hBeq : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = (B : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    eq_of_pow_two_pow_eq (b11.trans b00.symm)
  have hAB : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h3 : ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 ^ k =
        1 ^ 2 ^ k := by
      rw [mul_pow, a00, b00, one_pow, mul_inv_cancel₀ hc'0]
    exact eq_of_pow_two_pow_eq h3
  have hA0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hAB
  have h1 : Om4.lr A B = Om4.lr 1 1 := by
    refine (Om4Pt.lr_eq_of_smul hA0 ?_ ?_)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hA, hAd, hAeq]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hB, hBd, hBeq, eq_inv_of_mul_eq_one_right hAB]
  rw [h1, Om4.lr_one]

end Om4Pt

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem L34.mem_normalizer_sup_of_mem {A B : Subgroup G} {b : G}
    (hA : b ∈ Subgroup.normalizer (A : Set G)) (hB : b ∈ Subgroup.normalizer (B : Set G)) :
    b ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine L34.mem_normalizer_of_forall fun v hv => ?_
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj b).toMonoidHom := sup_le
    (fun x hx => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA x).mp hx))
    (fun x hx => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB x).mp hx))
  exact hle hv

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem mem_centralizer_V_of_commute
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2) {t : G}
    (ht : t ∈ T) (htL : t ∈ Subgroup.normalizer (L : Set G)) {b : ↥(fsuL0 T L)} {a : Kˣ}
    (ha : a ≠ 1) (hb : ψ b = (diagOf a, diagOf a⁻¹)) (htb : t * b = b * t) :
    t ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have htM : t ∈ fsuM T L := Setup.T_le_fsuM ht
  obtain ⟨A, B, τ, hA, hB, hform⟩ := hc.exists_form_ut ht
  rcases hform with hform | hform
  ·
    have hbar : bar e ⟨t, S.hMN htM⟩ * bar e (Subgroup.inclusion S.L0_le_normalizer_V b) =
        bar e (Subgroup.inclusion S.L0_le_normalizer_V b) * bar e ⟨t, S.hMN htM⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext htb
    rw [hc.bar_L0, hb, hform] at hbar
    obtain ⟨k, hk⟩ := (S.hyp.fsu.sylow.1) ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hpow : (Om4.lr A B * Om4.frM τ) ^ 2 ^ k = 1 := by
      rw [← hform, ← map_pow]
      have : (⟨t, S.hMN htM⟩ : ↥(Subgroup.normalizer (fsuV T I : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact htk)
      rw [this, map_one]
    have h1 := Om4Pt.eq_one_of_commute_diag hK4 hA hB ha hbar hpow
    rw [← hform] at h1
    exact mem_centralizer_of_bar e _ h1
  · exact absurd htL (hc.not_mem_normalizer_L_of_swap h37c h38c htM hform)

end IsCoord

variable (S : Setup T L I n)
include S

theorem inf_le_of_l34 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    {K B D : Subgroup G}
    (hStab : T ⊓ K ≤ Subgroup.normalizer (L : Set G)) (hB3 : Nat.card B = 3)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    T ⊓ K ≤ (T ⊓ fsuL0 T L) ⊔ (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQ
  set R := (T ⊓ fsuL0 T L) ⊔ Q with hR
  set Y := (T ⊓ K) ⊔ R with hY
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hBD' : B ≤ D := hBD ▸ inf_le_left
  have hBL : B ≤ fsuL0 T L := hBD'.trans hDL
  have hYT : Y ≤ T := sup_le inf_le_left (sup_le inf_le_left inf_le_left)
  have hY2 : IsPGroup 2 Y := S.hyp.fsu.sylow.1.to_le hYT
  have hBR : B ≤ Subgroup.normalizer (R : Set G) := by
    intro b hb
    have hbD := hBD' hb
    have h1 : b ∈ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := (hD.1 hbD).2
    have h3 : b ∈ Subgroup.normalizer (Q : Set G) :=
      S.L0T_le_normalizer_Q (Subgroup.mem_sup_left (hDL hbD))
    exact L34.mem_normalizer_sup_of_mem h1 h3
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := fun b hb =>
    L34.mem_normalizer_sup_of_mem (hBTK hb) (hBR hb)
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) := by
    refine sup_le hStab (sup_le ?_ ?_)
    · rintro x ⟨-, hxL0⟩
      have hform : bar e ⟨x, S.hMN (Setup.L0_le_fsuM hxL0)⟩ =
          Om4.lr (Matrix.SpecialLinearGroup.toGL (ψ ⟨x, hxL0⟩).1)
            (Matrix.SpecialLinearGroup.toGL (ψ ⟨x, hxL0⟩).2) * Om4.frM 1 := by
        rw [Om4.frM_one, mul_one, show (⟨x, S.hMN (Setup.L0_le_fsuM hxL0)⟩ :
          ↥(Subgroup.normalizer (fsuV T I : Set G))) =
          Subgroup.inclusion S.L0_le_normalizer_V ⟨x, hxL0⟩ from rfl, hc.bar_L0, Om4.rho_apply]
      exact hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c (Setup.L0_le_fsuM hxL0) hform
    · rintro x ⟨hxT, hxC⟩
      have hform : bar e ⟨x, S.hMN (Setup.T_le_fsuM hxT)⟩ = Om4.lr 1 1 * Om4.frM 1 := by
        rw [bar_eq_one_of_mem_centralizer e _ hxC, Om4.frM_one, mul_one, Om4.lr_one]
      exact hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c (Setup.T_le_fsuM hxT) hform
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hall
    push Not at hall
    have : B = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [this, Subgroup.card_bot] at hB3
    norm_num at hB3
  obtain ⟨a, a', hψb⟩ := IsCoord.exists_diag_of_mem hdiag (hBD' hbB) (hDL (hBD' hbB))
  have hbV1 : b ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    have h := hbB
    rw [hBD] at h
    exact h.2
  have haa' : a * a' = 1 := (hc.mem_centralizer_V1_iff_diag ⟨b, hDL (hBD' hbB)⟩ a a' hψb).mp hbV1
  have ha' : a' = a⁻¹ := eq_inv_of_mul_eq_one_right haa'
  rw [ha'] at hψb
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hb1
    have hd1 : diagOf (1 : Fˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hψ1 : ψ ⟨b, hDL (hBD' hbB)⟩ = 1 := by
      rw [hψb, inv_one, hd1, Prod.mk_one_one]
    have hodd : Odd (orderOf b) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard (hBD' hbB))
    exact hc.eq_one_of_odd h37c h38c ⟨b, hDL (hBD' hbB)⟩ hodd hψ1
  have hCY : Y ⊓ Subgroup.centralizer (B : Set G) ≤ Q := by
    rintro y ⟨hy, hyC⟩
    refine ⟨hYT hy, hc.mem_centralizer_V_of_commute h37c h38c h2 (hYT hy) (hYL hy) ha1 hψb ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hyC b hbB).symm
  have hcomm : ⁅Y, B⁆ ≤ T ⊓ fsuL0 T L := by
    rw [Subgroup.commutator_le]
    intro y hy c hc'
    have hcL : c ∈ fsuL0 T L := hBL hc'
    refine ⟨?_, ?_⟩
    · have h1 : c * y⁻¹ * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hBY hc') _).mp (Y.inv_mem hy)
      have h3 : y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) := by group
      rw [commutatorElement_def, h3]
      exact T.mul_mem (hYT hy) (hYT h1)
    · have h1 : y * c * y⁻¹ ∈ fsuL0 T L :=
        (Subgroup.mem_normalizer_iff.mp (Setup.T_le_normalizer_L0 (hYT hy)) c).mp hcL
      rw [commutatorElement_def]
      exact (fsuL0 T L).mul_mem h1 ((fsuL0 T L).inv_mem hcL)
  have hcop : Nat.Coprime (Nat.card B) (Nat.card Y) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hY2
    rw [hB3, hm]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hdec := CFSG.LocalAnalysis.EvenBN.TwoF4.inf_centralizer_sup_commutator_eq hBY
    (by have := hY2.isNilpotent; infer_instance) hcop
  calc T ⊓ K ≤ Y := le_sup_left
    _ = (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ ⁅Y, B⁆ := hdec.symm
    _ ≤ R := sup_le (hCY.trans le_sup_right) (hcomm.trans le_sup_left)

theorem normalizer_of_l34
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34) (h312 : A312ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h2 : n = 2) (h1 : zQ T I = fsuV T I)
    {H K B D : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn2 : E1.nParam H = 2)
    (hHK : H = K ⊔ T) (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hStab : T ⊓ K ≤ Subgroup.normalizer (L : Set G)) :
    D ≤ Subgroup.normalizer (K : Set G) ∧
      K ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
        ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQ
  set R := (T ⊓ fsuL0 T L) ⊔ Q with hR
  have hTKR := S.inf_le_of_l34 h37 h38 h37c h38c h2 hStab hB3 hBTK hD hBD
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := by
    have hRT : R ≤ T := sup_le inf_le_left inf_le_left
    have hR2 : IsPGroup 2 R := hT2.to_le hRT
    have hR1 : R ≠ ⊥ := by
      intro h0
      apply S.fsuV_ne_bot
      exact le_bot_iff.mp (h0 ▸ (S.fsuV_le_Q.trans le_sup_right))
    have hDTR : D ⊔ T ≤ Subgroup.normalizer (R : Set G) := by
      refine sup_le (fun d hd => ?_) (fun t ht => ?_)
      · exact L34.mem_normalizer_sup_of_mem (hD.1 hd).2
          (S.L0T_le_normalizer_Q (Subgroup.mem_sup_left (hDL hd)))
      · exact L34.mem_normalizer_sup_of_mem (Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer ht, Setup.T_le_normalizer_L0 ht⟩)
          (S.L0T_le_normalizer_Q (Subgroup.mem_sup_right ht))
    have hM₀ : InH T (D ⊔ T) := by
      refine ⟨le_sup_right, fun h0 => hR1 ?_⟩
      have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hRT.trans le_sup_right) hDTR hR2
      exact le_bot_iff.mp (h0 ▸ hle)
    have hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
      have hInM : InM T (fsuM T L) := ⟨S.uniq.1.1, le_sup_right.trans S.uniq.1.2⟩
      obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hfsu.sylow
      have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hInM.2)
      rw [hP] at this
      exact ⟨_, this⟩
    have hO2 : oTwoUpper H = K := by
      refine le_antisymm ?_ ?_
      · rw [hHK]
        exact S1567.oTwoUpper_sup_le hTK hT2
      · exact perfect_le_oTwoUpper hKH (Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKc))
    have hTHs : IsSylowTwoOf T H :=
      CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
    have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
      rw [hHK]
      exact sup_le Subgroup.le_normalizer hTK
    have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
    have hKR : K ⊓ R = T ⊓ K :=
      le_antisymm (fun x hx => ⟨hRT hx.2, hx.1⟩) (fun x hx => ⟨hx.2, hTKR hx⟩)
    have hRS : IsSylowTwoOf R (oTwoUpper H ⊔ R) := by
      rw [hO2]
      refine ⟨le_sup_right, hR2, ?_⟩
      have hRK : R ≤ Subgroup.normalizer (K : Set G) := hRT.trans hTK
      have hcard := CFSG.ShultStronglyClosedTI.LinearChain.card_sup_mul_card_inf_of_le_normalizer
        hRK
      rw [hKR] at hcard
      have h1 := Subgroup.relIndex_mul_card (H := R) (K := K ⊔ R)
      rw [inf_eq_left.mpr le_sup_right] at h1
      have h3 := Subgroup.relIndex_mul_card (H := T ⊓ K) (K := K)
      rw [inf_eq_left.mpr inf_le_right] at h3
      have hidx : R.relIndex (K ⊔ R) = (T ⊓ K).relIndex K := by
        have hpos : 0 < Nat.card ↥(T ⊓ K) := Nat.card_pos
        have hposR : 0 < Nat.card ↥R := Nat.card_pos
        apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposR hpos)
        calc R.relIndex (K ⊔ R) * (Nat.card ↥R * Nat.card ↥(T ⊓ K))
            = (R.relIndex (K ⊔ R) * Nat.card ↥R) * Nat.card ↥(T ⊓ K) := by ring
          _ = Nat.card ↥K * Nat.card ↥R := by rw [h1, hcard]
          _ = ((T ⊓ K).relIndex K * Nat.card ↥(T ⊓ K)) * Nat.card ↥R := by rw [h3]
          _ = (T ⊓ K).relIndex K * (Nat.card ↥R * Nat.card ↥(T ⊓ K)) := by ring
      have h4 := hTKs.2.2
      unfold Subgroup.relIndex at hidx
      rw [hidx]
      exact h4
    obtain ⟨R₀, hR₀1, hR₀R, hR₀N⟩ := theorem311_of_C58 hC58 hfsu.simple hfsu.nonabelian hfsu.qtke
      hfsu.sylow hM₀ hH.1 hu hR1 hRT hRS hDTR
    have hloc : IsTwoLocal (Subgroup.normalizer (R₀ : Set G)) :=
      ⟨R₀, hR₀1, hR2.to_le hR₀R, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hU := S.isUniqueM_normalizer_of_l34 hM hM23 h312 h37c h37 h38 h39 hE22 h331 hH hn1 hHK
      hKc hTK hJ hKL
    have hHM' : H ≤ M' := (le_sup_right.trans hR₀N).trans hle
    have hM'eq : M' = Subgroup.normalizer (K : Set G) := hU.2 M' ⟨hM', hHM'⟩
    intro d hd
    rw [← hM'eq]
    exact hle (hR₀N (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd)))
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  have hZK : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    have hZ := S.le_centerOf h37c h38c hC58 h317 h1 hH
    intro k hk
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hZ hz).2 k (hKH hk)).symm
  have hBN : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G) := hBD ▸ hBK.trans Subgroup.le_normalizer
  exact hc.first_red h2 h1 hdiag hDL hZK hBN (fun d hd _ _ => hDK hd)

end Setup

end CFSG.Quasithin.H13.Ch9
