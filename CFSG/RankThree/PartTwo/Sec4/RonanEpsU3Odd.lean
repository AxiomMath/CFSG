module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowU3
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowL3
public import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open Matrix

theorem u3OddEps_exists_cube_root_of_comm_involution {F : Type} [Field F] [CharP F 2]
    {B T : Matrix (Fin 3) (Fin 3) F} {c : F} (hB : B ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hT : T * T = 1) (hT1 : T ≠ 1) (hcomm : T * B = B * T) : ∃ μ : F, μ ^ 3 = c := by
  have h2 : ∀ M : Matrix (Fin 3) (Fin 3) F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  have hN : T - 1 ≠ 0 := sub_ne_zero.mpr hT1
  have hNN : (T - 1) * (T - 1) = 0 := by
    calc (T - 1) * (T - 1) = T * T - (T + T) + 1 := by noncomm_ring
      _ = 0 := by rw [hT, h2 T, sub_zero, h2 1]
  have hgN : B * (T - 1) = (T - 1) * B := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hcomm]
  obtain ⟨v, μ, hv, hgv⟩ := exists_eigenvector_of_commute_sq_zero hN hNN hgN
  exact ⟨μ, pow_three_eq_of_eigenvector hB hv hgv⟩

theorem u3OddEps_eq_zero_of_commute_diagonal_sq_zero {F : Type} [Field F] {d : Fin 3 → F}
    (hd : ∀ i j, i ≠ j → d i ≠ d j) {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M * diagonal d = diagonal d * M) (hM2 : M * M = 0) : M = 0 := by
  have hent : ∀ i j, M i j * d j = d i * M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have key : (d i - d j) * M i j = 0 := by linear_combination -(hent i j)
    exact (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr (hd i j hij))
  have hdiag : ∀ i, M i i = 0 := by
    intro i
    have h := congrFun (congrFun hM2 i) i
    fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_three, hoff] using h
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [hdiag]
  · simp [hoff i j hij]

theorem u3OddEps_sigma_mul_self_eq_one_of_diagonal {F : Type} [Field F] (σ : F ≃+* F)
    {B g : Matrix (Fin 3) (Fin 3) F} {d : Fin 3 → F} (hBu : conjTr σ B * B = 1) (hg : IsUnit g)
    (hBg : B * g = g * diagonal d) (h12 : d 1 = d 2) : σ (d 1) * d 1 = 1 := by
  set G := conjTr σ g * g with hGdef
  have hGD : conjTr σ (diagonal d) * G * diagonal d = G := by
    have h1 : conjTr σ (B * g) * (B * g) = G := by
      rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ B), hBu, Matrix.one_mul]
    rw [hBg, conjTr_mul, Matrix.mul_assoc] at h1
    calc conjTr σ (diagonal d) * G * diagonal d
        = conjTr σ (diagonal d) * (conjTr σ g * (g * diagonal d)) := by
          rw [hGdef]; simp only [Matrix.mul_assoc]
      _ = G := h1
  have hentry : ∀ i j, G i j = σ (d i) * G i j * d j := by
    intro i j
    have := congrFun (congrFun hGD i) j
    rw [conjTr_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this.symm
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hg).ne_zero
  have hGdet : G.det ≠ 0 := by
    rw [hGdef, det_mul, det_conjTr]
    exact mul_ne_zero ((map_ne_zero σ).mpr hgdet) hgdet
  by_contra hne
  have e11 := hentry 1 1
  have e12 := hentry 1 2
  have e21 := hentry 2 1
  have e22 := hentry 2 2
  rw [← h12] at e12 e21 e22
  have hk : (1 - σ (d 1) * d 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have z11 : G 1 1 = 0 := (mul_eq_zero.mp (by linear_combination e11 : (1 - σ (d 1) * d 1) * G 1 1 = 0)).resolve_left hk
  have z12 : G 1 2 = 0 := (mul_eq_zero.mp (by linear_combination e12 : (1 - σ (d 1) * d 1) * G 1 2 = 0)).resolve_left hk
  have z21 : G 2 1 = 0 := (mul_eq_zero.mp (by linear_combination e21 : (1 - σ (d 1) * d 1) * G 2 1 = 0)).resolve_left hk
  have z22 : G 2 2 = 0 := (mul_eq_zero.mp (by linear_combination e22 : (1 - σ (d 1) * d 1) * G 2 2 = 0)).resolve_left hk
  apply hGdet
  rw [Matrix.det_fin_three]
  simp [z11, z12, z21, z22]

theorem u3OddEps_exists_unitary_of_rank_one {F : Type} [Field F] (σ : F ≃+* F) (hσ : IsUnitaryInvolution σ)
    {B g : Matrix (Fin 3) (Fin 3) F} {c t : F} (hBu : conjTr σ B * B = 1) (hg : IsUnit g)
    (hBg : B * g = g * diagonal ![c * t, c, c]) (hc0 : c ≠ 0) (ht1 : t ≠ 1)
    (hσt : σ t * t = 1) :
    ∃ g'' : Matrix (Fin 3) (Fin 3) F, conjTr σ g'' * g'' = 1 ∧
      B * g'' = g'' * diagonal ![c, c, c * t] := by
  have hσc : σ c * c = 1 := u3OddEps_sigma_mul_self_eq_one_of_diagonal σ hBu hg hBg rfl
  have hd : ∀ i, σ (![c * t, c, c] i) * ![c * t, c, c] i = 1 := by
    intro i
    fin_cases i
    · show σ (c * t) * (c * t) = 1
      calc σ (c * t) * (c * t) = (σ c * c) * (σ t * t) := by rw [map_mul]; ring
        _ = 1 := by rw [hσc, hσt, mul_one]
    · exact hσc
    · exact hσc
  have h01 : (![c * t, c, c] : Fin 3 → F) 0 ≠ ![c * t, c, c] 1 := by
    intro h
    apply ht1
    have h' : c * t = c := h
    have : c * (t - 1) = 0 := by linear_combination h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0)
  obtain ⟨g', hg'u, hBg'⟩ := exists_unitary_conj hσ hd (Or.inr ⟨h01, rfl⟩) hBu hg hBg
  set P : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0] with hP
  have hσP : conjTr σ P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, hP]
  have hPP : P * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_three]
  have hPD : diagonal ![c * t, c, c] * P = P * diagonal ![c, c, c * t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_three, diagonal]
  refine ⟨g' * P, ?_, ?_⟩
  · rw [conjTr_mul, hσP, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ g'), hg'u, Matrix.one_mul,
      hPP]
  · rw [← Matrix.mul_assoc, hBg', Matrix.mul_assoc, hPD, ← Matrix.mul_assoc]


theorem u3OddEps_eq_zero_of_regular {F : Type} [Field F] {d : Fin 3 → F}
    (hd : ∀ i j, i ≠ j → d i ≠ d j) {N X g : Matrix (Fin 3) (Fin 3) F} (hg : IsUnit g)
    (hX : X * g = g * diagonal d) (hNX : N * X = X * N) (hN2 : N * N = 0) : N = 0 := by
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  set gi := g⁻¹ with hgi
  have h1 : g * gi = 1 := Matrix.mul_nonsing_inv g hdet
  have h2 : gi * g = 1 := Matrix.nonsing_inv_mul g hdet
  have hD : gi * X * g = diagonal d := by
    rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hM : diagonal d * (gi * N * g) = (gi * N * g) * diagonal d := by
    calc diagonal d * (gi * N * g) = (gi * X * g) * (gi * N * g) := by rw [hD]
      _ = gi * X * (g * gi) * N * g := by simp only [Matrix.mul_assoc]
      _ = gi * X * N * g := by rw [h1, Matrix.mul_one]
      _ = gi * (X * N) * g := by simp only [Matrix.mul_assoc]
      _ = gi * (N * X) * g := by rw [hNX]
      _ = gi * N * (X * g) := by simp only [Matrix.mul_assoc]
      _ = gi * N * (g * diagonal d) := by rw [hX]
      _ = (gi * N * g) * diagonal d := by simp only [Matrix.mul_assoc]
  have hM2 : (gi * N * g) * (gi * N * g) = 0 := by
    calc (gi * N * g) * (gi * N * g) = gi * N * (g * gi) * N * g := by simp only [Matrix.mul_assoc]
      _ = gi * (N * N) * g := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hN2]; simp
  have hM0 := u3OddEps_eq_zero_of_commute_diagonal_sq_zero hd hM.symm hM2
  calc N = (g * gi) * N * (g * gi) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = g * (gi * N * g) * gi := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hM0]; simp

theorem u3OddEps_map_commutator_comap_eq_of_surjective {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) (K : Subgroup Q) [Group.IsPerfect K] :
    Subgroup.map π ⁅K.comap π, K.comap π⁆ = K := by
  rw [Subgroup.map_commutator]
  have hm : Subgroup.map π (K.comap π) = K := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hπ, top_inf_eq]
  rw [hm]
  have h1 : (⁅(⊤ : Subgroup K), ⊤⁆ : Subgroup K) = ⊤ := by
    rw [← commutator_def K]
    exact Group.isPerfect_def.mp inferInstance
  have h2 := Subgroup.map_commutator (⊤ : Subgroup K) (⊤ : Subgroup K) K.subtype
  rw [h1] at h2
  have hT : Subgroup.map K.subtype (⊤ : Subgroup K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hT] at h2
  exact h2.symm

theorem commutator_le_suCentralizer {n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 n F}
    (B : unitaryIsom3 h) (H : Subgroup (unitarySU 2 n F 3))
    (hfix : ∀ a ∈ H, ∃ z ∈ unitaryScalars h 3, suConj h B a = a * z) :
    ⁅H, H⁆ ≤ suCentralizer (2 ^ n) (B : GL (Fin 3) F) := by
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  obtain ⟨za, hza, hA⟩ := hfix a ha
  obtain ⟨zb, hzb, hB⟩ := hfix b hb
  have key : suConj h B ⁅a, b⁆ = ⁅a, b⁆ := by
    rw [map_commutatorElement, hA, hB,
      commutatorElement_mul_central_eq (unitaryScalars_le_center h 3 hza)
        (unitaryScalars_le_center h 3 hzb)]
  have h1 : ((suConj h B ⁅a, b⁆ : unitarySU 2 n F 3) : GL (Fin 3) F) =
      ((⁅a, b⁆ : unitarySU 2 n F 3) : GL (Fin 3) F) := by rw [key]
  rw [coe_suConj, Subgroup.coe_inv] at h1
  rw [mem_suCentralizer]
  calc ((⁅a, b⁆ : unitarySU 2 n F 3) : GL (Fin 3) F) * (B : GL (Fin 3) F)
      = ((B : GL (Fin 3) F) * ((⁅a, b⁆ : unitarySU 2 n F 3) : GL (Fin 3) F) *
          (B : GL (Fin 3) F)⁻¹) * (B : GL (Fin 3) F) := by rw [h1]
    _ = (B : GL (Fin 3) F) * ((⁅a, b⁆ : unitarySU 2 n F 3) : GL (Fin 3) F) := by group

theorem forall_comm_scalar_of_le_autFix {n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 n F}
    (B : unitaryIsom3 h) (K : Subgroup (unitaryPSU h 3))
    (hK : K ≤ autFix (psuConj h B)) :
    ∀ a ∈ K.comap (unitaryProj h 3), ∃ z ∈ unitaryScalars h 3, suConj h B a = a * z := by
  intro a ha
  have h1 : psuConj h B (unitaryProj h 3 a) = unitaryProj h 3 a := mem_autFix.mp (hK ha)
  have h2 : ((suConj h B a : unitarySU 2 n F 3) : unitaryPSU h 3) =
      ((a : unitarySU 2 n F 3) : unitaryPSU h 3) := by
    rw [← psuConj_mk]
    exact h1
  exact ⟨a⁻¹ * suConj h B a, QuotientGroup.eq.mp h2.symm, (mul_inv_cancel_left _ _).symm⟩

theorem two_dvd_card_suCentralizer_of_cfgSEps {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {h : UnitaryFieldData 2 n F} [Finite (unitaryPSU h 3)] {A : Subgroup (MulAut (unitaryPSU h 3))}
    {B : unitaryIsom3 h} {K : Subgroup (unitaryPSU h 3)}
    (hc : CfgSEps (unitaryPSU h 3) A (psuConj h B) K) :
    2 ∣ Nat.card (suCentralizer (2 ^ n) (B : GL (Fin 3) F)) := by
  haveI := hc.isPerfect
  have hK₁ := commutator_le_suCentralizer B (K.comap (unitaryProj h 3))
    (forall_comm_scalar_of_le_autFix B K hc.le_autFix)
  have hmap := u3OddEps_map_commutator_comap_eq_of_surjective (unitaryProj h 3)
    (unitaryProj_surjective h 3) K
  have h1 : Nat.card K ∣ Nat.card ↥⁅K.comap (unitaryProj h 3), K.comap (unitaryProj h 3)⁆ := by
    have := Subgroup.card_map_dvd ⁅K.comap (unitaryProj h 3), K.comap (unitaryProj h 3)⁆
      (unitaryProj h 3)
    rwa [hmap] at this
  have h2 : Nat.card ↥⁅K.comap (unitaryProj h 3), K.comap (unitaryProj h 3)⁆ ∣
      Nat.card (suCentralizer (2 ^ n) (B : GL (Fin 3) F)) := Subgroup.card_dvd_of_le hK₁
  have h3 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
  have h4 : 2 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) :=
    two_dvd_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)
  exact h4.trans (h3.trans (h1.trans h2))

theorem exists_scalar_of_psuConj_pow_three {n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 n F}
    (B : unitaryIsom3 h) (hB3 : psuConj h B ^ 3 = 1) :
    ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = (B : GL (Fin 3) F) ^ 3 := by
  have hB3' : psuConj h (B ^ 3) = 1 := by rw [map_pow, hB3]
  have h1 := (RonanK432.L3Outer.psuConj_eq_one_iff (B ^ 3)).mp hB3'
  have h2 := mk_eq_one_iff_mem_statedScalars.mp h1
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp
    (show ((B ^ 3 : unitaryIsom3 h) : GL (Fin 3) F) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 3) : Fˣ →* GL (Fin 3) F).range from h2)
  exact ⟨c, by rw [hc, Subgroup.coe_pow]⟩

theorem false_of_diagonal_psuConj {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {h : UnitaryFieldData 2 n F} (hn1 : 1 ≤ n) (hq : 4 ≤ 2 ^ n) [Finite (unitaryPSU h 3)]
    {A : Subgroup (MulAut (unitaryPSU h 3))} {K : Subgroup (unitaryPSU h 3)}
    {B₀ : unitaryIsom3 h} {l m : F}
    (hD : ((B₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![l, l, m])
    (hlm : l ≠ m) (hc : CfgSEps (unitaryPSU h 3) A (psuConj h B₀) K) : False := by
  obtain ⟨F₀, _, hfin₀, hF₀, ⟨ι⟩⟩ := exists_perfectResidual_psuFixed_mulEquiv h hq hlm hD
  have hfix : autFix (psuConj h B₀) =
      (suCentralizer (2 ^ n) (B₀ : GL (Fin 3) F)).map (unitaryProj h 3) := by
    ext z
    rw [mem_autFix, mem_map_suCentralizer_iff h hD z]
  have hNeq : inSubgroup perfectResidual (autFix (psuConj h B₀)) =
      inSubgroup perfectResidual ((suCentralizer (2 ^ n) (B₀ : GL (Fin 3) F)).map
        (unitaryProj h 3)) := by rw [hfix]
  have ι' : ↥(inSubgroup perfectResidual (autFix (psuConj h B₀))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F₀ :=
    (MulEquiv.subgroupCongr hNeq).trans ι
  have hF₀4 : 4 ≤ Nat.card F₀ := by rw [hF₀]; exact hq
  haveI : CharP F₀ 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two (by rw [hF₀])
  have hK' : K ≤ inSubgroup perfectResidual (autFix (psuConj h B₀)) := hc.le_perfectResidual
  have hNC : inSubgroup perfectResidual (autFix (psuConj h B₀)) ≤ autFix (psuConj h B₀) :=
    Subgroup.map_subtype_le _
  have hNq : IsQuasisimple ↥(inSubgroup perfectResidual (autFix (psuConj h B₀))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ι'.symm (RonanKChevTwo.SpFour.isQuasisimple_sl2 hF₀4)
  have hZ : Subgroup.center ↥(inSubgroup perfectResidual (autFix (psuConj h B₀))) = ⊥ :=
    RonanK429.center_eq_bot_of_mulEquiv ι' Sec19.Item19Res2Proof.center_sl2_eq_bot
  have hcube : IsTypeEpsCube ↥(inSubgroup perfectResidual (autFix (psuConj h B₀))) :=
    hc.isTypeEpsCube_of_le hK' hNC hNq hZ
  have hcard : Nat.card ↥(inSubgroup perfectResidual (autFix (psuConj h B₀))) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr ι'.toEquiv, card_SL_two F₀, hF₀]
  exact not_isTypeEpsCube_of_card_sl2_even hn1 hcard hcube


theorem u3OddEps_mul_eq_diagonal_of_smul {F : Type} [Field F] {M g : Matrix (Fin 3) (Fin 3) F} {e t : F}
    (he : e ≠ 0) (hform : (e • M) * g = g * diagonal ![t, 1, 1]) :
    M * g = g * diagonal ![e⁻¹ * t, e⁻¹, e⁻¹] := by
  have hdiag : e⁻¹ • (diagonal ![t, 1, 1] : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![e⁻¹ * t, e⁻¹, e⁻¹] := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [diagonal, Matrix.smul_apply]
    · simp [diagonal, Matrix.smul_apply, hij]
  calc M * g = (e⁻¹ • (e • M)) * g := by rw [smul_smul, inv_mul_cancel₀ he, one_smul]
    _ = e⁻¹ • ((e • M) * g) := by rw [smul_mul]
    _ = e⁻¹ • (g * diagonal ![t, 1, 1]) := by rw [hform]
    _ = g * (e⁻¹ • diagonal ![t, 1, 1]) := by rw [Matrix.mul_smul]
    _ = g * diagonal ![e⁻¹ * t, e⁻¹, e⁻¹] := by rw [hdiag]

theorem u3OddEps_false_of_rank_one {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {h : UnitaryFieldData 2 n F} (hPi : PiField false 2 n F) (hn1 : 1 ≤ n) (hq4 : 4 ≤ 2 ^ n)
    (hq : ModThree false (2 ^ n)) [Finite (unitaryPSU h 3)]
    {A : Subgroup (MulAut (unitaryPSU h 3))} {B : unitaryIsom3 h} {K : Subgroup (unitaryPSU h 3)}
    (hc : CfgSEps (unitaryPSU h 3) A (psuConj h B) K) {c t : F} (hc0 : c ≠ 0) (ht1 : t ≠ 1)
    (ht3 : t ^ 3 = 1) {g : Matrix (Fin 3) (Fin 3) F} (hg : IsUnit g)
    (hBg : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * g = g * diagonal ![c * t, c, c]) :
    False := by
  have hσ : IsUnitaryInvolution (CFSG.LieType.BorelTits.unitaryInvolution F 2 n) :=
    isUnitaryInvolution_unitaryInvolution (by rw [hPi.card]; rfl)
  have hBu : conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 n)
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [conjTr_unitaryInvolution_eq hPi]
    exact mem_unitaryIsom3.mp B.2
  have hσt : CFSG.LieType.BorelTits.unitaryInvolution F 2 n t * t = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree hq ht3
  obtain ⟨g'', hg''u, hBg''⟩ :=
    u3OddEps_exists_unitary_of_rank_one (CFSG.LieType.BorelTits.unitaryInvolution F 2 n) hσ hBu hg hBg hc0
      ht1 hσt
  have hgU : IsUnit g'' := (Matrix.isUnit_iff_isUnit_det g'').mpr (Matrix.isUnit_det_of_left_inverse hg''u)
  obtain ⟨W, hWval⟩ : ∃ W : GL (Fin 3) F, (W : Matrix (Fin 3) (Fin 3) F) = g'' :=
    ⟨hgU.unit, hgU.unit_spec⟩
  have hWmem : W ∈ unitaryIsom3 h := by
    refine mem_unitaryIsom3.mpr ?_
    rw [hWval, ← conjTr_unitaryInvolution_eq hPi]
    exact hg''u
  obtain ⟨W', hW'⟩ : ∃ W' : unitaryIsom3 h, ((W' : unitaryIsom3 h) : GL (Fin 3) F) = W :=
    ⟨⟨W, hWmem⟩, rfl⟩
  obtain ⟨B₀, hB₀def⟩ : ∃ B₀ : unitaryIsom3 h, B₀ = W'⁻¹ * B * W' := ⟨_, rfl⟩
  have hB₀ : ((B₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![c, c, c * t] := by
    have e1 : ((B₀ : unitaryIsom3 h) : GL (Fin 3) F) =
        (W : GL (Fin 3) F)⁻¹ * (B : GL (Fin 3) F) * W := by
      rw [hB₀def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hW']
    have hBW : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (W : Matrix (Fin 3) (Fin 3) F) =
        (W : Matrix (Fin 3) (Fin 3) F) * diagonal ![c, c, c * t] := by
      rw [hWval]
      exact hBg''
    rw [e1, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hBW, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have hlm : c ≠ c * t := by
    intro h1
    apply ht1
    have h2 : c * (1 - t) = 0 := by linear_combination h1
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hc0)).symm
  have key : ∀ y : unitaryPSU h 3, psuConj h W'⁻¹ (psuConj h W' y) = y := fun y => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hcongr : MulAut.congr (psuConj h W'⁻¹) (psuConj h B) = psuConj h B₀ := by
    apply MulEquiv.ext
    intro x
    have hs : (psuConj h W'⁻¹).symm x = psuConj h W' x :=
      (MulEquiv.symm_apply_eq _).mpr (key x).symm
    show psuConj h W'⁻¹ (psuConj h B ((psuConj h W'⁻¹).symm x)) = psuConj h B₀ x
    rw [hs, hB₀def, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  have hc' := hc.map (psuConj h W'⁻¹)
  rw [hcongr] at hc'
  exact false_of_diagonal_psuConj hn1 hq4 hB₀ hlm hc'

theorem u3OddEps_tau_facts {F : Type} [Field F] {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    τ ≠ 0 ∧ τ ^ 2 ≠ 1 ∧ τ ≠ τ ^ 2 := by
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ3; norm_num at hτ3
  refine ⟨hτ0, fun h2 => ?_, fun h2 => ?_⟩
  · have h3 : τ ^ 3 = τ := by
      calc τ ^ 3 = τ ^ 2 * τ := by ring
        _ = τ := by rw [h2, one_mul]
    exact hτ1 (h3.symm.trans hτ3)
  · have h3 : τ * (1 - τ) = 0 := by linear_combination h2
    exact hτ1 (sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hτ0)).symm

theorem u3OddEps_distinct_tau {F : Type} [Field F] {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ∀ i j : Fin 3, i ≠ j → (![τ, τ ^ 2, 1] : Fin 3 → F) i ≠ ![τ, τ ^ 2, 1] j := by
  obtain ⟨-, hτ2, hττ2⟩ := u3OddEps_tau_facts hτ3 hτ1
  have h01 : τ ≠ τ ^ 2 := hττ2
  have h02 : τ ≠ 1 := hτ1
  have h12 : τ ^ 2 ≠ 1 := hτ2
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact h01 | exact h02 | exact h12
    | exact Ne.symm h01 | exact Ne.symm h02 | exact Ne.symm h12

theorem u3OddEps_false_of_inner_odd {n : ℕ} (hodd : Odd n) (hn2 : 2 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {h : UnitaryFieldData 2 n F} [Finite (unitaryPSU h 3)]
    {A : Subgroup (MulAut (unitaryPSU h 3))} {B : unitaryIsom3 h} {K : Subgroup (unitaryPSU h 3)}
    (hc : CfgSEps (unitaryPSU h 3) A (psuConj h B) K) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPi : PiField false 2 n F :=
    ⟨h.prime, h.one_le, by
      rw [h.card]
      change 2 ^ (2 * n) = (2 ^ n) ^ 2
      rw [← pow_mul, mul_comm]⟩
  have hq : ModThree false (2 ^ n) := by
    change 2 ^ n % 3 = 2
    exact two_pow_mod_three_of_odd hodd
  have hq4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hn1 : 1 ≤ n := by omega
  obtain ⟨τ, hτ3, hτ1⟩ := KFacts.exists_primitive_cube_root hPi
  obtain ⟨hτ0, hτ2, -⟩ := u3OddEps_tau_facts hτ3 hτ1
  have h3 : (3 : F) ≠ 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    intro h0
    have h1 : (1 : F) = 0 := by linear_combination h0 - h2
    exact one_ne_zero h1
  obtain ⟨c, hcB⟩ := exists_scalar_of_psuConj_pow_three B hc.pow_three
  have hBm3 : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) :=
    pow_three_matrix_eq_scalar hcB
  have hc0 : (c : F) ≠ 0 := Units.ne_zero c
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card_suCentralizer_of_cfgSEps hc)
  obtain ⟨Tg, hTg⟩ : ∃ Tg : GL (Fin 3) F, Tg = ((t : unitarySU 2 n F 3) : GL (Fin 3) F) :=
    ⟨_, rfl⟩
  have hTord : orderOf Tg = 2 := by
    rw [hTg, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have hT2 : Tg * Tg = 1 := by
    rw [← sq, ← hTord]
    exact pow_orderOf_eq_one Tg
  have hT1 : Tg ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hTord
    norm_num at hTord
  have hcommG : Tg * (B : GL (Fin 3) F) = (B : GL (Fin 3) F) * Tg := by
    rw [hTg]
    exact mem_suCentralizer.mp t.2
  have hcommM : (Tg : Matrix (Fin 3) (Fin 3) F) *
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (Tg : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, hcommG, Units.val_mul]
  have hTM2 : (Tg : Matrix (Fin 3) (Fin 3) F) * (Tg : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, hT2, Units.val_one]
  have hTM1 : (Tg : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h1 =>
    hT1 (Units.ext (by rw [h1, Units.val_one]))
  obtain ⟨μ, hμ⟩ := u3OddEps_exists_cube_root_of_comm_involution hBm3 hTM2 hTM1 hcommM
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hc0
    rw [← hμ, h0]
    norm_num
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin 3) (Fin 3) F,
      Y = μ⁻¹ • ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  have hY3 : Y ^ 3 = 1 := by
    rw [hY, smul_pow, hBm3, smul_smul, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, one_smul]
  have hYs : ∀ x : F, Y ≠ x • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro x hx
    have hBx : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (μ * x) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      calc ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = μ • (μ⁻¹ • ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
            rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
        _ = (μ * x) • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [← hY, hx, smul_smul]
    have hpow : (μ * x) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) F) =
        (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      calc (μ * x) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) F)
          = ((μ * x) • (1 : Matrix (Fin 3) (Fin 3) F)) ^ 3 := by rw [smul_pow, one_pow]
        _ = ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 := by rw [hBx]
        _ = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := hBm3
    have hac : (μ * x) ^ 3 = (c : F) := by
      have e := congrFun (congrFun hpow 0) 0
      simpa using e
    have ha0 : μ * x ≠ 0 := by
      intro h0
      apply hc0
      rw [← hac, h0]
      norm_num
    have hscalar : (B : GL (Fin 3) F) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (μ * x) ha0) := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact hBx
    exact hc.ne_one (psuConj_eq_one_of_coe_eq_scalar hscalar)
  obtain ⟨g, j, hgU, hform⟩ := exists_normal_form hτ3 hτ1 h3 hY3 hYs
  have h2 : ∀ M : Matrix (Fin 3) (Fin 3) F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  have hN0 : (Tg : Matrix (Fin 3) (Fin 3) F) - 1 ≠ 0 := sub_ne_zero.mpr hTM1
  have hN2 : ((Tg : Matrix (Fin 3) (Fin 3) F) - 1) * ((Tg : Matrix (Fin 3) (Fin 3) F) - 1) = 0 := by
    calc ((Tg : Matrix (Fin 3) (Fin 3) F) - 1) * ((Tg : Matrix (Fin 3) (Fin 3) F) - 1)
        = (Tg : Matrix (Fin 3) (Fin 3) F) * (Tg : Matrix (Fin 3) (Fin 3) F) -
          ((Tg : Matrix (Fin 3) (Fin 3) F) + (Tg : Matrix (Fin 3) (Fin 3) F)) + 1 := by
          noncomm_ring
      _ = 0 := by rw [hTM2, h2 _, sub_zero, h2 1]
  have hNB : ((Tg : Matrix (Fin 3) (Fin 3) F) - 1) *
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((Tg : Matrix (Fin 3) (Fin 3) F) - 1) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hcommM]
  have hNX : ∀ r : F, ((Tg : Matrix (Fin 3) (Fin 3) F) - 1) * (r • Y) =
      (r • Y) * ((Tg : Matrix (Fin 3) (Fin 3) F) - 1) := by
    intro r
    rw [hY]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hNB]
  have he : (τ ^ (j : ℕ) * μ⁻¹) ≠ 0 := mul_ne_zero (pow_ne_zero _ hτ0) (inv_ne_zero hμ0)
  have hτ2' : τ ^ 2 ≠ 1 := hτ2
  have hτ3' : (τ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
  rcases hform with hA | hB' | hC
  ·
    exact hN0 (u3OddEps_eq_zero_of_regular (u3OddEps_distinct_tau hτ3 hτ1) hgU hA (hNX _) hN2)
  ·
    rw [hY, smul_smul] at hB'
    have hBg := u3OddEps_mul_eq_diagonal_of_smul he hB'
    exact u3OddEps_false_of_rank_one hPi hn1 hq4 hq hc (inv_ne_zero he) hτ1 hτ3 hgU hBg
  ·
    rw [hY, smul_smul] at hC
    have hBg := u3OddEps_mul_eq_diagonal_of_smul he hC
    exact u3OddEps_false_of_rank_one hPi hn1 hq4 hq hc (inv_ne_zero he) hτ2' hτ3' hgU hBg

theorem u3OddInnerEps : U3OddInnerEps := by
  intro n hodd h hfin A α K hα hc
  obtain ⟨B, rfl⟩ := hα
  rcases eq_or_ne n 1 with rfl | hn1
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    have hsolv : Group.IsSolvable (projSU 3 2 1) :=
      CFSG.RankThree.PartTwo.Sec13.isSolvable_projSU_two
    haveI : Group.IsSolvable (unitaryPSU h 3) :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    haveI := hc.isPerfect
    haveI := hc.nontrivial
    exact Group.IsPerfect.not_isSolvable K inferInstance
  · obtain ⟨k, hk⟩ := hodd
    exact u3OddEps_false_of_inner_odd ⟨k, hk⟩ (by omega) hc

end CFSG.RankThree.PartTwo.Sec4.RonanEps
