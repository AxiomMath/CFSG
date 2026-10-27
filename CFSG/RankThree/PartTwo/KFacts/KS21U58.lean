module

public import CFSG.RankThree.PartTwo.KFacts.KS21TwoCentral
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.RankThree.CentralLiftU.UnitaryTriRoots
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U58

open Matrix CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.CentralLiftU
open CFSG.LieType.Chevalley (uSL coe_uSL)

abbrev K := GaloisField 2 (2 * 3)

theorem hK : UnitaryFieldData 2 3 K :=
  ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩

abbrev SU5 := hypSU hK 2 1

abbrev U5 := hypUnitriangular hK 2 1

abbrev Mat5 := Matrix (HypIndex 2 1) (HypIndex 2 1) K

abbrev mat (g : SU5) : Mat5 := ((g : GL (HypIndex 2 1) K) : Mat5)

abbrev iE1 : HypIndex 2 1 := .inl 0
abbrev iE2 : HypIndex 2 1 := .inl 1
abbrev iZ : HypIndex 2 1 := .inr (.inl 0)
abbrev iF2 : HypIndex 2 1 := .inr (.inr 1)
abbrev iF1 : HypIndex 2 1 := .inr (.inr 0)

theorem mat_mul (g h : SU5) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_injective : Function.Injective mat := fun _ _ h => Subtype.ext (Units.ext h)

theorem mat_pow (g : SU5) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

theorem two_eq_zero : (2 : K) = 0 := CharTwo.two_eq_zero

theorem bar_one : hK.bar 1 = 1 := map_one _

theorem h01 : (0 : Fin 2) ≠ 1 := by decide

@[expose] def x1 (t : K) : SU5 := rhoU (ε := 1) hK h01 (uSL t)

theorem x1_mem (t : K) : x1 t ∈ U5 := rhoU_uSL_mem (h := hK) (ε := 1) h01 (by decide) t

theorem mat_x1 (t : K) :
    mat (x1 t) = 1 + single iE1 iE2 t + single iF2 iF1 (-(hK.bar t)) := by
  rw [mat, x1, coe_rhoU]
  ext a b
  rcases a with a | a | a <;> rcases b with b | b | b <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat, embMat, quadIdx, rho4Mat, coe_uSL, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, one_apply, adjugate_fin_two]

theorem bar_eq (c : K) : hK.bar c = CFSG.LieType.BorelTits.unitaryInvolution K 2 3 c := by
  rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]

theorem card_K : Nat.card K = (2 ^ 3) ^ 2 := by
  rw [GaloisField.card 2 (2 * 3) (by norm_num)]
  norm_num

theorem exists_v : ∃ v : K, v + hK.bar v = -(1 * hK.bar 1) := by
  obtain ⟨c, hc⟩ := CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq card_K
    (a := -(1 * hK.bar 1)) (by rw [bar_one, mul_one, map_neg, map_one])
  exact ⟨c, by rw [bar_eq]; exact hc⟩

@[expose] def vElt : K := exists_v.choose

theorem vElt_spec : vElt + hK.bar vElt = -(1 * hK.bar 1) := exists_v.choose_spec

@[expose] def x2 : SU5 := kappaU hK 1 (heisU hK vElt_spec)

theorem x2_mem : x2 ∈ U5 := kappaU_mem_of_heisUpper (h := hK) 1 (heisU_mem hK _)

theorem mat_x2 : mat x2 = 1 + single iE2 iZ 1 + single iE2 iF2 vElt +
    single iZ iF2 (-(hK.bar 1)) := by
  rw [mat, x2, coe_kappaU, coe_heisU]
  ext a b
  rcases a with a | a | a <;> rcases b with b | b | b <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat, embMat, tripIdx, heisUMat, Matrix.mul_apply, Fin.sum_univ_three, one_apply]

theorem exists_bar_ne : ∃ t : K, hK.bar t ≠ t := by
  by_contra h
  push Not at h
  have htop : hK.fixedField = ⊤ := by
    rw [eq_top_iff]
    intro t _
    exact h t
  have h1 := hK.card_fixedField
  rw [htop] at h1
  have h2 : Nat.card (⊤ : Subfield K) = Nat.card K := Nat.card_congr Subfield.topEquiv.toEquiv
  rw [h2, GaloisField.card 2 (2 * 3) (by norm_num)] at h1
  norm_num at h1

theorem eq_one_add_single_of_mem_center {z : SU5} (hz : z ∈ U5)
    (hc : ∀ v ∈ U5, z * v = v * z) : ∃ c : K, mat z = 1 + single iE1 iF1 c := by
  obtain ⟨hbt, hdiag⟩ := mem_hypUnitriangular.mp hz
  have hbt' : (mat z).BlockTriangular fullPos := hbt
  have hdiag' : ∀ a, mat z a a = 1 := hdiag
  set N := mat z - 1 with hN
  have hlow : ∀ a b, fullPos b ≤ fullPos a → N a b = 0 := by
    intro a b hab
    rcases lt_or_eq_of_le hab with hlt | heq
    · rw [hN, Matrix.sub_apply, hbt' hlt, one_apply_ne]
      · simp
      · rintro rfl; exact lt_irrefl _ hlt
    · have hab' : a = b := fullPos_injective heq.symm
      subst hab'
      rw [hN, Matrix.sub_apply, hdiag' a, one_apply_eq, sub_self]
  have hcomm : ∀ v ∈ U5, N * (mat v - 1) = (mat v - 1) * N := by
    intro v hv
    have e : mat z * mat v = mat v * mat z := by rw [← mat_mul, ← mat_mul, hc v hv]
    calc N * (mat v - 1) = mat z * mat v - mat z - mat v + 1 := by rw [hN]; noncomm_ring
      _ = mat v * mat z - mat v - mat z + 1 := by rw [e]; abel
      _ = (mat v - 1) * N := by rw [hN]; noncomm_ring
  obtain ⟨t, ht⟩ := exists_bar_ne
  have c1 := hcomm _ (x1_mem 1)
  have c2 := hcomm _ x2_mem
  have c3 := hcomm _ (x1_mem t)
  rw [mat_x1, add_assoc, add_sub_cancel_left] at c1 c3
  rw [mat_x2, add_assoc, add_assoc, add_sub_cancel_left] at c2
  have l1 := hlow iE2 iE1 (by decide)
  have l2 := hlow iZ iE1 (by decide)
  have l3 := hlow iF2 iE1 (by decide)
  have l4 := hlow iF1 iE1 (by decide)
  have l5 := hlow iZ iE2 (by decide)
  have l6 := hlow iF2 iE2 (by decide)
  have l7 := hlow iF1 iE2 (by decide)
  have l8 := hlow iF2 iZ (by decide)
  have l9 := hlow iF1 iZ (by decide)
  have l10 := hlow iF1 iF2 (by decide)
  have d1 := hlow iE1 iE1 le_rfl
  have d2 := hlow iE2 iE2 le_rfl
  have d3 := hlow iZ iZ le_rfl
  have d4 := hlow iF2 iF2 le_rfl
  have d5 := hlow iF1 iF1 le_rfl
  have E1 := fun a b => congrFun₂ c1 a b
  have E2 := fun a b => congrFun₂ c2 a b
  have E3 := fun a b => congrFun₂ c3 a b
  have f1 : N iE2 iF2 = 0 := by
    have h := E1 iE2 iF1
    simpa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, single_apply, bar_one, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, d1, d2,
      d3, d4, d5] using h
  have g1 := E1 iE1 iF1
  have g2 := E2 iE1 iZ
  have g3 := E2 iE1 iF2
  have g4 := E2 iZ iF1
  have g5 := E2 iE2 iF1
  have g6 := E3 iE1 iF1
  have g7 := E1 iZ iF1
  have g8 := E1 iE1 iZ
  simp [Matrix.mul_apply, Fintype.sum_sum_type, single_apply, bar_one] at g1 g2 g3 g4 g5 g6 g7 g8
  have f4 : N iE1 iZ = 0 := by linear_combination vElt * g2 - g3
  have f5 : N iZ iF1 = 0 := by linear_combination -g5 - vElt * g4
  have f8 : N iE2 iZ = 0 := g8.symm
  have f6 : N iE1 iF2 = 0 := by
    have h0 : N iE1 iF2 * (t - hK.bar t) = 0 := by linear_combination g6 - t * g1
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm ht
  have f7 : N iE2 iF1 = 0 := by linear_combination -g1 - f6
  refine ⟨N iE1 iF1, ?_⟩
  have hz' : mat z = 1 + N := by rw [hN]; abel
  rw [hz']
  congr 1
  ext a b
  rcases a with a | a | a <;> rcases b with b | b | b <;> fin_cases a <;> fin_cases b <;>
    simp <;> assumption

theorem norm_eq_pow (c : K) : hK.norm c = c ^ 9 := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
  ring

theorem bar_eq_pow (c : K) : hK.bar c = c ^ 8 := by
  rw [UnitaryFieldData.bar_apply]
  norm_num

theorem exists_omega : ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply exists_prime_orderOf_dvd_card' 3
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card 2 (2 * 3) (by norm_num)]
  norm_num

@[expose] def ω3 : Kˣ := exists_omega.choose

theorem orderOf_ω3 : orderOf ω3 = 3 := exists_omega.choose_spec

abbrev A9 := ↥(Subgroup.zpowers ω3) × ↥(Subgroup.zpowers ω3)

theorem ω3_pow : ω3 ^ 3 = 1 := by
  have := pow_orderOf_eq_one ω3
  rwa [orderOf_ω3] at this

theorem pow_three_of_mem {x : Kˣ} (hx : x ∈ Subgroup.zpowers ω3) : x ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm k, _root_.zpow_mul, zpow_natCast, ω3_pow,
    _root_.one_zpow]

@[expose] def tA (q : A9) : Fin 2 → Kˣ := ![(q.1 : Kˣ), (q.2 : Kˣ)]

@[expose] def tD (q : A9) : Fin 1 → Kˣ := ![(q.1 : Kˣ) * (q.2 : Kˣ)]

theorem tD_norm (q : A9) (k : Fin 1) : hK.norm (tD q k : K) = 1 := by
  fin_cases k
  have h3 : ((q.1 : Kˣ) * (q.2 : Kˣ)) ^ 3 = 1 := by
    rw [mul_pow, pow_three_of_mem q.1.2, pow_three_of_mem q.2.2, one_mul]
  have h3' : ((((q.1 : Kˣ) * (q.2 : Kˣ) : Kˣ) : K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  simp only [tD, Matrix.cons_val_fin_one]
  rw [norm_eq_pow, show (9 : ℕ) = 3 * 3 from rfl, pow_mul, h3', one_pow]

theorem tRatio (q : A9) : torusRatio hK (tA q) (tD q) = 1 := by
  have h1 : ((q.1 : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_three_of_mem q.1.2, Units.val_one]
  have h2 : ((q.2 : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_three_of_mem q.2.2, Units.val_one]
  have hx0 : ((q.1 : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hy0 : ((q.2 : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one]
  simp only [tA, tD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Units.val_mul, bar_eq_pow]
  have e1 : ((q.1 : Kˣ) : K) ^ 8 = ((q.1 : Kˣ) : K) ^ 2 := by
    rw [show (8 : ℕ) = 3 * 2 + 2 from rfl, pow_add, pow_mul, h1, one_pow, one_mul]
  have e2 : ((q.2 : Kˣ) : K) ^ 8 = ((q.2 : Kˣ) : K) ^ 2 := by
    rw [show (8 : ℕ) = 3 * 2 + 2 from rfl, pow_add, pow_mul, h2, one_pow, one_mul]
  rw [e1, e2]
  field_simp

@[expose] def torusElt (q : A9) : SU5 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (diagonal (torusEntries hK (tA q) (tD q)))
      (by rw [det_diagonal_torusEntries, tRatio]; exact one_ne_zero),
    diagonal_torusEntries_isometry hK (tA q) (tD_norm q),
    by rw [GeneralLinearGroup.val_mkOfDetNeZero, det_diagonal_torusEntries, tRatio]⟩

theorem mat_torusElt (q : A9) : mat (torusElt q) = diagonal (torusEntries hK (tA q) (tD q)) := rfl

@[expose] def e9Hom : A9 →* SU5 where
  toFun := torusElt
  map_one' := mat_injective (by
    rw [mat_torusElt, mat_one]
    ext a b
    rcases a with a | a | a <;> rcases b with b | b | b <;> fin_cases a <;> fin_cases b <;>
      simp [torusEntries, tA, tD])
  map_mul' q q' := mat_injective (by
    rw [mat_mul, mat_torusElt, mat_torusElt, mat_torusElt, diagonal_mul_diagonal]
    congr 1
    funext a
    rcases a with a | a | a <;> fin_cases a <;> simp [torusEntries, tA, tD, mul_comm, mul_left_comm,
      map_mul])

theorem e9Hom_injective : Function.Injective e9Hom := by
  intro q q' h
  have h' := congrArg mat h
  change mat (torusElt q) = mat (torusElt q') at h'
  rw [mat_torusElt, mat_torusElt] at h'
  have h1 := congrFun₂ h' iE1 iE1
  have h2 := congrFun₂ h' iE2 iE2
  simp [torusEntries, tA] at h1 h2
  exact Prod.ext (Subtype.ext (Units.ext h1)) (Subtype.ext (Units.ext h2))

theorem card_A9 : Nat.card A9 = 3 ^ 2 := by
  rw [Nat.card_prod, Nat.card_zpowers, orderOf_ω3]
  norm_num

theorem sq_one_add_single (c : K) :
    (1 + single iE1 iF1 c : Mat5) * (1 + single iE1 iF1 c) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, single_mul_single_of_ne _ _ _ _ (by decide), add_zero, add_assoc]
  have h0 : (single iE1 iF1 c + single iE1 iF1 c : Mat5) = 0 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.zero_apply, ← two_mul, two_eq_zero, zero_mul]
  rw [h0, add_zero]

theorem diagonal_commute {d : HypIndex 2 1 → K} (hd : d iF1 = d iE1) (c : K) :
    diagonal d * (1 + single iE1 iF1 c) = (1 + single iE1 iF1 c) * diagonal d := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hd, mul_comm]
  · simp

theorem one_add_single_eq_blockMat (c : K) :
    (1 + single iE1 iF1 c : Mat5) = blockMat (pairIdx (ε := 1) 0) !![1, c; 0, 1] := by
  ext a b
  rcases a with a | a | a <;> rcases b with b | b | b <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat, embMat, pairIdx, Matrix.mul_apply, Fin.sum_univ_two, one_apply]

theorem trace_one : (1 : K) ∈ hK.traceZero := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, bar_one, ← two_mul, mul_one]
  exact two_eq_zero

@[expose] def iota2 : SpecialLinearGroup (Fin 2) hK.fixedField →* SU5 :=
  iotaU (ε := 1) hK trace_one one_ne_zero 1

theorem iota2_injective : Function.Injective iota2 :=
  iotaU_injective (ε := 1) hK trace_one one_ne_zero 1

theorem isSimpleGroup_SL2 : IsSimpleGroup (SpecialLinearGroup (Fin 2) hK.fixedField) := by
  have := hK.finite
  have : CharP hK.fixedField 2 := (RingHom.charP_iff_charP hK.fixedField.subtype 2).mpr hK.charP
  have := Fintype.ofFinite hK.fixedField
  have h4 : ∃ s : Finset hK.fixedField, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset hK.fixedField).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK.card_fixedField]
      norm_num
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := hK.fixedField) (n := 2) le_rfl (Or.inr h4)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := hK.fixedField)).symm.isSimpleGroup

theorem card_SL2 : Nat.card (SpecialLinearGroup (Fin 2) hK.fixedField) = 504 := by
  have := hK.finite
  rw [LinearFlag.card_SL_eq (by norm_num), hK.card_fixedField]
  decide

theorem isGoodInvolution_of_mat {z : SU5} {c : K} (hc : c ≠ 0)
    (hz : mat z = 1 + single iE1 iF1 c) : IsGoodInvolution z := by
  have hC : ∀ g : SU5, mat g * mat z = mat z * mat g →
      g ∈ Subgroup.centralizer ({z} : Set SU5) := fun g hg => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mat_injective (by rw [mat_mul, mat_mul]; exact hg)
  refine ⟨?_, ?_, iota2.range, ?_, ?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · exact mat_injective (by rw [mat_pow, hz, sq, sq_one_add_single, mat_one])
    · intro h
      have := congrFun₂ (congrArg mat h) iE1 iF1
      rw [hz, mat_one] at this
      simp at this
      exact hc this
  · apply CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
      (fun q => Prod.ext (Subtype.ext (pow_three_of_mem q.1.2))
        (Subtype.ext (pow_three_of_mem q.2.2))) card_A9 e9Hom e9Hom_injective
    rintro _ ⟨q, rfl⟩
    apply hC
    change mat (torusElt q) * mat z = mat z * mat (torusElt q)
    rw [mat_torusElt, hz]
    refine diagonal_commute ?_ c
    have h1 : ((q.1 : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_three_of_mem q.1.2, Units.val_one]
    have hx0 : ((q.1 : Kˣ) : K) ≠ 0 := Units.ne_zero _
    simp only [torusEntries, tA, Matrix.cons_val_zero, bar_eq_pow]
    rw [show (8 : ℕ) = 3 * 2 + 2 from rfl, pow_add, pow_mul, h1, one_pow, one_mul]
    field_simp
    exact h1.symm
  · rintro _ ⟨g, rfl⟩
    apply hC
    rw [hz, one_add_single_eq_blockMat]
    have hio : mat (iota2 g) = blockMat (pairIdx (ε := 1) 1) _ :=
      coe_iotaU (ε := 1) hK trace_one one_ne_zero 1 g
    rw [hio]
    exact (commute_blockMat (by decide) _ _).eq
  · have := isSimpleGroup_SL2
    exact (MonoidHom.ofInjective iota2_injective).symm.isSimpleGroup
  · rw [← Nat.card_congr (MonoidHom.ofInjective iota2_injective).toEquiv, card_SL2]
    norm_num
  · rw [← Nat.card_congr (MonoidHom.ofInjective iota2_injective).toEquiv, card_SL2]
    norm_num

theorem hypScalars_eq_bot : hypScalars hK 2 1 = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (by rw [card_hypScalars hK (by norm_num)]; norm_num)

@[expose] def equivSU : projSU 5 2 3 ≃* SU5 :=
  (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 5 2 3)).symm.trans
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).symm.trans
      ((hypPSUEquivStatedProj hK (exists_isHypTransport (r := 2) (ε := 1) hK).choose_spec
        (by norm_num)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hypScalars_eq_bot).trans QuotientGroup.quotientBot)))

theorem isGoodInvolution_of_sylow (S : Sylow 2 SU5) (z : SU5) (hzS : z ∈ (S : Subgroup SU5))
    (hzC : z ∈ Subgroup.centralizer ((S : Subgroup SU5) : Set SU5)) (hz2 : orderOf z = 2) :
    IsGoodInvolution z := by
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow hK (r := 2) (ε := 1) (by norm_num) (by norm_num)).2.1
  refine forall_good_of_sylow P (fun u huP huC hu2 => ?_) S z hzS hzC hz2
  rw [hP] at huP huC
  obtain ⟨c, hc⟩ := eq_one_add_single_of_mem_center huP (fun v hv =>
    ((Subgroup.mem_centralizer_iff.mp huC) v hv).symm)
  refine isGoodInvolution_of_mat (fun h0 => ?_) hc
  rw [h0, single_zero, add_zero] at hc
  have : u = 1 := mat_injective hc
  rw [this, orderOf_one] at hu2
  omega

theorem two_dvd_card_SU5 : 2 ∣ Nat.card SU5 := by
  have h := (unitary_order_and_Sylow hK (r := 2) (ε := 1) (by norm_num) (by norm_num)).1
  have hdvd : Nat.card U5 ∣ Nat.card SU5 := Subgroup.card_subgroup_dvd_card _
  rw [h] at hdvd
  exact (dvd_pow_self 2 (by norm_num)).trans ((pow_dvd_pow_of_dvd (dvd_pow_self 2 (by norm_num))
    _).trans hdvd)

instance : Finite (projSU 5 2 3) := Finite.of_equiv SU5 equivSU.symm.toEquiv

theorem hasLongRootSet_projSU : HasLongRootSet (projSU 5 2 3) :=
  (hasLongRootSet_of_forall two_dvd_card_SU5 isGoodInvolution_of_sylow).of_mulEquiv equivSU.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.U58
