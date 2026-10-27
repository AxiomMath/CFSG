module

public import CFSG.RankThree.PartOne.HNB.F25
public import CFSG.Quasithin.Vol2.KGFact12614U35a
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofLA7
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res3U35

open CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Quasithin.H13 Matrix
open CFSG.Assembly.RankThreeEven (projSU)

theorem hF : UnitaryFieldData 5 1 F25 := ⟨Nat.prime_five, le_rfl, by rw [F25.card]; norm_num⟩

abbrev SU5 : Subgroup (GL (Fin 3) F25) := unitarySU 5 1 F25 3

abbrev PU5 : Type := unitaryPSU hF 3

@[expose] def fe (a b : ZMod 5) : F25 := (a, b)

noncomputable def gfEquiv [Fact (Nat.Prime 5)] : GaloisField 5 (2 * 1) ≃+* F25 :=
  letI := Fintype.ofFinite (GaloisField 5 (2 * 1))
  FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card 5 (2 * 1) (by norm_num), F25.card]
    norm_num)

noncomputable def equivPU [Fact (Nat.Prime 5)] : ↥(projSU 3 5 1) ≃* PU5 :=
  (Sec4.projSUEquivStatedProj 3 5 1).trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) gfEquiv)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU gfEquiv 3 (5 ^ 1))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars gfEquiv)).trans
      (unitaryPSUEquiv hF (n := 3) (by norm_num)).symm)

theorem card_PU5 : Nat.card PU5 = 126000 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [← Nat.card_congr (equivPU).toEquiv]
  exact Sec15.Proof1515.card_projSU_three_five

instance : Finite PU5 := Nat.finite_of_card_ne_zero (by rw [card_PU5]; norm_num)

@[expose] noncomputable def mkSU (M : Matrix (Fin 3) (Fin 3) F25) (hdet : M.det = 1)
    (hu : (M.map (· ^ (5 ^ 1)))ᵀ * M = 1) : SU5 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    Subgroup.subset_closure ⟨by simpa using hdet, by simpa using hu⟩⟩

theorem coe_mkSU (M : Matrix (Fin 3) (Fin 3) F25) (hdet : M.det = 1)
    (hu : (M.map (· ^ (5 ^ 1)))ᵀ * M = 1) :
    (((mkSU M hdet hu : SU5) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = M :=
  rfl

theorem SU5_ext {g k : SU5}
    (h : ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      ((k : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25)) : g = k :=
  Subtype.ext (Units.ext h)

@[expose] def det3 (M : Matrix (Fin 3) (Fin 3) F25) : F25 :=
  M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 +
    M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0

theorem det_eq_det3 (M : Matrix (Fin 3) (Fin 3) F25) : M.det = det3 M :=
  Matrix.det_fin_three M

theorem coe_mul (g k : SU5) :
    (((g * k : SU5) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) *
        ((k : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) :=
  rfl

theorem coe_pow (g : SU5) (n : ℕ) :
    (((g ^ n : SU5) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem bar_eq (c : F25) : hF.bar c = c ^ 5 := by
  rw [hF.bar_apply, pow_one]

theorem mk_eq_mk_of_smul {g k : SU5} {c : F25}
    (h : ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      c • ((k : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25)) : (g : PU5) = (k : PU5) := by
  have hg := (mem_unitarySU_iff hF).1 g.2
  have hk := (mem_unitarySU_iff hF).1 k.2
  have hc3 : c ^ 3 = 1 := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_smul, hg.1, hk.1, Fintype.card_fin, mul_one] at h1
    exact h1.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc3
  rw [QuotientGroup.eq, mem_unitaryScalars]
  refine ⟨(Units.mk0 c hc0)⁻¹, ?_, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, bar_eq, Units.val_inv_eq_inv_val, Units.val_mk0, ← pow_succ',
      inv_pow, show 5 + 1 = 3 * 2 from rfl, pow_mul, hc3, one_pow, inv_one]
  · rw [inv_pow]
    have : (Units.mk0 c hc0) ^ 3 = 1 := Units.ext (by simpa using hc3)
    rw [this, inv_one]
  · apply Units.ext
    have hk' : ((k : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
        c⁻¹ • ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) := by
      rw [h, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hgi : (((g⁻¹ : SU5) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) *
        ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = 1 := by
      rw [← coe_mul, inv_mul_cancel]
      rfl
    change (((g⁻¹ : SU5) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) *
      ((k : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = _
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_inv_eq_inv_val,
      Units.val_mk0, hk', Matrix.mul_smul, hgi, Matrix.smul_one_eq_diagonal]

theorem mk_ne_one_of {g : SU5}
    (h : ∀ c : F25, ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) ≠ c • 1) :
    (g : PU5) ≠ 1 := by
  intro h1
  rw [QuotientGroup.eq_one_iff, mem_unitaryScalars] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  apply h c
  rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

@[expose] def om : F25 := fe 2 3

theorem om_pow_three : om ^ 3 = 1 := by decide +kernel

theorem om_ne_one : om ≠ 1 := by decide +kernel

noncomputable abbrev g1 : SU5 := U35A6.g₁ hF om_pow_three

noncomputable abbrev g2 : SU5 := U35A6.g₂ hF

theorem coe_g1 : ((g1 : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = U35A6.dMat om := rfl

theorem coe_g2 : ((g2 : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = U35A6.cMat := rfl

noncomputable abbrev x1 : PU5 := (g1 : PU5)

noncomputable abbrev x2 : PU5 := (g2 : PU5)

theorem x1_mul_x2 : x1 * x2 = x2 * x1 := U35A6.x_comm hF om_pow_three

theorem x1_pow_three : x1 ^ 3 = 1 := U35A6.x1_pow hF om_pow_three

theorem x2_pow_three : x2 ^ 3 = 1 := U35A6.x2_pow hF

noncomputable abbrev E0 : Subgroup PU5 := Subgroup.zpowers x1 ⊔ Subgroup.zpowers x2

theorem dMat_pow_mul_cMat_pow_ne : ∀ i j : Fin 3, (i, j) ≠ (0, 0) → ∀ c : F25,
    U35A6.dMat om ^ (i : ℕ) * U35A6.cMat ^ (j : ℕ) ≠ c • 1 := by
  decide +kernel

theorem x1_pow_mul_x2_pow_ne_one (i j : Fin 3) (hij : (i, j) ≠ (0, 0)) :
    x1 ^ (i : ℕ) * x2 ^ (j : ℕ) ≠ 1 := by
  have e : x1 ^ (i : ℕ) * x2 ^ (j : ℕ) = ((g1 ^ (i : ℕ) * g2 ^ (j : ℕ) : SU5) : PU5) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
  rw [e]
  refine mk_ne_one_of fun c => ?_
  rw [coe_mul, coe_pow, coe_pow, coe_g1, coe_g2]
  exact dMat_pow_mul_cMat_pow_ne i j hij c

theorem exists_fin_zpow_eq {G : Type*} [Group G] {x : G} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1)
    (i : ℤ) : ∃ k : Fin n, x ^ i = x ^ (k : ℕ) := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 := Int.emod_nonneg i hn'
  have h1 := Int.emod_lt_of_pos i (by exact_mod_cast hn : (0 : ℤ) < n)
  refine ⟨⟨(i % (n : ℤ)).toNat, by omega⟩, ?_⟩
  rw [zpow_eq_zpow_emod' i hx, ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem exists_eq_of_mem_E0 {e : PU5} (he : e ∈ E0) :
    ∃ i j : Fin 3, e = x1 ^ (i : ℕ) * x2 ^ (j : ℕ) := by
  obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup x1_mul_x2 he
  obtain ⟨a, ha⟩ := exists_fin_zpow_eq (by norm_num) x1_pow_three i
  obtain ⟨b, hb⟩ := exists_fin_zpow_eq (by norm_num) x2_pow_three j
  exact ⟨a, b, by rw [ha, hb]⟩

theorem mem_E0 (i j : ℕ) : x1 ^ i * x2 ^ j ∈ E0 :=
  E0.mul_mem (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers x1 i))
    (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers x2 j))

theorem exists_smul_of_mk_eq {g k : SU5} (h : (g : PU5) = (k : PU5)) :
    ∃ c : F25, ((k : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      c • ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) := by
  rw [QuotientGroup.eq, mem_unitaryScalars] at h
  obtain ⟨c, -, -, hc⟩ := h
  refine ⟨(c : F25), ?_⟩
  have hk : (k : GL (Fin 3) F25) = (g : GL (Fin 3) F25) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hk, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem cMat_ne_smul_dMat_pow : ∀ k : Fin 3, ∀ c : F25,
    U35A6.cMat ≠ c • U35A6.dMat om ^ (k : ℕ) := by
  decide +kernel

theorem x1_ne_one : x1 ≠ 1 := by
  have := x1_pow_mul_x2_pow_ne_one 1 0 (by decide)
  simpa using this

theorem orderOf_x1 : orderOf x1 = 3 :=
  orderOf_eq_prime x1_pow_three x1_ne_one

theorem x2_not_mem_zpowers_x1 : x2 ∉ Subgroup.zpowers x1 := by
  intro h
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  obtain ⟨k, hk⟩ := exists_fin_zpow_eq (by norm_num) x1_pow_three i
  have e : ((g1 ^ (k : ℕ) : SU5) : PU5) = (g2 : PU5) := by
    rw [QuotientGroup.mk_pow, ← hk, hi]
  obtain ⟨c, hc⟩ := exists_smul_of_mk_eq e
  rw [coe_pow, coe_g1, coe_g2] at hc
  exact cMat_ne_smul_dMat_pow k c hc

theorem pow_three_of_mem_E0 {e : PU5} (he : e ∈ E0) : e ^ 3 = 1 := by
  obtain ⟨i, j, rfl⟩ := exists_eq_of_mem_E0 he
  rw [(Commute.pow_pow x1_mul_x2 _ _).mul_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ), pow_mul,
    x1_pow_three, one_pow, one_mul, mul_comm (j : ℕ), pow_mul, x2_pow_three, one_pow]

theorem card_E0 : Nat.card E0 = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E0 := fun e => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_three_of_mem_E0 e.2, Subgroup.coe_one])⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hle : Nat.card E0 ≤ 9 := by
    have hsurj : Function.Surjective (fun q : Fin 3 × Fin 3 =>
        (⟨x1 ^ (q.1 : ℕ) * x2 ^ (q.2 : ℕ), mem_E0 _ _⟩ : E0)) := by
      rintro ⟨e, he⟩
      obtain ⟨i, j, rfl⟩ := exists_eq_of_mem_E0 he
      exact ⟨(i, j), rfl⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, Nat.card_fin] at h1
  have hlt : 3 < Nat.card E0 := by
    have h1 : Subgroup.zpowers x1 < E0 := lt_of_le_of_ne le_sup_left fun heq =>
      x2_not_mem_zpowers_x1 (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x2))
    have h2 := Subgroup.card_lt_of_lt h1
    rwa [Nat.card_zpowers, orderOf_x1] at h2
  rw [hn] at hle hlt ⊢
  have hn3 : n < 3 := by
    by_contra hge
    have : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> omega

theorem not_three_dvd_index_of_card_nine {E : Subgroup PU5} (hE : Nat.card E = 9) :
    ¬ 3 ∣ E.index := by
  have h := E.index_mul_card
  rw [hE, card_PU5] at h
  omega

theorem exists_conj_eq_E0 {E : Subgroup PU5} (hE : Nat.card E = 9) :
    ∃ g : PU5, ∀ x : PU5, x ∈ E ↔ g * x * g⁻¹ ∈ E0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  have hE0p : IsPGroup 3 E0 := IsPGroup.of_card (n := 2) (by rw [card_E0]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PU5
    (hEp.toSylow (not_three_dvd_index_of_card_nine hE))
    (hE0p.toSylow (not_three_dvd_index_of_card_nine card_E0))
  refine ⟨g, fun x => ?_⟩
  have h1 : g * x * g⁻¹ ∈ ((g • hEp.toSylow (not_three_dvd_index_of_card_nine hE) :
      Sylow 3 PU5) : Subgroup PU5) ↔ x ∈ E := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
      group
    rw [this, IsPGroup.toSylow_coe]
  rw [← h1, hg, IsPGroup.toSylow_coe]

theorem exists_conj_E0_le {K : Subgroup PU5} (hK : 9 ∣ Nat.card K) :
    ∃ g : PU5, ∀ x ∈ E0, g⁻¹ * x * g ∈ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) (G := K)
    (by norm_num; exact hK)
  set P := P'.map K.subtype with hP
  have hPc : Nat.card P = 9 := by
    rw [hP, Subgroup.card_map_of_injective K.subtype_injective, hP']
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_eq_E0 hPc
  refine ⟨g, fun x hx => ?_⟩
  have h1 : g⁻¹ * x * g ∈ P := by
    rw [hg]
    convert hx using 1
    group
  obtain ⟨y, -, hy⟩ := h1
  rw [← hy]
  exact y.2

end CFSG.RankThree.PartTwo.Sec16.Res3U35
