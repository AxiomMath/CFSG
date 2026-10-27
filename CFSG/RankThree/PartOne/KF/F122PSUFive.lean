module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF.F122Glue
public import CFSG.RankThree.PartOne.S11c.Sec66PSU

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.Sec66T

section Five

variable {f : ℕ} {K : Type} [Field K]

theorem exists_five_decomp (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (h25 : ¬ 25 ∣ 2 ^ f + 1) (d : Kˣ) (hd : h.norm (d : K) = 1) :
    ∃ ε c : Kˣ, h.norm (ε : K) = 1 ∧ h.norm (c : K) = 1 ∧ ε ^ 5 = 1 ∧ d = ε * c ^ 5 := by
  classical
  have hfin : Finite K := h.finite
  have hcard : Nat.card (Units.map h.normHom).ker = 2 ^ f + 1 := (unitary_field_norm h).2.2.1
  obtain ⟨N', hN'⟩ := h5
  have hcop : Nat.Coprime 5 N' := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    rintro ⟨M, hM⟩
    exact h25 ⟨M, by rw [hN', hM]; ring⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * 5 + b * N' = 1 := by
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨a, b, by exact_mod_cast hab⟩
  set d1 : (Units.map h.normHom).ker := ⟨d, (h.mem_ker_normUnits).2 hd⟩ with hd1
  have hord : d1 ^ (Nat.card (Units.map h.normHom).ker : ℤ) = 1 := by
    rw [zpow_natCast]
    exact pow_card_eq_one'
  have hε5 : (d1 ^ (b * N')) ^ 5 = 1 := by
    have h1 : (d1 ^ (b * (N' : ℤ))) ^ 5 = d1 ^ (b * (5 * N' : ℕ)) := by
      rw [← zpow_natCast, ← _root_.zpow_mul]
      congr 1
      push_cast
      ring
    rw [h1, ← hN', ← hcard, Int.mul_comm, _root_.zpow_mul, hord, _root_.one_zpow]
  have hdec : d1 = d1 ^ (b * N') * (d1 ^ a) ^ 5 := by
    have h2 : (d1 ^ a) ^ 5 = d1 ^ (a * 5) := by
      rw [_root_.zpow_mul]
      simp
    calc d1 = d1 ^ (a * 5 + b * N') := by rw [hab, zpow_one]
      _ = d1 ^ (b * N') * (d1 ^ a) ^ 5 := by rw [_root_.zpow_add, h2, mul_comm]
  refine ⟨((d1 ^ (b * N') : (Units.map h.normHom).ker) : Kˣ),
    ((d1 ^ a : (Units.map h.normHom).ker) : Kˣ), ?_, ?_, ?_, ?_⟩
  · exact (h.mem_ker_normUnits).1 (d1 ^ (b * N')).2
  · exact (h.mem_ker_normUnits).1 (d1 ^ a).2
  · have := congrArg Subtype.val hε5
    simpa using this
  · have := congrArg Subtype.val hdec
    simpa using this

theorem diagU_mem_unit5 (h : UnitaryFieldData 2 f K) {v : Fin 5 → Kˣ}
    (hv : ∀ i, h.norm (v i : K) = 1) : (KFU.diagU v : GL (Fin 5) K) ∈ unit5 h := by
  refine mem_primeFormUnitary.mpr ?_
  rw [KFU.diagU_val, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Units.val_one, Matrix.mul_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [mul_comm]
  exact hv i

theorem primeFormConjHom_scalar (h : UnitaryFieldData 2 f K) {c : Kˣ} (hc : h.norm (c : K) = 1) :
    primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
      ⟨Matrix.GeneralLinearGroup.scalar (Fin 5) c, scalar_mem_primeFormUnitary_one h hc⟩ = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show Matrix.GeneralLinearGroup.scalar (Fin 5) c * (g : GL (Fin 5) K) *
    (Matrix.GeneralLinearGroup.scalar (Fin 5) c)⁻¹ = (g : GL (Fin 5) K)
  rw [← (commute_scalar c (g : GL (Fin 5) K)).eq, mul_inv_cancel_right]

theorem psu5_exists_violation (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (h25 : ¬ 25 ∣ 2 ^ f + 1) {α : MulAut (psu5 h)} (hα5 : α ^ 5 = 1)
    (hαinn : α ∉ innerAut (psu5 h)) :
    ∃ (i : MulAut (psu5 h)) (j : ℕ), i ∈ innerAut (psu5 h) ∧
      ¬ LocalRankAut 5 (psu5 h) (i * α ^ j) := by
  classical
  have hfin : Finite K := h.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases hαD : α ∈ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  ·
    obtain ⟨P, rfl⟩ := hαD
    set d : Kˣ := Matrix.GeneralLinearGroup.det (P : GL (Fin 5) K) with hd
    have hdn : h.norm (d : K) = 1 := by
      have := norm_det_eq_one h (1 : GL (Fin 5) K) P.2
      simpa [hd] using this
    obtain ⟨ε, c, hεn, hcn, hε5, hdεc⟩ := exists_five_decomp h h5 h25 d hdn
    set v : Fin 5 → Kˣ := Pi.mulSingle (0 : Fin 5) ε with hv
    have hvn : ∀ i, h.norm (v i : K) = 1 := by
      intro i
      by_cases hi : i = 0
      · subst hi
        simpa [hv] using hεn
      · simp [hv, Pi.mulSingle_eq_of_ne hi, UnitaryFieldData.norm]
    have hQ : (KFU.diagU v : GL (Fin 5) K) ∈ unit5 h := diagU_mem_unit5 h hvn
    set Q : unit5 h := ⟨KFU.diagU v, hQ⟩ with hQdef
    have hcs : Matrix.GeneralLinearGroup.scalar (Fin 5) c ∈ unit5 h :=
      scalar_mem_primeFormUnitary_one h hcn
    set S : unit5 h := ⟨Matrix.GeneralLinearGroup.scalar (Fin 5) c, hcs⟩ with hSdef
    have hS1 : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) S = 1 :=
      primeFormConjHom_scalar h hcn
    set s : unit5 h := S * Q * P⁻¹ with hs
    have hsdet : ((s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (s : GL (Fin 5) K) = 1 := by
        have hdetQ : Matrix.GeneralLinearGroup.det (KFU.diagU v : GL (Fin 5) K) = ε := by
          apply Units.ext
          rw [Matrix.GeneralLinearGroup.val_det_apply, KFU.det_diagU, ← Units.coe_prod, hv,
            Finset.prod_pi_mulSingle']
          simp
        simp only [hs, hSdef, hQdef, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
          Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hdetQ, ← hd]
        rw [hdεc, mul_comm ε (c ^ 5)]
        rw [mul_comm (c ^ 5) ε] 
        exact mul_inv_cancel _
      have h2 := congrArg (fun u : Kˣ => (u : K)) h1
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
    have hsΓ : (s : GL (Fin 5) K) ∈ gamma5 h := (mem_gramSU_iff_unitary h).mpr ⟨s.2, hsdet⟩
    set i : MulAut (psu5 h) := primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) s
      with hi
    have hiinn : i ∈ innerAut (psu5 h) :=
      (mem_inner_primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i).2
        ⟨⟨s, hsΓ⟩, rfl⟩
    have hβ : i * primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P =
        primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) Q := by
      rw [hi, ← map_mul]
      have : s * P = S * Q := by
        rw [hs]
        group
      rw [this, map_mul, hS1, one_mul]
    set ψ : MulAut (psu5 h) := primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) Q
      with hψ
    refine ⟨i, 1, hiinn, ?_⟩
    rw [pow_one, hβ]
    have hψ5 : ψ ^ 5 = 1 := by
      rw [hψ, ← map_pow]
      have : Q ^ 5 = 1 := by
        apply Subtype.ext
        change (KFU.diagU v : GL (Fin 5) K) ^ 5 = 1
        rw [KFU.diagU_pow, hv, ← Pi.mulSingle_pow, hε5, Pi.mulSingle_one, KFU.diagU_one]
      rw [this, map_one]
    have hψinn : ψ ∉ innerAut (psu5 h) := by
      intro hmem
      apply hαinn
      have : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P = i⁻¹ * ψ :=
        eq_inv_mul_of_mul_eq hβ
      rw [this]
      exact mul_mem (inv_mem hiinn) hmem
    have hdiagQ : ((KFU.diagU v : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag :=
      KFU.isDiag_diagU v
    have h12 : ((KFU.diagU v : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 1 1 =
        ((KFU.diagU v : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 2 2 := by
      rw [KFU.diagU_apply_same, KFU.diagU_apply_same, hv, Pi.mulSingle_eq_of_ne (by decide),
        Pi.mulSingle_eq_of_ne (by decide)]
    refine not_localRankAut_of_frame h h5 (1 : unit5 h) (i := 1) (j := 2) (by decide) ψ hψ5
      hψinn ?_ ?_
    · intro a ha
      obtain ⟨t, ht, hat⟩ := exists_of_mem_frameA ha
      show primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) Q
        ((a : gamma5 h) : psu5 h) = ((a : gamma5 h) : psu5 h)
      rw [primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      show (KFU.diagU v : GL (Fin 5) K) * (a : GL (Fin 5) K) * (KFU.diagU v : GL (Fin 5) K)⁻¹ =
        (a : GL (Fin 5) K)
      rw [hat]
      have hc := isDiag_comm hdiagQ (isDiag_of_mem_torusEq ht)
      simp only [Subgroup.coe_one, one_mul, inv_one, mul_one]
      rw [hc]
      group
    · show primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) Q
        ((frameR h (1 : unit5 h) 1 2 : gamma5 h) : psu5 h) =
          ((frameR h (1 : unit5 h) 1 2 : gamma5 h) : psu5 h)
      rw [primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      show (KFU.diagU v : GL (Fin 5) K) * ((frameR h (1 : unit5 h) 1 2 : gamma5 h) : GL (Fin 5) K) *
        (KFU.diagU v : GL (Fin 5) K)⁻¹ = ((frameR h (1 : unit5 h) 1 2 : gamma5 h) : GL (Fin 5) K)
      rw [coe_frameR]
      have hc := KFSU5.swapUnit_mul_comm (K := K) (i := (1 : Fin 5)) (j := 2)
        (KFU.diagU v : GL (Fin 5) K) hdiagQ h12
      simp only [Subgroup.coe_one, one_mul, inv_one, mul_one]
      rw [← hc]
      group
  ·
    refine ⟨1, 1, Subgroup.one_mem _, fun hra => ?_⟩
    rw [one_mul, pow_one] at hra
    have hα1 : α ≠ 1 := fun h1 => hαinn (h1 ▸ Subgroup.one_mem _)
    exact psu5_F_case h h5 (orderOf_eq_prime hα5 hα1) hαD hra

end Five

theorem kf122RowW12_holds : KF122RowW 12 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn
  obtain ⟨rfl, -, f, -, h5, h25, hC⟩ := hmodel
  obtain ⟨K, _, _, hU, -, -, ⟨e⟩⟩ := psu_prime_form_model hC
  have hα'p : MulAut.congr e α ^ 5 = 1 := by rw [← map_pow, hαp, map_one]
  have hα'inn : MulAut.congr e α ∉ innerAut (psu5 hU) := fun hmem =>
    hαinn ((mem_innerAut_congr e α).mp hmem)
  obtain ⟨i', j, hi', hviol⟩ := psu5_exists_violation hU h5 h25 hα'p hα'inn
  refine ⟨(MulAut.congr e).symm i', j, ?_, fun hra => hviol ?_⟩
  · rw [← mem_innerAut_congr e, MulEquiv.apply_symm_apply]
    exact hi'
  · have h1 := localRankAut_congr e hp hra
    have h2 : MulAut.congr e ((MulAut.congr e).symm i' * α ^ j) = i' * MulAut.congr e α ^ j := by
      rw [map_mul, map_pow, MulEquiv.apply_symm_apply]
    rwa [h2] at h1

end CFSG.RankThree.PartOne
