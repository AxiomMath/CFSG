module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompU3C
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompA

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K)

theorem eq_one_of_pow_char {d : K} [hp : Fact p.Prime] [CharP K p] (hd : d ^ p = 1) : d = 1 := by
  have : (d - 1) ^ p = 0 := by rw [sub_pow_char, hd, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff hp.out.ne_zero |>.mp this)

theorem mem_hypSU_of_pow {u u' : Matrix (HypIndex 1 1) (HypIndex 1 1) K} (huu : u * u' = 1)
    (hu'u : u' * u = 1) (hu : (u.map h.bar)ᵀ * hypGram 1 1 K * u = hypGram 1 1 K)
    (hup : u ^ p = 1) : (⟨u, u', huu, hu'u⟩ : GL (HypIndex 1 1) K) ∈ hypSU h 1 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  refine ⟨hu, eq_one_of_pow_char ?_⟩
  change u.det ^ p = 1
  rw [← det_pow, hup, det_one]

theorem orderOf_hypProj_of_pow {g : hypSU h 1 1}
    (hgp : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) ^ p = 1)
    (hsc : ∀ c : K, ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) ≠ c • 1) :
    orderOf g = p ∧ orderOf (hypProj h 1 1 g) = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp1 : g ^ p = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hgp]
    rfl))
  refine ⟨orderOf_eq_prime hp1 fun h1 => hsc 1 (by rw [h1, one_smul]; rfl),
    orderOf_eq_prime (by rw [← map_pow, hp1, map_one]) fun h1 => ?_⟩
  rw [← MonoidHom.mem_ker, ker_hypProj] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  apply hsc c
  rw [hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]

theorem exists_psu3_inv_of_involution (hp2 : p ≠ 2) {ν : MulAut (hypPSU h 1 1)}
    (hν : orderOf ν = 2) :
    ∃ g : hypSU h 1 1, orderOf g = p ∧ orderOf (hypProj h 1 1 g) = p ∧
      ν (hypProj h 1 1 g) = hypProj h 1 1 g⁻¹ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨happly, -, -, hinv⟩ := odd_unitary_automorphism_semilinear_representation h hp2
    (r := 1) (ε := 1) le_rfl le_rfl (by norm_num)
  obtain ⟨A, σ, hx, hA, hαx, hσ, hinner, hfield⟩ := hinv ν hν
  have hνg : ∀ g : hypSU h 1 1, ν (hypProj h 1 1 g) =
      hypProj h 1 1 ⟨_, conj_mem_hypSU hx g⟩ := fun g => by
    rw [← hαx]
    exact happly ⟨_, hx⟩ g
  have hAm : ((A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K * A =
      hypGram 1 1 K := hA
  have hAA : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * ((A⁻¹ : GL _ K) : Matrix _ _ K) = 1 :=
    by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rcases hσ with rfl | hσb
  ·
    have hord := hinner rfl
    have hsq : (⟨A, hA⟩ : hypUnitary h 1 1) ^ 2 ∈ normOneScalars h (hypUnitary h 1 1) 0 := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hord, pow_orderOf_eq_one]
    have hns : (⟨A, hA⟩ : hypUnitary h 1 1) ∉ normOneScalars h (hypUnitary h 1 1) 0 := by
      intro hmem
      have : (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 1 1) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      rw [this, orderOf_one] at hord
      omega
    obtain ⟨c, hcN, -, hc⟩ := hsq
    have hc' : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * A = (c : K) • 1 := by
      have h1 := congrArg (fun g : GL (HypIndex 1 1) K =>
        (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hc
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
        scalar_apply, ← smul_one_eq_diagonal] at h1
      rwa [pow_two] at h1
    have hdb : ((A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar).det =
        h.bar (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det := by rw [RingHom.map_det]; rfl
    have hNd : h.bar (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det *
        (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det = 1 := by
      have h1 := congrArg Matrix.det hAm
      rw [det_mul, det_mul, det_transpose, hdb] at h1
      have hJ : (hypGram 1 1 K).det ≠ 0 := det_hypGram_ne_zero
      have : (h.bar (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det *
          (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det - 1) * (hypGram 1 1 K).det = 0 := by
        linear_combination h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hJ)
    set d : K := (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det with hd
    have hd0 : d ≠ 0 := fun h0 => by rw [h0, mul_zero] at hNd; exact zero_ne_one hNd
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    have hdc : d * d = (c : K) ^ 3 := by
      have h1 := congrArg Matrix.det hc'
      rw [det_mul, det_smul, det_one, mul_one, card_hypIndex] at h1
      exact h1
    set lam : K := d / c with hlam
    have hlam0 : lam ≠ 0 := div_ne_zero hd0 hc0
    have hlam2 : lam * lam = c := by
      rw [hlam, div_mul_div_comm, hdc]
      field_simp
    have hNc : h.bar (c : K) * c = 1 := by
      have := hcN
      rw [UnitaryFieldData.norm] at this
      rw [mul_comm]
      exact this
    have hNlam : h.bar lam * lam = 1 := by
      rw [hlam, map_div₀, div_mul_div_comm, hNd, hNc, div_one]
    set Tm : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
      lam⁻¹ • (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hTm
    set Tm' : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
      lam • ((A⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hTm'
    have hTT : Tm * Tm' = 1 := by
      rw [hTm, hTm', smul_mul_smul_comm, hAA, inv_mul_cancel₀ hlam0, one_smul]
    have hT2 : Tm * Tm = 1 := by
      rw [hTm, smul_mul_smul_comm, hc', smul_smul, ← mul_inv, hlam2, inv_mul_cancel₀ hc0, one_smul]
    have hTdet : Tm.det = 1 := by
      rw [hTm, det_smul, card_hypIndex, ← hd, hlam, inv_div, show 2 * 1 + 1 = 3 from rfl, div_pow,
        div_mul_eq_mul_div, div_eq_one_iff_eq (pow_ne_zero 3 hd0)]
      linear_combination (-d) * hdc
    have hTu : (Tm.map h.bar)ᵀ * hypGram 1 1 K * Tm = hypGram 1 1 K := by
      rw [hTm, map_smul_bar, transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        smul_smul, hAm, map_inv₀, ← mul_inv, hNlam, inv_one, one_smul]
    have hT1 : Tm ≠ 1 := by
      intro h1
      apply hns
      have hAl : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = lam • 1 := by
        calc (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = lam • Tm := by
              rw [hTm, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
          _ = lam • 1 := by rw [h1]
      refine ⟨Units.mk0 lam hlam0, ?_, by rw [pow_zero], ?_⟩
      · rw [UnitaryFieldData.norm, Units.val_mk0, mul_comm]
        exact hNlam
      · apply Units.ext
        rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0,
          ← smul_one_eq_diagonal]
        exact hAl
    obtain ⟨u, u', huu, hu'u, huni, hup, hsc, hconj⟩ := exists_eichler h hp2 hTu hTT hT2 hTdet hT1
    have hU := mem_hypSU_of_pow h huu hu'u huni hup
    set g : hypSU h 1 1 := ⟨_, hU⟩ with hg
    obtain ⟨ho, hop⟩ := orderOf_hypProj_of_pow h (g := g) hup hsc
    refine ⟨g, ho, hop, ?_⟩
    rw [hνg]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      ((glAut (RingEquiv.refl K) (g : GL (HypIndex 1 1) K) : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      ((A⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u'
    rw [coe_glAut]
    have hmap : (u : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map (RingEquiv.refl K) = u := by
      ext i j
      rfl
    rw [show ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u from rfl,
      hmap, ← hconj, hTm, hTm', smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ hlam0, one_smul]
  ·
    obtain ⟨c, -, hAc⟩ := hfield hσb
    obtain ⟨u, u', huu, hu'u, huni, hup, hsc, hconj⟩ := exists_transv h hp2 hAm hAA hAc
    have hU := mem_hypSU_of_pow h huu hu'u huni hup
    set g : hypSU h 1 1 := ⟨_, hU⟩ with hg
    obtain ⟨ho, hop⟩ := orderOf_hypProj_of_pow h (g := g) hup hsc
    refine ⟨g, ho, hop, ?_⟩
    rw [hνg]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change (A : Matrix _ _ K) * ((glAut σ (g : GL (HypIndex 1 1) K) : GL _ K) : Matrix _ _ K) *
      ((A⁻¹ : GL _ K) : Matrix _ _ K) = u'
    rw [coe_glAut]
    have hmap : (u : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map σ = u.map h.bar := by
      ext i j
      simp [hσb]
    rw [show ((g : GL (HypIndex 1 1) K) : Matrix _ _ K) = u from rfl, hmap, hconj]

theorem eq_three_or_five_of_autConf_psu3 (hp2 : p ≠ 2) {ν : MulAut (hypPSU h 1 1)}
    {Lb Pb : Subgroup (MulAut (hypPSU h 1 1))} (hc : AutConf (hypPSU h 1 1) ν Lb Pb) :
    p = 3 ∨ p = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, hgo, hνg⟩ := exists_psu3_inv_of_involution h hp2 (orderOf_eq_prime hc.sq hc.ne_one)
  rw [map_inv] at hνg
  rcases hc.inv _ (by rw [hgo]; exact h.prime.odd_of_ne_two hp2) hνg with h3 | h5
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [hgo] at this
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp this)
  · have := orderOf_dvd_of_pow_eq_one h5
    rw [hgo] at this
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).mp this)

variable {Q : Type} [Group Q] {K' L P T : Subgroup Q} {v : Q}

theorem Conf12626.eq_three_or_five_of_psu3 (hQ : CFSG.QuasithinUnique.Vol2Native.SQTKHypCat Q)
    (hconf : Conf12626 K' L P T v) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hU3 : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K' .PSU 3 q 1) : q = 3 ∨ q = 5 := by
  have := hQ.finite
  obtain ⟨-, F, _, _, hFc, ⟨e⟩⟩ := hU3
  have hUF : UnitaryFieldData q 1 F := ⟨hq, le_rfl, by rw [hFc, pow_one]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hUF
  exact eq_three_or_five_of_autConf_psu3 hUF hq2
    (hconf.autConf.map (e.trans (hypPSUEquivStatedProj hUF hR (by norm_num)).symm))

end CFSG.Quasithin.H13.S126C
