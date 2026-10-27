module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem ks1520HessCent : KS1520HessCent := Sec16.kS169HessCent

namespace KSL3Two

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.Sec16.ProofHess

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem lifts_not_commute (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) {y₁ y₂ : GL (Fin 3) K}
    (hy₁S : y₁ ∈ slPi π 3 (p ^ f) K) (hy₂S : y₂ ∈ slPi π 3 (p ^ f) K)
    (he₁E : ProjGenLinGroup.mk y₁ ∈ E) (he₁1 : ProjGenLinGroup.mk y₁ ≠ 1)
    (he₂E : ProjGenLinGroup.mk y₂ ∈ E)
    (he₂ : ProjGenLinGroup.mk y₂ ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₁)) :
    y₁ * y₂ ≠ y₂ * y₁ := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hy₁3 : y₁ ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy₁S (hE.2 _ he₁E)
  have hdet₁ : (y₁ : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hy₁S).2
  have hdet₂ : (y₂ : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hy₂S).2
  have hy₁s : ∀ c : K, (y₁ : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply he₁1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, det_zero] at hdet₁
      exact zero_ne_one hdet₁
    exact mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_eq_smul hc hc0)
  have hy₁3m : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy₁3, Units.val_one]
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hy₁3m hdet₁ hy₁s
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, τ ^ 2, 1] with hD
  set Y : Matrix (Fin 3) (Fin 3) K := τ ^ (j : ℕ) • (y₁ : Matrix (Fin 3) (Fin 3) K) with hY
  set Q := P⁻¹ with hQ
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hYc : ∀ M : Matrix (Fin 3) (Fin 3) K,
      M * (y₁ : Matrix (Fin 3) (Fin 3) K) = (y₁ : Matrix (Fin 3) (Fin 3) K) * M →
        M * Y = Y * M := by
    intro M hM
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, hM]
  have hYPD : Y = P * D * Q := by
    calc Y = Y * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (Y * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * D * Q := by rw [hPD]
  set N := Q * (y₂ : Matrix (Fin 3) (Fin 3) K) * P with hN
  have hNdet : N.det = 1 := by rw [hN, det_conj hQP, hdet₂]
  intro hcomm
  have hcomm' : (y₂ : Matrix (Fin 3) (Fin 3) K) * y₁ = y₁ * y₂ := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hcomm
    simp only [Units.val_mul] at h
    exact h.symm
  have hND : N * D = D * N := conj_commute hPQ hQP hPD (hYc _ hcomm')
  have hNdiag := eq_diagonal_of_commute hτ hτ1 hND
  have hy₂3 : y₂ ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy₂S (hE.2 _ he₂E)
  have hN3 : N ^ 3 = 1 := by
    rw [hN, conj_pow hPQ hQP, ← Units.val_pow_eq_pow_val, hy₂3, Units.val_one,
      Matrix.mul_one, hQP]
  have hcub : ∀ i, (N i i) ^ 3 = 1 := by
    intro i
    have h := congrFun (congrFun hN3 i) i
    rw [hNdiag, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h
    simpa using h
  have habc : N 0 0 * N 1 1 * N 2 2 = 1 := by
    have h := hNdet
    rw [hNdiag, det_diagonal, Fin.prod_univ_three] at h
    exact h
  obtain ⟨i, hi⟩ := exists_eq_smul_pow_of_diag hτ hτ1 (hcub 0) (hcub 1) habc
  obtain ⟨c, hc⟩ : ∃ c : K, c = N 2 2 := ⟨_, rfl⟩
  have hNeq : N = c • D ^ i := by
    rw [hc, ← hi, hNdiag]
    congr 1
    funext l
    fin_cases l <;> rfl
  have hy₂eq : (y₂ : Matrix (Fin 3) (Fin 3) K) =
      (c * (τ ^ (j : ℕ)) ^ i) • (y₁ : Matrix (Fin 3) (Fin 3) K) ^ i := by
    have h1 : (y₂ : Matrix (Fin 3) (Fin 3) K) = P * N * Q := by rw [hN, unconj hPQ]
    have h2 : P * D ^ i * Q = Y ^ i := by
      rw [hYPD, conj_pow hQP hPQ D i]
    rw [h1, hNeq, Matrix.mul_smul, Matrix.smul_mul, h2, hY, smul_pow, smul_smul]
  apply he₂
  have hc0 : c * (τ ^ (j : ℕ)) ^ i ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hy₂eq
    rw [hy₂eq, det_zero] at hdet₂
    exact zero_ne_one hdet₂
  have hsc : y₂ * (y₁ ^ i)⁻¹ ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_eq_smul (a := c * (τ ^ (j : ℕ)) ^ i) ?_ hc0
    have hinv : ((y₁ ^ i : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((y₁ ^ i)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, hy₂eq, Matrix.smul_mul, ← Units.val_pow_eq_pow_val, hinv]
  have hmk := mk_eq_one_iff_mem_statedScalars.mpr hsc
  rw [map_mul, map_inv, mul_inv_eq_one] at hmk
  rw [hmk, map_pow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i

theorem type_one_of_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y₁ y₂ : GL (Fin 3) K} (hy₁S : y₁ ∈ slPi π 3 (p ^ f) K) (hy₁3 : y₁ ^ 3 = 1)
    (hy₁1 : ProjGenLinGroup.mk y₁ ≠ 1) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    Type123 π (p ^ f) K y₁ 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hyH : y₁ ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hy₁S
  have hyZ : y₁ ∉ zPi π 3 (p ^ f) K := by
    intro hz
    exact hy₁1 (mk_eq_one_iff_mem_statedScalars.mpr
      (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz))
  have hy3 : y₁ ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [hy₁3]
    exact one_mem _
  rcases type123_exhaust hK hq hyH hyZ hy3 with h | h | h
  · exact h
  · exfalso
    apply trace_ne_zero_of_type2 hK hq h
    have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
        A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
      fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
    have hconj : y₂ * y₁ * y₂⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * y₁ := by
      have h1 : y₁ * y₂ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂ * y₁ := by
        rw [← hζ]
        group
      calc y₂ * y₁ * y₂⁻¹
          = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ *
              (GeneralLinearGroup.scalar (Fin 3) ζ * y₂ * y₁) * y₂⁻¹ := by
            rw [map_inv]
            group
        _ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (y₁ * y₂) * y₂⁻¹ := by rw [h1]
        _ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * y₁ := by group
    exact trace_eq_zero_of_conj_eq_scalar_mul (inv_ne_one.mpr hζ1) hconj
  · exfalso
    obtain ⟨-, -, hirr⟩ := h
    have hy₁3m : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hy₁3, Units.val_one]
    obtain ⟨b, hb, hk⟩ := exists_eigenbasis hτ hτ1 h3 hy₁3m
    obtain ⟨k, hk0⟩ := hk 0
    set W : Submodule K (Fin 3 → K) := K ∙ b 0 with hW
    have hWinv : ∀ v ∈ W, (y₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
      intro v hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [Matrix.mulVec_smul, hk0, smul_smul]
      exact Submodule.mem_span_singleton.mpr ⟨a * τ ^ (k : ℕ), rfl⟩
    have hb0 : b 0 ≠ 0 := hb.ne_zero 0
    rcases hirr W hWinv with hbot | htop
    · apply hb0
      have : b 0 ∈ W := Submodule.mem_span_singleton_self _
      rw [hbot] at this
      exact (Submodule.mem_bot K).mp this
    · have h1 : Module.finrank K W = 1 := finrank_span_singleton hb0
      rw [htop, finrank_top, Module.finrank_fin_fun] at h1
      norm_num at h1

theorem exists_heis_pair (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {E : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hES : E ≤ projImage (slPi π 3 (p ^ f) K)) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) :
    ∃ y₁ ∈ slPi π 3 (p ^ f) K, ∃ y₂ ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk y₁ ∈ E ∧ ProjGenLinGroup.mk y₂ ∈ E ∧
      Subgroup.zpowers (ProjGenLinGroup.mk y₁) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk y₂) = E ∧
      Type123 π (p ^ f) K y₁ 1 ∧
      ∃ ζ : Kˣ, ζ ≠ 1 ∧ y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂ := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨e₁, he₁E, he₁1, e₂, he₂E, he₂⟩ := exists_two_of_card_nine hE hE9
  have hcomm_bar : e₁ * e₂ = e₂ * e₁ :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩)
  obtain ⟨y₁, hy₁S, rfl⟩ := hES he₁E
  obtain ⟨y₂, hy₂S, rfl⟩ := hES he₂E
  have hnc := lifts_not_commute hK hq h9 hE hy₁S hy₂S he₁E he₁1 he₂E he₂
  set w := y₁ * y₂ * y₁⁻¹ * y₂⁻¹ with hw
  have hwsc : w ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, hw, map_mul, map_mul, map_mul, map_inv,
      map_inv, hcomm_bar]
    group
  obtain ⟨ζ, hζ⟩ := hwsc
  have hζ' : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂ := by
    rw [hζ, hw]
    group
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply hnc
    rw [map_one] at hζ
    calc y₁ * y₂ = w * (y₂ * y₁) := by rw [hw]; group
      _ = y₂ * y₁ := by rw [← hζ, one_mul]
  have hy₁3 : y₁ ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hy₁S (hE.2 _ he₁E)
  refine ⟨y₁, hy₁S, y₂, hy₂S, he₁E, he₂E, ?_, type_one_of_heis hK hq hy₁S hy₁3 he₁1 hζ1 hζ',
    ζ, hζ1, hζ'⟩
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have hord : orderOf (ProjGenLinGroup.mk y₁) = 3 := orderOf_eq_prime (hE.2 _ he₁E) he₁1
  have hcard := card_zpowers_sup_zpowers (hE.2 _ he₂E) hord he₂ hcomm_bar.symm
  exact Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr he₁E)
    (Subgroup.zpowers_le.mpr he₂E)) (by rw [hE9, hcard])

end KSL3Two

open KSL3Two Sec4
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks1522HessTrans : KS1522HessTrans := by
  intro X _ _ n hn hiso h9 E hE hE9 f hf g hg hf1 hg1
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hn hiso
  have h9K := Sec16.not_nine_dvd_card_sub_one hK h9
  set S := projImage (slPi π 3 (2 ^ n) K) with hS
  set ψ : X →* Matrix.ProjGenLinGroup (Fin 3) K := S.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hE'S : E.map ψ ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact (φ x).2
  have hE'a : CFSG.Assembly.IsElemAbelian 3 (E.map ψ) := CFSG.SectionRank.isElemAbelian_map hE ψ
  have hE'9 : Nat.card (E.map ψ) = 9 := by rw [Subgroup.card_map_of_injective hψinj, hE9]
  obtain ⟨y₁, -, y₂, hy₂S, h₁E, h₂E, hsup, ht1, ζ, hζ1, hζ⟩ :=
    exists_heis_pair hK hq h9K hE'S hE'a hE'9
  obtain ⟨x₁, -, hx₁⟩ := h₁E
  obtain ⟨x₂, -, hx₂⟩ := h₂E
  set e : (⊤ : Subgroup X) ≃* S := Subgroup.topEquiv.trans φ with he
  have he₁ : ((e ⟨x₁, Subgroup.mem_top x₁⟩ : S) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk y₁ := hx₁
  have he₂ : ((e ⟨x₂, Subgroup.mem_top x₂⟩ : S) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk y₂ := hx₂
  have key := transitive_of_heis_pair hK hq e (Subgroup.mem_top x₁) (Subgroup.mem_top x₂) he₁ he₂
    ht1 hy₂S hζ1 hζ
  have hEeq : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ = E := by
    apply Subgroup.map_injective hψinj
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hx₁, hx₂, hsup]
  rw [hEeq] at key
  obtain ⟨w, hw, hwfg⟩ := key f hf hf1 g hg hg1
  exact ⟨w, (Subgroup.mem_inf.mp hw).2, hwfg⟩

end CFSG.RankThree.PartTwo.Sec15
