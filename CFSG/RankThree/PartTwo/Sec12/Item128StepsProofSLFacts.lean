module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec12.Item128StepsProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem exists_model {X : Type} [Group X] {q : ℕ} (hX : IsSLThreePiAt X q) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      p ^ f = q ∧ Nonempty (X ≃* slPi π 3 (p ^ f) K) := by
  obtain ⟨K, _, _, hK⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  set p := ringChar K
  have hcardK : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rcases hK with ⟨hq, hq3, ⟨e⟩⟩ | ⟨hq, hq3, ⟨e⟩⟩
  · have hqn : q = p ^ (n : ℕ) := by rw [← hq, hcardK]
    subst hqn
    exact ⟨true, p, n, K, inferInstance, ⟨hp, n.pos, hcardK⟩, hq3, rfl, ⟨e⟩⟩
  · have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hcardK, hq, sq]⟩
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp at hq3
      · exact h0
    exact ⟨false, p, m, K, inferInstance, ⟨hp, hm1, by rw [hq]; rfl⟩, hq3, rfl, ⟨e⟩⟩

theorem card_le_nine_of_isSLThreePi {X : Type} [Group X] [Finite X] (hX : IsSLThreePi X)
    (S : Subgroup X) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS3 : ∀ x ∈ S, x ^ 3 = 1) :
    Nat.card S ≤ 9 := by
  obtain ⟨q, hXq⟩ := hX
  obtain ⟨π, p, f, K, _, hK, hq, -, ⟨e⟩⟩ := exists_model hXq
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set ι : X →* GL (Fin 3) K := (slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom with hι
  have hinj : Function.Injective ι :=
    (slPi π 3 (p ^ f) K).subtype_injective.comp e.injective
  set T : Subgroup (GL (Fin 3) K) := S.map ι with hT
  have hcard : Nat.card T = Nat.card S := Subgroup.card_map_of_injective hinj
  have : Finite T := Finite.of_equiv S (S.equivMapOfInjective ι hinj).toEquiv
  have h3 : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast hK.three_ne_zero hq
  have h := CFSG.RankThree.PartOne.LIT.card_le_sq_of_det_gl Nat.prime_three h3 (by simp) T
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hS x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hS3 x hx, map_one])
    (by
      rintro _ ⟨x, -, rfl⟩
      exact ((mem_slPi_iff hπ).mp (e x).2).2)
  rw [hcard] at h
  simpa using h

theorem mod_nine_eq_one_of_dvd {q : ℕ} (hq : 1 ≤ q) (h : 9 ∣ q - 1) : q % 9 = 1 := by
  omega

theorem mod_nine_eq_eight_of_dvd {q : ℕ} (hq3 : q % 3 = 2) (h : 9 ∣ q ^ 2 - 1) : q % 9 = 8 := by
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1 : q ^ 2 % 9 = 1 := by omega
  have h2 : q ^ 2 % 9 = (q % 9) ^ 2 % 9 := Nat.pow_mod q 2 9
  have h3 : q % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have h4 : q % 9 % 3 = 2 := by omega
  interval_cases hr : q % 9 <;> simp_all

theorem nine_dvd_card_sub_one {K : Type} [Field K] [Finite K] {μ : K} (hμ9 : μ ^ 9 = 1)
    (hμ3 : μ ^ 3 ≠ 1) : 9 ∣ Nat.card K - 1 := by
  classical
  have := Fintype.ofFinite K
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ9
  set u : Kˣ := Units.mk0 μ hμ0 with hu
  have hu9 : u ^ 9 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ9]; rfl)
  have hu3 : u ^ 3 ≠ 1 := fun h => hμ3 (by
    have := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this)
  have ho : orderOf u = 9 := by
    have hdvd : orderOf u ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hu9)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact absurd (by rw [hk', one_pow]) hu3
    · rw [pow_one] at hk'
      exact absurd (by rw [← hk', pow_orderOf_eq_one]) hu3
    · rw [hk']
      norm_num
  have h := orderOf_dvd_card (x := u)
  rw [ho, Fintype.card_units] at h
  rwa [Nat.card_eq_fintype_card]

theorem pow_three_eq_one_of_not_modNine {X : Type} [Group X] {q : ℕ} (hX : IsSLThreePiAt X q)
    (h9 : ¬ (q % 9 = 1 ∨ q % 9 = 8)) {x : X} (hx : x ^ 3 ∈ Subgroup.center X) : x ^ 3 = 1 := by
  obtain ⟨π, p, f, K, _, hK, hq, hpq, ⟨e⟩⟩ := exists_model hX
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  by_contra hx1
  have hc := KFacts.mem_center_of_mulEquiv e hx
  obtain ⟨ζ, hζ3, hζ⟩ := KFacts.exists_scalar_of_mem_center hK hq hc
  set v : GL (Fin 3) K := ((e x : slPi π 3 (p ^ f) K) : GL (Fin 3) K) with hv
  have hv3 : v ^ 3 = GeneralLinearGroup.scalar (Fin 3) ζ := by
    rw [hv, ← Subgroup.coe_pow, ← map_pow, hζ]
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply hx1
    apply e.injective
    rw [map_one]
    apply Subtype.ext
    rw [hζ, map_one, Subgroup.coe_one]
  have hdet : (v : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp (e x).2).2
  have hvm : (v : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ζ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hv3, coe_scalar_eq_smul]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ 3 = ζ := by
    by_contra hcon
    push Not at hcon
    have h1 := det_eq_of_cube hcon hvm
    rw [hdet] at h1
    exact hζ1 (Units.ext h1.symm)
  have hζ3' : (ζ : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hμ9 : μ ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hμ, hζ3']
  have hμ3 : μ ^ 3 ≠ 1 := by
    rw [hμ]
    exact fun h => hζ1 (Units.ext h)
  have hdvd := nine_dvd_card_sub_one hμ9 hμ3
  rw [hK.card] at hdvd
  apply h9
  cases π
  · right
    change 9 ∣ (p ^ f) ^ 2 - 1 at hdvd
    rw [hpq] at hdvd hq
    exact mod_nine_eq_eight_of_dvd hq hdvd
  · left
    change 9 ∣ p ^ f - 1 at hdvd
    rw [hpq] at hdvd
    exact mod_nine_eq_one_of_dvd (by rw [← hpq]; exact Nat.one_le_pow _ _ hK.prime.pos) hdvd

theorem eq_one_of_conj_eq_scalar_mul {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {V : GL (Fin 3) K}
    (hV : V ∈ slPi π 3 (p ^ f) K) {κ : Kˣ} (hκ : V ^ 3 = GeneralLinearGroup.scalar (Fin 3) κ)
    (hκ1 : κ ≠ 1) {U : GL (Fin 3) K} {ℓ : Kˣ}
    (hU : U * V * U⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * V) : ℓ = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hdet : (V : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hV).2
  have hVH : V ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hV
  have hVm : (V : Matrix (Fin 3) (Fin 3) K) ^ 3 = (κ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hκ, coe_scalar_eq_smul]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ 3 = κ := by
    by_contra hcon
    push Not at hcon
    have h1 := det_eq_of_cube hcon hVm
    rw [hdet] at h1
    exact hκ1 (Units.ext h1.symm)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact κ.ne_zero hμ.symm
  have hVμ : V ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0 ^ 3) := by
    rw [hκ]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ]
  have hVs : V ∉ StatedScalars (Fin 3) K := by
    rintro ⟨s, rfl⟩
    apply hκ1
    have hs3 : (s : K) ^ 3 = 1 := by rw [← det_scalar_three]; exact hdet
    have hs3' : s ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hs3, Units.val_one])
    have h1 : GeneralLinearGroup.scalar (Fin 3) κ = 1 := by rw [← hκ, ← map_pow, hs3', map_one]
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext h2
  obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 hVH hVs hVμ
  rw [zPi_eq hπ hq' hτ hτ1] at hzZ
  obtain ⟨-, ζ, rfl⟩ := Subgroup.mem_inf.mp hzZ
  have hzc : ∀ h : GL (Fin 3) K, h * GeneralLinearGroup.scalar (Fin 3) ζ =
      GeneralLinearGroup.scalar (Fin 3) ζ * h := fun h => commute_of_mem_statedScalars ⟨ζ, rfl⟩ h
  rcases hD with hD | ⟨e, he, hD⟩
  ·
    exfalso
    have hy : V * GeneralLinearGroup.scalar (Fin 3) ζ = g * diagTau hτ * g⁻¹ := by
      rw [← hD]
      group
    have hdetD : ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      ((mem_slPi_iff hπ).mp (diagTau_mem_slPi hπ hq' hτ)).2
    have hζ3 : (ζ : K) ^ 3 = 1 := by
      have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).det) hy
      simp only [Units.val_mul, det_mul, hdet, one_mul] at h1
      rw [det_scalar_three] at h1
      rw [h1, mul_right_comm, hdetD, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, det_one]
    have hζ3' : ζ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζ3, Units.val_one])
    have hy3 : (V * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 = 1 := by
      rw [hy, conj_pow, diagTau_pow_three, mul_one, mul_inv_cancel]
    rw [Commute.mul_pow (hzc V) 3, ← map_pow, hζ3', map_one, mul_one, hκ] at hy3
    apply hκ1
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hy3
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext h2
  ·
    set y := V * GeneralLinearGroup.scalar (Fin 3) ζ with hydef
    have hy : y = g * diagE e * g⁻¹ := by
      rw [← hD]
      group
    have hUy : U * y * U⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * y := by
      rw [hydef]
      calc U * (V * GeneralLinearGroup.scalar (Fin 3) ζ) * U⁻¹
          = U * V * (GeneralLinearGroup.scalar (Fin 3) ζ * U⁻¹) := by group
        _ = U * V * (U⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ) := by rw [hzc U⁻¹]
        _ = (U * V * U⁻¹) * GeneralLinearGroup.scalar (Fin 3) ζ := by group
        _ = _ := by rw [hU]; group
    have htr : ∀ A B : GL (Fin 3) K, (A * B * A⁻¹ : GL (Fin 3) K).val.trace =
        (B : Matrix (Fin 3) (Fin 3) K).trace := by
      intro A B
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have hty : (y : Matrix (Fin 3) (Fin 3) K).trace = (e : K) + 2 := by
      rw [hy, htr g, coe_diagE, Matrix.trace_diagonal, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring
    have h1 := htr U y
    rw [hUy, Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, hty, smul_eq_mul] at h1
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he
      · rw [he, hτ]
      · rw [he, ← pow_mul, mul_comm, pow_mul, hτ, one_pow]
    by_contra hℓ
    have hℓ' : (ℓ : K) ≠ 1 := fun h => hℓ (Units.ext h)
    have he2 : (e : K) + 2 = 0 := by
      have h2 : ((ℓ : K) - 1) * ((e : K) + 2) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (sub_eq_zero.mp h) hℓ'
      · exact h
    have he' : (e : K) = -2 := by linear_combination he2
    rw [he'] at he3
    apply h3
    have h9 : (3 : K) * 3 = 0 := by linear_combination -he3
    rcases mul_eq_zero.mp h9 with h | h <;> exact h

theorem conj_eq_of_mul_inv_mem_center {X : Type} [Group X] (hX : IsSLThreePi X) {u v : X}
    (hv3 : v ^ 3 ∈ Subgroup.center X) (hv1 : v ^ 3 ≠ 1)
    (hu : u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center X) : u * v * u⁻¹ = v := by
  obtain ⟨q, hXq⟩ := hX
  obtain ⟨π, p, f, K, _, hK, hq, -, ⟨e⟩⟩ := exists_model hXq
  obtain ⟨κ, -, hκ⟩ :=
    KFacts.exists_scalar_of_mem_center hK hq (KFacts.mem_center_of_mulEquiv e hv3)
  obtain ⟨ℓ, -, hℓ⟩ :=
    KFacts.exists_scalar_of_mem_center hK hq (KFacts.mem_center_of_mulEquiv e hu)
  set V : GL (Fin 3) K := ((e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K) with hV
  set U : GL (Fin 3) K := ((e u : slPi π 3 (p ^ f) K) : GL (Fin 3) K) with hU
  have hV3 : V ^ 3 = GeneralLinearGroup.scalar (Fin 3) κ := by
    rw [hV, ← Subgroup.coe_pow, ← map_pow, hκ]
  have hκ1 : κ ≠ 1 := by
    rintro rfl
    apply hv1
    apply e.injective
    rw [map_one]
    apply Subtype.ext
    rw [hκ, map_one, Subgroup.coe_one]
  have hUV : U * V * U⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * V := by
    have h1 : U * V * U⁻¹ * V⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ := by
      rw [← hℓ, hU, hV]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc U * V * U⁻¹ = (U * V * U⁻¹ * V⁻¹) * V := by group
      _ = _ := by rw [h1]
  have hℓ1 := eq_one_of_conj_eq_scalar_mul hK hq (e v).2 hV3 hκ1 hUV
  have h1 : e (u * v * u⁻¹ * v⁻¹) = 1 := by
    apply Subtype.ext
    rw [hℓ, hℓ1, map_one, Subgroup.coe_one]
  have h2 : u * v * u⁻¹ * v⁻¹ = 1 := by
    rw [← map_one e] at h1
    exact e.injective h1
  calc u * v * u⁻¹ = (u * v * u⁻¹ * v⁻¹) * v := by group
    _ = v := by rw [h2, one_mul]

end CFSG.RankThree.PartTwo.Sec12.Item128StepsProof
