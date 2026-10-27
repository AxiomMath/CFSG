module

public import CFSG.RankThree.PartTwo.Sec12.Item125DiagKFact
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.Sec12.Item125DiagSU

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank (StatedScalars StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ClassicalGroups.UnitaryFlag

variable {n : ℕ} {K : Type} [Field K]

@[expose] def permZeroOne : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

@[expose] def permOneTwo : GL (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_permZeroOne :
    ((permZeroOne : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] :=
  rfl

theorem coe_permOneTwo :
    ((permOneTwo : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem permZeroOne_mul_self : (permZeroOne : GL (Fin 3) K) * permZeroOne = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_permZeroOne, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem permOneTwo_mul_self : (permOneTwo : GL (Fin 3) K) * permOneTwo = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_permOneTwo, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem permZeroOne_ne_one : (permZeroOne : GL (Fin 3) K) ≠ 1 := by
  intro h1
  have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h1
  simp [coe_permZeroOne] at this

theorem permOneTwo_ne_one : (permOneTwo : GL (Fin 3) K) ≠ 1 := by
  intro h1
  have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) h1
  simp [coe_permOneTwo] at this

theorem permZeroOne_mem (h : UnitaryFieldData 2 n K) : permZeroOne ∈ unitarySU 2 n K 3 := by
  have : CharP K 2 := h.charP
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [coe_permZeroOne, det_fin_three]
    simp [CharTwo.neg_eq]
  · rw [coe_permZeroOne]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem permOneTwo_mem (h : UnitaryFieldData 2 n K) : permOneTwo ∈ unitarySU 2 n K 3 := by
  have : CharP K 2 := h.charP
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [coe_permOneTwo, det_fin_three]
    simp [CharTwo.neg_eq]
  · rw [coe_permOneTwo]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem glAut_permZeroOne (φ : K ≃+* K) : glAut φ permZeroOne = permZeroOne := by
  apply Units.ext
  rw [coe_glAut, coe_permZeroOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem permOneTwo_mul_diagonal {d : Fin 3 → K} (hd : d 1 = d 2) :
    ((permOneTwo : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d =
      diagonal d * ((permOneTwo : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [coe_permOneTwo]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hd]

theorem eq_diagonal_of_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M) :
    M = diagonal fun i => M i i := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  rw [coe_diagTau] at hM
  have ent : ∀ i j, (M * !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1]) i j =
      (!![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] * M) i j := fun i j => by rw [hM]
  have aux : ∀ {x a b : K}, a ≠ b → x * a = b * x → x = 0 := fun {x a b} hab h => by
    have h' : x * (a - b) = 0 := by rw [mul_sub, h, mul_comm, sub_self]
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr hab)
  have e01 := ent 0 1
  have e02 := ent 0 2
  have e10 := ent 1 0
  have e12 := ent 1 2
  have e20 := ent 2 0
  have e21 := ent 2 1
  simp [mul_apply, Fin.sum_univ_three] at e01 e02 e10 e12 e20 e21
  have m01 : M 0 1 = 0 := aux (Ne.symm hττ2) e01
  have m02 : M 0 2 = 0 := aux (Ne.symm hτ1) (by rw [mul_one]; exact e02)
  have m10 : M 1 0 = 0 := aux hττ2 e10
  have m12 : M 1 2 = 0 := aux (Ne.symm hτ2) (by rw [mul_one]; exact e12)
  have m20 : M 2 0 = 0 := aux hτ1 (by rw [one_mul]; exact e20)
  have m21 : M 2 1 = 0 := aux hτ2 (by rw [one_mul]; exact e21)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m12, m20, m21]

theorem conclusion_of_fixed {X S : Type*} [Group X] [Group S] (e : X ≃* S)
    {Y : Subgroup (MulAut X)} {σ : MulAut X} (hσY : σ ∈ Y) (hσ1 : σ ≠ 1) {t : S}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (hσt : MulAut.congr e σ t = t) :
    ∃ σ ∈ Y, σ ≠ 1 ∧ ∃ P : Subgroup X, P ≠ ⊥ ∧ IsPGroup 2 P ∧ ∀ p ∈ P, σ p ∈ P := by
  set u := e.symm t with hu
  have hσu : σ u = u := by
    have h1 : e (σ (e.symm t)) = t := hσt
    rw [hu, ← e.symm_apply_apply (σ (e.symm t)), h1]
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← map_pow, sq, ht2, map_one]
  refine ⟨σ, hσY, hσ1, Subgroup.zpowers u, ?_, ?_, ?_⟩
  · intro hbot
    apply ht1
    have hmem : u ∈ (⊥ : Subgroup X) := hbot ▸ Subgroup.mem_zpowers u
    rw [Subgroup.mem_bot] at hmem
    rw [← e.apply_symm_apply t, ← hu, hmem, map_one]
  · rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hu2,
      _root_.one_zpow]
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, by simp only [map_zpow, hσu]⟩

set_option maxHeartbeats 400000 in
theorem ks125TypeCInvolSU : KS125TypeCInvolSU := by
  intro X _ _ hXq hX x hxZ hx3 Y hYab hY9 hconjY hfix
  obtain ⟨q, K, _, _, hK, hq3, hqe, ⟨e₀⟩⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = 2 ^ n := by
    obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
    have hq2 : 2 ∣ q := even_iff_two_dvd.mp hqe
    have hcard : q ^ 2 = ringChar K ^ (m : ℕ) := by rw [← hK, Nat.card_eq_fintype_card, hm]
    have h2p : 2 ∣ ringChar K := by
      have h1 : 2 ∣ ringChar K ^ (m : ℕ) := hcard ▸ dvd_pow hq2 two_ne_zero
      exact Nat.prime_two.dvd_of_dvd_pow h1
    have hp2 : ringChar K = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
    rw [hp2] at hcard
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show q ∣ 2 ^ (m : ℕ) from hcard ▸ dvd_pow_self q two_ne_zero)
    exact ⟨k, hk⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hqe
      exact absurd hqe (by decide)
    · exact h0
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, by rw [hK, ← pow_mul, mul_comm]⟩
  have hPi : PiField false 2 n K := ⟨Nat.prime_two, hn1, hK⟩
  have hq : ModThree false (2 ^ n) := hq3
  have hπ : (false : Bool) = false → UnitaryFieldData 2 n K := fun _ => h
  have hq' : (false : Bool) = false → ModThree false (2 ^ n) := fun _ => hq
  have hXp : Group.IsPerfect X := hXq.1
  have hq2 : 2 < 2 ^ n := by
    by_contra hle
    push Not at hle
    have hn : n = 1 := by
      have h1 : 2 ^ n ≤ 2 ^ 1 := by rw [pow_one]; exact hle
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
      omega
    subst hn
    have hcardX : Nat.card X = 216 := by
      rw [Nat.card_congr e₀.toEquiv]
      exact CFSG.RankThree.CentralLiftU.card_statedSU_three_two h rfl
    have := Fintype.ofFinite X
    have hsolv : Group.IsSolvable X :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcardX]; norm_num)
    have hnt : Nontrivial X := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardX]
      norm_num
    exact Group.IsPerfect.not_isSolvable X hsolv
  have hSp : Group.IsPerfect (unitarySU 2 n K 3) :=
    Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hlift : ∀ β₁ β₂ : MulAut (unitarySU 2 n K 3),
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β₁) =
        MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β₂) → β₁ = β₂ := by
    intro β₁ β₂ h12
    have h12' : centerDescend _ β₁ = centerDescend _ β₂ := (MulAut.congr _).injective h12
    apply mulAut_eq_of_inv_mul_mem_center
    intro g
    have h1 := congrArg (fun τ : MulAut (unitarySU 2 n K 3 ⧸ Subgroup.center _) =>
      τ (g : unitarySU 2 n K 3 ⧸ Subgroup.center _)) h12'
    simp only [centerDescend_mk] at h1
    exact QuotientGroup.eq.mp h1.symm
  have hσ3 : ∀ σ ∈ Y, (MulAut.congr (suCenterEquiv h hq2)
      (centerDescend _ (MulAut.congr e₀ σ))) ^ 3 = 1 := by
    intro σ hσ
    rw [← map_pow, ← map_pow, ← map_pow, hYab.2 σ hσ, map_one, map_one, map_one]
  by_cases hF : ∃ σ ∈ Y, MulAut.congr (suCenterEquiv h hq2)
      (centerDescend _ (MulAut.congr e₀ σ)) ∉ (psuConj h).range
  ·
    obtain ⟨σ, hσY, hD⟩ := hF
    obtain ⟨φ, -, H, hαH⟩ := unitary_order_three_field_descent hq2 _ (hσ3 σ hσY) hD
    have hβ : MulAut.congr e₀ σ = suConj h H * suField h φ * (suConj h H)⁻¹ := by
      apply hlift
      rw [hαH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
        congr_centerDescend_suConj h hq2, congr_centerDescend_suField h hq2]
    set t₀ : unitarySU 2 n K 3 := ⟨permZeroOne, permZeroOne_mem h⟩ with ht₀
    have hft : suField h φ t₀ = t₀ :=
      Subtype.ext (by rw [coe_suField]; exact glAut_permZeroOne φ)
    have hβt : MulAut.congr e₀ σ (suConj h H t₀) = suConj h H t₀ := by
      rw [hβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hft]
    have ht₀1 : t₀ ≠ 1 := fun h1 => permZeroOne_ne_one (congrArg Subtype.val h1)
    have ht₀2 : t₀ * t₀ = 1 := Subtype.ext permZeroOne_mul_self
    refine conclusion_of_fixed e₀ hσY ?_ (by rw [← map_mul, ht₀2, map_one])
      (fun h1 => ht₀1 ((suConj h H).injective (by rw [h1, map_one]))) hβt
    rintro rfl
    exact hD ⟨1, by rw [map_one, map_one, map_one, map_one]⟩
  ·
    push Not at hF
    have hA : ∀ σ ∈ Y, ∃ A : unitaryIsom3 h, MulAut.congr e₀ σ = suConj h A := by
      intro σ hσ
      obtain ⟨A, hA⟩ := hF σ hσ
      exact ⟨A, hlift _ _ (by rw [congr_centerDescend_suConj h hq2]; exact hA.symm)⟩
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hPi hq
    set X₀ : GL (Fin 3) K := ((e₀ x : unitarySU 2 n K 3) : GL (Fin 3) K) with hX₀
    have hX₀S : X₀ ∈ slPi false 3 (2 ^ n) K := (e₀ x).2
    have hX₀U : X₀ ∈ unitaryIsom3 h := unitarySU_le_unitaryIsom3 (e₀ x).2
    have hX₀H : X₀ ∈ glPi false 3 (2 ^ n) K := slPi_le_glPi hπ hX₀S
    have hX₀3 : X₀ ^ 3 = 1 := by
      rw [hX₀, ← Subgroup.coe_pow, ← map_pow, hx3, map_one, Subgroup.coe_one]
    have hX₀det : (X₀ : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_unitarySU_iff h).mp (e₀ x).2).1
    have hX₀s : X₀ ∉ StatedScalars (Fin 3) K := by
      intro hs
      apply hxZ
      have hc : e₀ x ∈ Subgroup.center (unitarySU 2 n K 3) := Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (commute_of_mem_statedScalars hs (g : GL (Fin 3) K))
      have := mem_center_of_mulEquiv e₀.symm hc
      rwa [MulEquiv.symm_apply_apply] at this
    obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hD⟩ := exists_diag_normal_form hPi hq hτ hτ1 hX₀H hX₀s
      (μ := 1) (by rw [one_pow, map_one, hX₀3])
    rw [zPi_eq hπ hq' hτ hτ1] at hzZ
    obtain ⟨-, ζ, rfl⟩ := Subgroup.mem_inf.mp hzZ
    have hzc : ∀ B : GL (Fin 3) K, B * GeneralLinearGroup.scalar (Fin 3) ζ =
        GeneralLinearGroup.scalar (Fin 3) ζ * B := fun B =>
      commute_of_mem_statedScalars ⟨ζ, rfl⟩ B
    have hgU : g ∈ unitaryIsom3 h := (mem_glPi_false h).mp hg
    have hgD : g⁻¹ * (X₀ * GeneralLinearGroup.scalar (Fin 3) ζ) * g = diagTau hτ := by
      rcases hD with hD | ⟨e', he', hD⟩
      · exact hD
      · exfalso
        have he'1 : (e' : K) ≠ 1 := by
          rcases he' with he' | he' <;> rw [he']
          · exact hτ1
          · intro h2
            apply hτ1
            calc τ = τ ^ 3 / τ ^ 2 := by
                  have hτ0 : τ ≠ 0 := by
                    rintro rfl
                    simp at hτ
                  field_simp
              _ = 1 := by rw [hτ, h2, div_one]
        have hdet := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K).det) hD
        rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj', Units.val_mul, det_mul, hX₀det,
          one_mul, det_scalar_three, coe_diagE, det_diagonal, Fin.prod_univ_three] at hdet
        have hcube : (g⁻¹ * (X₀ * GeneralLinearGroup.scalar (Fin 3) ζ) * g) ^ 3 =
            GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) := by
          have h1 : (X₀ * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 =
              GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) := by
            rw [Commute.mul_pow (hzc X₀) 3, hX₀3, one_mul, map_pow]
          have h2 : (g⁻¹ * (X₀ * GeneralLinearGroup.scalar (Fin 3) ζ) * g) ^ 3 =
              g⁻¹ * (X₀ * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 * g := by
            simpa only [inv_inv] using
              (conj_pow (i := 3) (a := g⁻¹) (b := X₀ * GeneralLinearGroup.scalar (Fin 3) ζ))
          rw [h2, h1, mul_assoc, ← commute_of_mem_statedScalars ⟨ζ ^ 3, rfl⟩ g, ← mul_assoc,
            inv_mul_cancel, one_mul]
        rw [hD] at hcube
        have h11 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) 1 1) hcube
        simp [Units.val_pow_eq_pow_val, coe_diagE, Matrix.diagonal_pow] at h11
        apply he'1
        simp at hdet
        rw [← hdet, ← h11]
    have hgX : g⁻¹ * X₀ * g = diagTau hτ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
      rw [← hgD, map_inv]
      symm
      calc g⁻¹ * (X₀ * GeneralLinearGroup.scalar (Fin 3) ζ) * g *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ =
          g⁻¹ * X₀ * (GeneralLinearGroup.scalar (Fin 3) ζ * g) *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by group
        _ = g⁻¹ * X₀ * (g * GeneralLinearGroup.scalar (Fin 3) ζ) *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by rw [hzc g]
        _ = g⁻¹ * X₀ * g := by group
    have hdiag : ∀ σ ∈ Y, ∀ A : unitaryIsom3 h, MulAut.congr e₀ σ = suConj h A →
        ((g⁻¹ * (A : GL (Fin 3) K) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal fun i => ((g⁻¹ * (A : GL (Fin 3) K) * g : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) i i := by
      intro σ hσ A hσA
      apply eq_diagonal_of_commute_diagTau hτ hτ1
      have h1 : (A : GL (Fin 3) K) * X₀ * (A : GL (Fin 3) K)⁻¹ = X₀ := by
        have h2 := congrArg (fun s : unitarySU 2 n K 3 => (s : GL (Fin 3) K))
          (show MulAut.congr e₀ σ (e₀ x) = e₀ x by
            rw [MulAut.congr_apply]
            simp [hfix σ hσ])
        rw [hσA] at h2
        exact h2
      have h2 : (A : GL (Fin 3) K) * X₀ = X₀ * A := by
        calc (A : GL (Fin 3) K) * X₀ = (A : GL (Fin 3) K) * X₀ * (A : GL (Fin 3) K)⁻¹ * A := by
              group
          _ = X₀ * A := by rw [h1]
      set D := g⁻¹ * (A : GL (Fin 3) K) * g with hDdef
      set T := diagTau hτ with hT
      set sc := GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ with hsc
      have h3 : D * (T * sc) = (T * sc) * D := by
        rw [← hgX, hDdef]
        calc g⁻¹ * (A : GL (Fin 3) K) * g * (g⁻¹ * X₀ * g) =
            g⁻¹ * ((A : GL (Fin 3) K) * X₀) * g := by group
          _ = g⁻¹ * (X₀ * A) * g := by rw [h2]
          _ = g⁻¹ * X₀ * g * (g⁻¹ * (A : GL (Fin 3) K) * g) := by group
      have hsD : sc * D = D * sc := (commute_of_mem_statedScalars ⟨ζ⁻¹, rfl⟩ D).symm
      have h4 : D * T = T * D := by
        calc D * T = D * (T * sc) * sc⁻¹ := by group
          _ = (T * sc) * D * sc⁻¹ := by rw [h3]
          _ = T * (sc * D) * sc⁻¹ := by group
          _ = T * (D * sc) * sc⁻¹ := by rw [hsD]
          _ = T * D := by group
      have := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) h4
      simpa only [Units.val_mul] using this
    have hcubeS : ∀ σ ∈ Y, ∀ A : unitaryIsom3 h, MulAut.congr e₀ σ = suConj h A →
        (A : GL (Fin 3) K) ^ 3 ∈ StatedScalars (Fin 3) K := by
      intro σ hσ A hσA
      refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs => ?_
      have h1 : suConj h (A ^ 3) = 1 := by
        rw [map_pow, ← hσA, ← map_pow, hYab.2 σ hσ, map_one]
      have h2 := congrArg (fun φ : MulAut (unitarySU 2 n K 3) =>
        ((φ ⟨s, hs⟩ : unitarySU 2 n K 3) : GL (Fin 3) K)) h1
      simp only [coe_suConj, MulAut.one_apply, Subgroup.coe_pow, Subgroup.coe_inv] at h2
      calc (A : GL (Fin 3) K) ^ 3 * s =
          (A : GL (Fin 3) K) ^ 3 * s * ((A : GL (Fin 3) K) ^ 3)⁻¹ * (A : GL (Fin 3) K) ^ 3 := by
            group
        _ = s * (A : GL (Fin 3) K) ^ 3 := by rw [h2]
    have hconj3 : (MulAut.conj x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    obtain ⟨σ₁, hσ₁Y, hσ₁⟩ : ∃ σ₁ ∈ Y, σ₁ ∉ Subgroup.zpowers (MulAut.conj x) := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show Y ≤ Subgroup.zpowers (MulAut.conj x) from
        fun σ hσ => hcon σ hσ)
      rw [hY9, Nat.card_zpowers] at h1
      have h2 := orderOf_le_of_pow_eq_one (by norm_num) hconj3
      omega
    obtain ⟨A₁, hσ₁A⟩ := hA σ₁ hσ₁Y
    set D₁ := g⁻¹ * (A₁ : GL (Fin 3) K) * g with hD₁
    set d : Fin 3 → K := fun i => (D₁ : Matrix (Fin 3) (Fin 3) K) i i with hd
    have hD₁d : (D₁ : Matrix (Fin 3) (Fin 3) K) = diagonal d := hdiag σ₁ hσ₁Y A₁ hσ₁A
    obtain ⟨κ, hκ⟩ := hcubeS σ₁ hσ₁Y A₁ hσ₁A
    have hD₁3 : D₁ ^ 3 = GeneralLinearGroup.scalar (Fin 3) κ := by
      have h1 : D₁ ^ 3 = g⁻¹ * (A₁ : GL (Fin 3) K) ^ 3 * g := by
        simpa only [inv_inv] using (conj_pow (i := 3) (a := g⁻¹) (b := (A₁ : GL (Fin 3) K)))
      rw [h1, ← hκ, mul_assoc, ← commute_of_mem_statedScalars ⟨κ, rfl⟩ g, ← mul_assoc,
        inv_mul_cancel, one_mul]
    have hd3 : ∀ i, d i ^ 3 = κ := by
      intro i
      have h1 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) i i) hD₁3
      simp only [Units.val_pow_eq_pow_val, hD₁d, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
        coe_scalar_eq_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Pi.pow_apply] at h1
      exact h1
    have hd0 : ∀ i, d i ≠ 0 := fun i h0 => κ.ne_zero (by rw [← hd3 i, h0]; ring)
    obtain ⟨σ, hσY, hσ1, A, hσA, hDA⟩ : ∃ σ ∈ Y, σ ≠ 1 ∧ ∃ A : unitaryIsom3 h,
        MulAut.congr e₀ σ = suConj h A ∧
        ((g⁻¹ * (A : GL (Fin 3) K) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 =
          ((g⁻¹ * (A : GL (Fin 3) K) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
      by_cases hd12 : d 1 = d 2
      · exact ⟨σ₁, hσ₁Y, fun h1 => hσ₁ (h1 ▸ Subgroup.one_mem _), A₁, hσ₁A, hd12⟩
      · have hr3 : (d 2 / d 1) ^ 3 = 1 := by
          rw [div_pow, hd3, hd3, div_self κ.ne_zero]
        have hr1 : d 2 / d 1 ≠ 1 := fun h1 => hd12 ((div_eq_one_iff_eq (hd0 1)).mp h1).symm
        obtain ⟨i, hi⟩ : ∃ i : ℕ, τ ^ (2 * i) = d 2 / d 1 := by
          rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hr3 with h1 | h1 | h1
          · exact absurd h1 hr1
          · refine ⟨2, ?_⟩
            rw [h1]
            calc τ ^ (2 * 2) = τ ^ 3 * τ := by ring
              _ = τ := by rw [hτ, one_mul]
          · exact ⟨1, by rw [h1]⟩
        refine ⟨MulAut.conj x ^ i * σ₁, mul_mem (pow_mem hconjY i) hσ₁Y, ?_,
          ⟨X₀, hX₀U⟩ ^ i * A₁, ?_, ?_⟩
        · intro h1
          apply hσ₁
          rw [eq_inv_of_mul_eq_one_right h1]
          exact inv_mem (pow_mem (Subgroup.mem_zpowers _) i)
        · have hc : MulAut.congr e₀ (MulAut.conj x) = suConj h ⟨X₀, hX₀U⟩ := by
            rw [congr_mulAutConj]
            exact MulEquiv.ext fun s => Subtype.ext (by
              rw [coe_suConj, MulAut.conj_apply]
              simp [X₀])
          rw [map_mul, map_pow, hc, hσ₁A, map_mul, map_pow]
        ·
          have hT : ((diagTau hτ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) =
              diagonal ![τ * ((ζ⁻¹ : Kˣ) : K), τ ^ 2 * ((ζ⁻¹ : Kˣ) : K), ((ζ⁻¹ : Kˣ) : K)] := by
            rw [Units.val_mul, coe_diagTau_eq_diagonal, coe_scalar_eq_smul, Matrix.mul_smul,
              Matrix.mul_one]
            ext j k
            fin_cases j <;> fin_cases k <;> simp [mul_comm]
          have h1 : g⁻¹ * ((⟨X₀, hX₀U⟩ ^ i * A₁ : unitaryIsom3 h) : GL (Fin 3) K) * g =
              (diagTau hτ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹) ^ i * D₁ := by
            rw [← hgX, Subgroup.coe_mul, Subgroup.coe_pow]
            have h2 : (g⁻¹ * X₀ * g) ^ i = g⁻¹ * X₀ ^ i * g := by
              simpa only [inv_inv] using (conj_pow (i := i) (a := g⁻¹) (b := X₀))
            rw [h2, hD₁]
            group
          rw [h1, Units.val_mul, Units.val_pow_eq_pow_val, hT, hD₁d, Matrix.diagonal_pow,
            Matrix.diagonal_mul_diagonal]
          simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
          have hd2 : d 2 = τ ^ (2 * i) * d 1 := by
            rw [hi, div_mul_cancel₀ _ (hd0 1)]
          rw [hd2, mul_pow, ← pow_mul]
          ring
    have hDdiag := hdiag σ hσY A hσA
    set P₁ : GL (Fin 3) K := permOneTwo with hP₁
    have hDt : g⁻¹ * (A : GL (Fin 3) K) * g * P₁ = P₁ * (g⁻¹ * (A : GL (Fin 3) K) * g) := by
      apply Units.ext
      rw [Units.val_mul (g⁻¹ * (A : GL (Fin 3) K) * g), Units.val_mul P₁, hDdiag, hP₁]
      exact (permOneTwo_mul_diagonal hDA).symm
    have ht₁mem : g * P₁ * g⁻¹ ∈ unitarySU 2 n K 3 :=
      conj_mem_unitarySU hgU (permOneTwo_mem h)
    have hc : (A : GL (Fin 3) K) * (g * P₁ * g⁻¹) * (A : GL (Fin 3) K)⁻¹ = g * P₁ * g⁻¹ :=
      calc (A : GL (Fin 3) K) * (g * P₁ * g⁻¹) * (A : GL (Fin 3) K)⁻¹ =
          g * ((g⁻¹ * (A : GL (Fin 3) K) * g) * P₁) *
            (g⁻¹ * (A : GL (Fin 3) K) * g)⁻¹ * g⁻¹ := by group
        _ = g * (P₁ * (g⁻¹ * (A : GL (Fin 3) K) * g)) *
            (g⁻¹ * (A : GL (Fin 3) K) * g)⁻¹ * g⁻¹ := by rw [hDt]
        _ = g * P₁ * g⁻¹ := by group
    have hβt : MulAut.congr e₀ σ ⟨g * P₁ * g⁻¹, ht₁mem⟩ = ⟨g * P₁ * g⁻¹, ht₁mem⟩ := by
      rw [hσA]
      exact Subtype.ext ((coe_suConj A _).trans hc)
    have ht₁1 : (⟨g * P₁ * g⁻¹, ht₁mem⟩ : unitarySU 2 n K 3) ≠ 1 := by
      intro h1
      apply permOneTwo_ne_one (K := K)
      have h2 : g * P₁ * g⁻¹ = 1 := congrArg Subtype.val h1
      calc (permOneTwo : GL (Fin 3) K) = g⁻¹ * (g * P₁ * g⁻¹) * g := by rw [hP₁]; group
        _ = 1 := by rw [h2]; group
    have ht₁2 : (⟨g * P₁ * g⁻¹, ht₁mem⟩ : unitarySU 2 n K 3) * ⟨g * P₁ * g⁻¹, ht₁mem⟩ = 1 := by
      have h1 : g * P₁ * g⁻¹ * (g * P₁ * g⁻¹) = 1 :=
        calc g * P₁ * g⁻¹ * (g * P₁ * g⁻¹) = g * (P₁ * P₁) * g⁻¹ := by group
          _ = 1 := by rw [hP₁, permOneTwo_mul_self]; group
      exact Subtype.ext h1
    exact conclusion_of_fixed e₀ hσY hσ1 ht₁2 ht₁1 hβt

theorem ks125TypeCInvol_closed : KS125TypeCInvol :=
  ks125TypeCInvol_of_su ks125TypeCInvolSU

theorem item125Diag_of_item45
    (h45 : Sec4.Item4_5) :
    Item125Diag :=
  item125Diag_of_su h45 ks125TypeCInvolSU

end CFSG.RankThree.PartTwo.Sec12.Item125DiagSU
