module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofSymForm
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.GH74.GLS.Stage4.T2F1LocH90

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open Matrix CFSG.LieType.Universal.Unitary

section FormDescent

variable {K : Type} [Field K]

@[expose] def restrictSub (σ : K ≃+* K) (L : Subfield K) (h : ∀ x, σ x ∈ L ↔ x ∈ L) :
    L ≃+* L where
  toFun x := ⟨σ x, (h x).mpr x.2⟩
  invFun x := ⟨σ.symm x, (h (σ.symm x)).mp (by rw [σ.apply_symm_apply]; exact x.2)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : K))
  right_inv x := Subtype.ext (σ.apply_symm_apply (x : K))
  map_mul' x y := Subtype.ext (map_mul σ (x : K) y)
  map_add' x y := Subtype.ext (map_add σ (x : K) y)

theorem coe_restrictSub (σ : K ≃+* K) (L : Subfield K) (h : ∀ x, σ x ∈ L ↔ x ∈ L) (x : L) :
    (restrictSub σ L h x : K) = σ x :=
  rfl

@[expose] def toSub (L : Subfield K) (A : Matrix (Fin 3) (Fin 3) K) (hA : ∀ i j, A i j ∈ L) :
    Matrix (Fin 3) (Fin 3) L :=
  fun i j => ⟨A i j, hA i j⟩

theorem map_toSub (L : Subfield K) (A : Matrix (Fin 3) (Fin 3) K) (hA : ∀ i j, A i j ∈ L) :
    (toSub L A hA).map L.subtype = A :=
  rfl

theorem det_map_subtype_ne_zero (L : Subfield K) {M : Matrix (Fin 3) (Fin 3) L} :
    (M.map L.subtype).det ≠ 0 ↔ M.det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h (Subtype.ext h0)⟩

theorem exists_mul_map_transpose_eq [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (L : Subfield K) (σ : K ≃+* K) (hσL : ∀ x, σ x ∈ L ↔ x ∈ L)
    (hσσ : ∀ x ∈ L, σ (σ x) = x) (A : Matrix (Fin 3) (Fin 3) K) (hAL : ∀ i j, A i j ∈ L)
    (hdet : A.det ≠ 0) {μ : K} (hA : ∀ i j, A i j = μ * σ (A j i)) :
    ∃ (k : GL (Fin 3) K) (c : K), (∀ i j, (k : Matrix (Fin 3) (Fin 3) K) i j ∈ L) ∧ c ≠ 0 ∧
      (k : Matrix (Fin 3) (Fin 3) K) * ((k : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ = c • A := by
  classical
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    have : A = 0 := by ext i j; exact h i j
    simp [this]
  by_cases hid : ∀ x ∈ L, σ x = x
  ·
    have hsym : ∀ i j, A i j = μ * A j i := fun i j => by rw [hA i j, hid _ (hAL j i)]
    have hμ2 : μ * μ = 1 := by
      have h1 := hsym i₀ j₀
      rw [hsym j₀ i₀] at h1
      have : A i₀ j₀ * (μ * μ - 1) = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hij)
    have hμ1 : μ = 1 := by
      rcases mul_self_eq_one_iff.mp hμ2 with h | h
      · exact h
      · exfalso
        have hAT : Aᵀ = -A := by
          ext i j
          rw [transpose_apply, hsym j i, h, Matrix.neg_apply]
          ring
        have hd : A.det = -A.det := by
          calc A.det = Aᵀ.det := (det_transpose A).symm
            _ = (-A).det := by rw [hAT]
            _ = -A.det := by rw [det_neg, Fintype.card_fin]; ring
        apply hdet
        have : (2 : K) * A.det = 0 := by linear_combination hd
        exact (mul_eq_zero.mp this).resolve_left hK2
    set AL := toSub L A hAL with hALdef
    have hALs : ALᵀ = AL := by
      ext i j
      change A j i = A i j
      rw [hsym i j, hμ1, one_mul]
    have hL2 : (2 : L) ≠ 0 := fun h => hK2 (by
      have := congrArg L.subtype h
      rwa [map_ofNat, map_zero] at this)
    have : Finite L := inferInstance
    have hALd : AL.det ≠ 0 := (det_map_subtype_ne_zero L).mp hdet
    obtain ⟨c, h, hc, hh, hAh⟩ := exists_eq_smul_mul_transpose hL2 AL hALs hALd
    have hk₀ : (h.map L.subtype).det ≠ 0 := (det_map_subtype_ne_zero L).mpr hh
    have hc0 : (c : K) ≠ 0 := fun h0 => hc (Subtype.ext h0)
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hk₀, (c : K)⁻¹, fun i j => (h i j).2,
      inv_ne_zero hc0, ?_⟩
    change h.map L.subtype * ((h.map L.subtype).map σ)ᵀ = _
    have hk₀σ : (h.map L.subtype).map σ = h.map L.subtype := by
      ext i j
      exact hid _ (h i j).2
    have hAk : A = (c : K) • (h.map L.subtype * (h.map L.subtype)ᵀ) := by
      have e := congrArg (fun M => M.map L.subtype) hAh
      rw [map_toSub] at e
      rw [e, ← transpose_map, ← Matrix.map_mul]
      ext i j
      simp [Matrix.map_apply]
    rw [hk₀σ, hAk, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  ·
    push Not at hid
    obtain ⟨x₀, hx₀L, hx₀⟩ := hid
    set σL := restrictSub σ L hσL with hσLdef
    have hσL1 : σL ≠ 1 := fun h => hx₀ (by
      have := congrArg (fun φ : L ≃+* L => (φ ⟨x₀, hx₀L⟩ : K)) h
      simpa [σL, coe_restrictSub] using this)
    have hσL2 : σL * σL = 1 := RingEquiv.ext fun x => Subtype.ext (hσσ x x.2)
    have hAji : σ (A j₀ i₀) ≠ 0 := by
      intro h0
      apply hij
      rw [hA i₀ j₀, h0, mul_zero]
    have hμL : μ ∈ L := by
      have hμ : μ = A i₀ j₀ / σ (A j₀ i₀) := by
        rw [eq_div_iff hAji]
        exact (hA i₀ j₀).symm
      rw [hμ]
      exact L.div_mem (hAL _ _) ((hσL _).mpr (hAL _ _))
    have hμμ : μ * σ μ = 1 := by
      have h1 := hA i₀ j₀
      have h3 : σ (A j₀ i₀) = σ μ * A i₀ j₀ := by rw [hA j₀ i₀, map_mul, hσσ _ (hAL _ _)]
      rw [h3] at h1
      have : A i₀ j₀ * (μ * σ μ - 1) = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hij)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hμμ
      exact zero_ne_one hμμ
    have hord : orderOf σL = 2 := orderOf_eq_prime (by rw [sq]; exact hσL2) hσL1
    have : Finite L := inferInstance
    set μL : L := ⟨μ, hμL⟩ with hμLdef
    have hnorm : ∏ i ∈ Finset.range 2, (σL ^ i) μL⁻¹ = 1 := by
      rw [Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one]
      apply Subtype.ext
      change μ⁻¹ * σ μ⁻¹ = 1
      rw [map_inv₀, ← mul_inv, hμμ, inv_one]
    obtain ⟨y, hy0, hy⟩ := CFSG.GH74.GLS.Stage4.Rest.F1Loc.hilbert90_finiteField σL hord hnorm
    have hl : σ y = μ * y := by
      have e : μ⁻¹ * σ y = y := congrArg Subtype.val hy
      calc σ y = μ * (μ⁻¹ * σ y) := by rw [← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
        _ = μ * y := by rw [e]
    have hy0' : (y : K) ≠ 0 := fun h0 => hy0 (Subtype.ext h0)
    set B : Matrix (Fin 3) (Fin 3) K := (y : K) • A with hB
    have hBL : ∀ i j, B i j ∈ L := fun i j => L.mul_mem y.2 (hAL i j)
    have hBh : ∀ i j, σ (B j i) = B i j := fun i j => by
      simp only [hB, Matrix.smul_apply, smul_eq_mul, map_mul, hl]
      rw [hA i j]
      ring
    set BL := toSub L B hBL with hBLdef
    have hBLh : conjTr σL BL = BL := by
      ext i j
      exact hBh i j
    have hBLd : BL.det ≠ 0 := by
      refine (det_map_subtype_ne_zero L).mp ?_
      rw [map_toSub, hB, det_smul]
      exact mul_ne_zero (pow_ne_zero _ hy0') hdet
    have : CharP L p := inferInstance
    have : Fintype L := Fintype.ofFinite L
    obtain ⟨e', hp, he⟩ := FiniteField.card L p
    set e : ℕ := (e' : ℕ) with hedef
    obtain ⟨heven, hpow⟩ :=
      LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution_prime
        hp e'.pos (by rw [Nat.card_eq_fintype_card, he]) hσL1 hσL2
    have hσU : σL = CFSG.LieType.BorelTits.unitaryInvolution L p (e / 2) := by
      ext x
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hpow]
    have hcard : Nat.card L = (p ^ (e / 2)) ^ 2 := by
      rw [Nat.card_eq_fintype_card, he, ← pow_mul]
      congr 1
      obtain ⟨k, hk⟩ := heven
      omega
    have hIU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σL := by
      rw [hσU]
      exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hcard
    obtain ⟨P, hP⟩ :=
      CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hIU hBLh hBLd
    have hσσL : ∀ x : L, σL (σL x) = x := fun x => Subtype.ext (hσσ x x.2)
    set kL : Matrix (Fin 3) (Fin 3) L :=
      conjTr σL ((P⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) with hkL
    have hBP : BL = kL * conjTr σL kL := by
      rw [hkL, LocalAnalysis.ComponentInitial.LinearFlag.conjTr_conjTr hσσL]
      calc BL = conjTr σL ((P : Matrix (Fin 3) (Fin 3) L) * ((P⁻¹ : GL (Fin 3) L) :
            Matrix (Fin 3) (Fin 3) L)) * BL * ((P : Matrix (Fin 3) (Fin 3) L) *
              ((P⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, conjTr_one, Matrix.one_mul,
              Matrix.mul_one]
        _ = conjTr σL ((P⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
            (conjTr σL (P : Matrix (Fin 3) (Fin 3) L) * BL * (P : Matrix (Fin 3) (Fin 3) L)) *
              ((P⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
            rw [conjTr_mul]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP, Matrix.mul_one]
    have hkLd : kL.det ≠ 0 := by
      intro h0
      apply hBLd
      rw [hBP, det_mul, h0, zero_mul]
    have hk₀ : (kL.map L.subtype).det ≠ 0 := (det_map_subtype_ne_zero L).mpr hkLd
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hk₀, (y : K), fun i j => (kL i j).2, hy0',
      ?_⟩
    change kL.map L.subtype * ((kL.map L.subtype).map σ)ᵀ = _
    have e1 : ((kL.map L.subtype).map σ)ᵀ = (conjTr σL kL).map L.subtype := by
      ext i j
      rfl
    rw [e1, ← Matrix.map_mul, ← hBP, map_toSub]

end FormDescent

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
