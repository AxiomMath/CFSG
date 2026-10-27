module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119AutTorus

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)

variable {F : Type} [Field F]

theorem torPhi_one (p : ℕ) : torPhi p (1 : rootsOfUnity p F × rootsOfUnity p F) = 1 := by
  unfold torPhi
  refine (congrArg (proj 3 F) ?_).trans (map_one (proj 3 F))
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal_apply]

theorem torPhi_mul (p : ℕ) (x y : rootsOfUnity p F × rootsOfUnity p F) :
    torPhi p (x * y) = torPhi p x * torPhi p y := by
  unfold torPhi
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, coe_diagSL, coe_diagSL,
    diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

@[expose] noncomputable def torHom (p : ℕ) (F : Type) [Field F] :
    (rootsOfUnity p F × rootsOfUnity p F) →* projectiveSL 3 F where
  toFun := torPhi p
  map_one' := torPhi_one p
  map_mul' := torPhi_mul p

@[expose] noncomputable def torSub (p : ℕ) (F : Type) [Field F] : Subgroup (projectiveSL 3 F) :=
  (torHom p F).range

theorem mem_torSub_iff {p : ℕ} (hp : p.Prime) {z : projectiveSL 3 F} :
    z ∈ torSub p F ↔ ∃ (a b c : F) (h : a * b * c = 1), a ^ p = 1 ∧ b ^ p = 1 ∧ c ^ p = 1 ∧
      z = proj 3 F (diagSL a b c h) := by
  constructor
  · intro hz
    rw [torSub, MonoidHom.mem_range] at hz
    obtain ⟨⟨u, v⟩, rfl⟩ := hz
    refine ⟨((u : Fˣ) : F), ((v : Fˣ) : F), (((u : Fˣ) * (v : Fˣ))⁻¹ : Fˣ), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · exact (mem_rootsOfUnity' p _).mp u.2
    · exact (mem_rootsOfUnity' p _).mp v.2
    · exact (mem_rootsOfUnity' p _).mp (by
        rw [mem_rootsOfUnity, inv_pow, mul_pow, (mem_rootsOfUnity p _).mp u.2,
          (mem_rootsOfUnity p _).mp v.2, mul_one, inv_one])
    · rfl
  · rintro ⟨a, b, c, h, ha, hb, hc, rfl⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at ha
      exact zero_ne_one ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hb
      exact zero_ne_one hb
    have hc' : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [torSub, MonoidHom.mem_range]
    refine ⟨(⟨Units.mk0 a ha0, ?_⟩, ⟨Units.mk0 b hb0, ?_⟩), ?_⟩
    · exact (mem_rootsOfUnity' p _).mpr (by simpa using ha)
    · exact (mem_rootsOfUnity' p _).mpr (by simpa using hb)
    · change torPhi p _ = _
      unfold torPhi
      congr 1
      apply Subtype.ext
      simp [diagSL, hc']

theorem torSub_pow_eq_one {p : ℕ} (hp : p.Prime) : ∀ z ∈ torSub p F, z ^ p = 1 := by
  intro z hz
  obtain ⟨a, b, c, h, ha, hb, hc, rfl⟩ := (mem_torSub_iff hp).mp hz
  have hpow : diagSL a b c h ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL, diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [ha, hb, hc]
  rw [← map_pow, hpow, map_one]

theorem torSub_comm {p : ℕ} : ∀ z ∈ torSub p F, ∀ w ∈ torSub p F, z * w = w * z := by
  intro z hz w hw
  rw [torSub, MonoidHom.mem_range] at hz hw
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := hw
  rw [← map_mul, ← map_mul, mul_comm]

theorem torHom_injective {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    Function.Injective (torHom p F) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, v⟩ h
  have h' : torPhi p (u, v) = 1 := h
  rw [torPhi, proj_eq_one_iff] at h'
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp h'
  have e0 : ((u : Fˣ) : F) = (c : F) := by
    simpa using congrFun (congrFun hc 0) 0
  have e1 : ((v : Fˣ) : F) = (c : F) := by
    simpa using congrFun (congrFun hc 1) 1
  have hcp : (c : F) ^ p = 1 := by
    rw [← e0]
    exact (mem_rootsOfUnity' p _).mp u.2
  have hc3' : (c : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hc1 : (c : F) = 1 := eq_one_of_pow_eq_one_of_pow_eq_one hp hp3 hcp hc3'
  have hu1 : (u : Fˣ) = 1 := Units.ext (e0.trans (hc1.trans Units.val_one.symm))
  have hv1 : (v : Fˣ) = 1 := Units.ext (e1.trans (hc1.trans Units.val_one.symm))
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simpa using hu1
  · simpa using hv1

theorem natCard_rootsOfUnity_of_dvd [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F - 1) : Nat.card (rootsOfUnity p F) = p := by
  have : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hle : Subgroup.zpowers x ≤ rootsOfUnity p F :=
    Subgroup.zpowers_le.mpr ((mem_rootsOfUnity p x).mpr hxp)
  have h1 : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have h2 : Nat.card (Subgroup.zpowers x) ≤ Nat.card (rootsOfUnity p F) :=
    Subgroup.card_le_of_le hle
  have h3 : Nat.card (rootsOfUnity p F) ≤ p := card_rootsOfUnity (k := p) (R := F)
  omega

theorem card_torSub [Finite F] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpF : p ∣ Nat.card F - 1) : Nat.card (torSub p F) = p ^ 2 := by
  have inj : Function.Injective (torHom p F) := torHom_injective hp hp3
  rw [torSub, ← Nat.card_congr (MonoidHom.ofInjective inj).toEquiv, Nat.card_prod,
    natCard_rootsOfUnity_of_dvd hp hpF, sq]

theorem conjAut_diagUnits_of_mem_torSub {p : ℕ} (hp : p.Prime) (a b c : Fˣ)
    {z : projectiveSL 3 F} (hz : z ∈ torSub p F) : conjAut 3 F (diagUnits a b c) z = z := by
  obtain ⟨a', b', c', h, -, -, -, rfl⟩ := (mem_torSub_iff hp).mp hz
  rw [conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  refine conj_diag_eq ?_ _ ![a', b', c'] (coe_diagSL a' b' c' h)
  intro i j hij
  rw [coe_diagUnits, diagonal_apply_ne _ hij]

theorem exists_diag_of_centralized {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {τ : Fˣ} (hτ3 : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {z : projectiveSL 3 F} (hz : z ^ p = 1)
    (hc : conjAut 3 F (diagUnits 1 τ (τ ^ 2)) z = z) :
    ∃ (a b c : F) (h : a * b * c = 1), a ^ p = 1 ∧ b ^ p = 1 ∧ c ^ p = 1 ∧
      z = proj 3 F (diagSL a b c h) := by
  obtain ⟨s, rfl⟩ := proj_surjective 3 F z
  have hs := slConjugation_eq_self hp hp3 _ s hz hc
  have hdiag := isDiag_of_slConjugation_eq hτ3 hτ1 hs
  exact exists_diag_pow_eq_one hp hp3 hdiag hz

theorem eq_torSub_of_centralized [Finite F] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpF : p ∣ Nat.card F - 1) {τ : Fˣ} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (Pbar : Subgroup (projectiveSL 3 F)) (hcard : Nat.card Pbar = p ^ 2)
    (hexp : ∀ z ∈ Pbar, z ^ p = 1)
    (hcomm : ∀ z ∈ Pbar, conjAut 3 F (diagUnits 1 τ (τ ^ 2)) z = z) : Pbar = torSub p F := by
  have hle : Pbar ≤ torSub p F := by
    intro z hz
    obtain ⟨a, b, c, h, ha, hb, hc, rfl⟩ :=
      exists_diag_of_centralized hp hp3 hτ3 hτ1 (hexp z hz) (hcomm z hz)
    exact (mem_torSub_iff hp).mpr ⟨a, b, c, h, ha, hb, hc, rfl⟩
  have hcardT : Nat.card (torSub p F) = p ^ 2 := card_torSub hp hp3 hpF
  have hfin : Finite (torSub p F) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero 2 hp.ne_zero)
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcardT, hcard]))

@[expose] def xSL (t : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, t, 0; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

theorem coe_xSL (t : F) :
    ((xSL t : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, t, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem xSL_add (s t : F) : xSL (s + t) = xSL s * xSL t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_xSL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem xSL_zero : xSL (0 : F) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_xSL]

@[expose] noncomputable def xHom (F : Type) [Field F] : Multiplicative F →* projectiveSL 3 F where
  toFun t := proj 3 F (xSL (Multiplicative.toAdd t))
  map_one' := by
    simp only [toAdd_one, xSL_zero, map_one]
  map_mul' := by
    intro x y
    simp only [toAdd_mul, xSL_add, map_mul]

@[expose] noncomputable def rootSub (F : Type) [Field F] : Subgroup (projectiveSL 3 F) :=
  (xHom F).range

theorem xHom_ofAdd (t : F) : xHom F (Multiplicative.ofAdd t) = proj 3 F (xSL t) := rfl

theorem inv_diagUnits (a b c : Fˣ) :
    (diagUnits a b c : GL (Fin 3) F)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagUnits_mul]
  apply Units.ext
  rw [Units.val_one, coe_diagUnits, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem slConjugation_diagUnits_xSL (a b c : Fˣ) (t : F) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F
      (diagUnits a b c) (xSL t) = xSL ((a : F) * (b : F)⁻¹ * t) := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : (b : F) ≠ 0 := b.ne_zero
  have hc : (c : F) ≠ 0 := c.ne_zero
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, coe_xSL, coe_xSL, inv_diagUnits, coe_diagUnits,
    coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, ha, hb, hc] <;>
      (try field_simp) <;> ring

theorem conjAut_diagUnits_xHom (a b c : Fˣ) (t : F) :
    conjAut 3 F (diagUnits a b c) (xHom F (Multiplicative.ofAdd t)) =
      xHom F (Multiplicative.ofAdd ((a : F) * (b : F)⁻¹ * t)) := by
  rw [xHom_ofAdd, xHom_ofAdd, conjAut_proj, slConjugation_diagUnits_xSL]

theorem fieldAut_xHom (σ : F ≃+* F) (t : F) :
    fieldAut 3 F σ (xHom F (Multiplicative.ofAdd t)) = xHom F (Multiplicative.ofAdd (σ t)) := by
  rw [xHom_ofAdd, xHom_ofAdd, fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe σ.toRingHom (xSL t)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_xSL, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem conjAut_diagUnits_mem_rootSub (a b c : Fˣ) {u : projectiveSL 3 F} (hu : u ∈ rootSub F) :
    conjAut 3 F (diagUnits a b c) u ∈ rootSub F := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hu
  have hex : ∃ t : F, x = Multiplicative.ofAdd t :=
    ⟨Multiplicative.toAdd x, (ofAdd_toAdd x).symm⟩
  obtain ⟨t, ht⟩ := hex
  rw [ht]
  exact MonoidHom.mem_range.mpr
    ⟨Multiplicative.ofAdd ((a : F) * (b : F)⁻¹ * t), (conjAut_diagUnits_xHom a b c t).symm⟩

theorem fieldAut_mem_rootSub (σ : F ≃+* F) {u : projectiveSL 3 F} (hu : u ∈ rootSub F) :
    fieldAut 3 F σ u ∈ rootSub F := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hu
  have hex : ∃ t : F, x = Multiplicative.ofAdd t :=
    ⟨Multiplicative.toAdd x, (ofAdd_toAdd x).symm⟩
  obtain ⟨t, ht⟩ := hex
  rw [ht]
  exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (σ t), (fieldAut_xHom σ t).symm⟩

theorem diagSL_mul_xSL (a b c : F) (h : a * b * c = 1) (hb : b ≠ 0) (t : F) :
    diagSL a b c h * xSL t = xSL (a * b⁻¹ * t) * diagSL a b c h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL,
    coe_xSL, coe_xSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply] <;>
      (try field_simp) <;> ring

theorem diagSL_xSL_conj (a b c : F) (h : a * b * c = 1) (hb : b ≠ 0) (t : F) :
    diagSL a b c h * xSL t * (diagSL a b c h)⁻¹ = xSL (a * b⁻¹ * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact diagSL_mul_xSL a b c h hb t

theorem proj_diagSL_conj_mem_rootSub (a b c : F) (h : a * b * c = 1) {u : projectiveSL 3 F}
    (hu : u ∈ rootSub F) :
    proj 3 F (diagSL a b c h) * u * (proj 3 F (diagSL a b c h))⁻¹ ∈ rootSub F := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hu
  have hex : ∃ t : F, x = Multiplicative.ofAdd t :=
    ⟨Multiplicative.toAdd x, (ofAdd_toAdd x).symm⟩
  obtain ⟨t, ht⟩ := hex
  rw [ht]
  refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (a * b⁻¹ * t), ?_⟩
  rw [xHom_ofAdd, xHom_ofAdd, ← diagSL_xSL_conj a b c h hb t, map_mul, map_mul, map_inv]

theorem rootSub_isPGroup [CharP F 2] : IsPGroup 2 (rootSub F) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp g.2
  have hex : ∃ t : F, x = Multiplicative.ofAdd t :=
    ⟨Multiplicative.toAdd x, (ofAdd_toAdd x).symm⟩
  obtain ⟨t, ht⟩ := hex
  rw [ht] at hx
  have h2 : (Multiplicative.ofAdd t) ^ 2 = 1 := by
    rw [pow_two, ← ofAdd_add, CharTwo.add_self_eq_zero t, ofAdd_zero]
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_one, ← hx, ← map_pow, h2, map_one, Subgroup.coe_one]

theorem rootSub_ne_bot : rootSub F ≠ ⊥ := by
  intro h
  have hmem : xHom F (Multiplicative.ofAdd (1 : F)) ∈ rootSub F :=
    MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, rfl⟩
  rw [h, Subgroup.mem_bot, xHom_ofAdd, LinearFlag.proj_eq_one_iff,
    LinearFlag.mem_scalars] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  have h01 := congrFun (congrFun hc 0) 1
  simp [coe_xSL, Matrix.scalar_apply, Matrix.diagonal_apply] at h01

end CFSG.RankThree.PartTwo.Sec21.Hering2119
