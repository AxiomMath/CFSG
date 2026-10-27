module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148RNineDef
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTypes

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

section Mat

variable {K : Type} [Field K]

@[expose] noncomputable def diagGL (x : Fin 3 → Kˣ) : GL (Fin 3) K :=
  ⟨diagonal fun i => (x i : K), diagonal fun i => ((x i)⁻¹ : Kˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem coe_diagGL (x : Fin 3 → Kˣ) :
    ((diagGL x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal fun i => (x i : K) :=
  rfl

theorem diagGL_mul (x y : Fin 3 → Kˣ) : diagGL x * diagGL y = diagGL (x * y) := by
  apply Units.ext
  rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
  rfl

theorem diagGL_one : diagGL (1 : Fin 3 → Kˣ) = 1 := by
  apply Units.ext
  rw [coe_diagGL, Units.val_one]
  simp

theorem diagGL_pow (x : Fin 3 → Kˣ) (n : ℕ) : diagGL x ^ n = diagGL (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, diagGL_one]
  | succ n ih => rw [pow_succ, ih, diagGL_mul, pow_succ]

theorem diagGL_mul_comm (x y : Fin 3 → Kˣ) : diagGL x * diagGL y = diagGL y * diagGL x := by
  rw [diagGL_mul, diagGL_mul, mul_comm]

theorem eq_of_diagGL_mem_scalars {x : Fin 3 → Kˣ}
    (hx : diagGL x ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K) :
    x 0 = x 1 ∧ x 1 = x 2 := by
  obtain ⟨c, hc⟩ := hx
  have h := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hc
  simp only [GeneralLinearGroup.coe_scalar, coe_diagGL] at h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  have h2 := congrFun (congrFun h 2) 2
  simp only [scalar_apply, diagonal_apply_eq] at h0 h1 h2
  exact ⟨Units.ext (h0.symm.trans h1), Units.ext (h1.symm.trans h2)⟩

@[expose] def swapGL : GL (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapGL :
    ((swapGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem swapGL_mul_self : (swapGL : GL (Fin 3) K) * swapGL = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_swapGL, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem swapGL_not_mem_scalars :
    (swapGL : GL (Fin 3) K) ∉ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 2) hc
  simp [GeneralLinearGroup.coe_scalar, coe_swapGL, scalar_apply] at h

theorem diagGL_mul_swapGL (a c : Kˣ) :
    diagGL ![a, c, c] * swapGL = swapGL * diagGL ![a, c, c] := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_swapGL]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, diagonal]

theorem glAut_diagGL (σ : K ≃+* K) {x : Fin 3 → Kˣ} (hx : ∀ i, σ (x i : K) = x i) :
    glAut σ (diagGL x) = diagGL x := by
  apply Units.ext
  rw [coe_glAut, coe_diagGL, diagonal_map (map_zero σ)]
  congr 1
  funext i
  exact hx i

theorem glAut_swapGL (σ : K ≃+* K) : glAut σ (swapGL : GL (Fin 3) K) = swapGL := by
  apply Units.ext
  rw [coe_glAut, coe_swapGL]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end Mat

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem diagGL_mem_unitaryIsom3 {x : Fin 3 → Kˣ} (hn : ∀ i, h.norm (x i : K) = 1) :
    diagGL x ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_diagGL, diagonal_map (map_zero h.bar), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have := hn i
  rw [UnitaryFieldData.norm, mul_comm] at this
  exact this

theorem swapGL_mem_unitaryIsom3 : (swapGL : GL (Fin 3) K) ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_swapGL]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem exists_omega (h9 : 2 ^ f % 9 = 8) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ h.norm (ω : K) = 1 ∧
      ∀ σ : K ≃+* K, σ ^ 3 = 1 → σ (ω : K) = ω := by
  classical
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 2 ^ (2 * f) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [hcard]
    have h1 : 2 ^ (2 * f) % 3 = 1 := by
      rw [mul_comm, pow_mul, Nat.pow_mod]
      have : 2 ^ f % 3 = 2 := by omega
      rw [this]
    have h2 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    norm_num at hω
  refine ⟨ω, hω3, hω1, ?_, fun σ hσ => ?_⟩
  · rw [UnitaryFieldData.norm, h.bar_apply]
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = 3 * k + 2 := ⟨2 ^ f / 3, by omega⟩
    rw [hk, ← pow_succ', show 3 * k + 2 + 1 = 3 * (k + 1) by ring, pow_mul,
      ← Units.val_pow_eq_pow_val, hω3, Units.val_one, one_pow]
  · have hprim : IsPrimitiveRoot (ω : K) 3 :=
      IsPrimitiveRoot.coe_units_iff.mpr (hω ▸ IsPrimitiveRoot.orderOf ω)
    have hσ3 : (σ (ω : K)) ^ 3 = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hω3, Units.val_one, map_one]
    obtain ⟨i, hi, hie⟩ := hprim.eq_pow_of_pow_eq_one hσ3
    have hσσσ : σ (σ (σ (ω : K))) = ω := by
      have h1 : (σ ^ 3) (ω : K) = σ (σ (σ (ω : K))) := rfl
      rw [← h1, hσ]
      rfl
    have hpow : ∀ j : ℕ, σ ((ω : K) ^ j) = (ω : K) ^ (i * j) := fun j => by
      rw [map_pow, ← hie, ← pow_mul]
    rw [← hie, hpow, hpow] at hσσσ
    have hmod : i * (i * i) % 3 = 1 := by
      have h1 : ω ^ (i * (i * i)) = ω ^ 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_one]
        exact hσσσ)
      have := pow_eq_pow_iff_modEq.mp h1
      rw [hω] at this
      exact this
    interval_cases i <;> norm_num at hmod
    rw [← hie, pow_one]

end Model

section Fixed

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] noncomputable def diagHom : (Fin 3 → Kˣ) →* GL (Fin 3) K where
  toFun := diagGL
  map_one' := diagGL_one
  map_mul' x y := (diagGL_mul x y).symm

theorem diagHom_apply (x : Fin 3 → Kˣ) : diagHom x = diagGL x :=
  rfl

theorem exists_fixed_e9_conj {X : Type} [Group X] (β α' : MulAut X) {u d t : X} (hu1 : u ≠ 1)
    (hu3 : u ^ 3 = 1) (hd3 : d ^ 3 = 1) (hud : u * d = d * u) (hdu : d ∉ Subgroup.zpowers u)
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (hut : u * t = t * u) (hu : α' u = u) (hd : α' d = d)
    (ht : α' t = t) :
    ∃ u d t : X, u ≠ 1 ∧ u ^ 3 = 1 ∧ d ^ 3 = 1 ∧ u * d = d * u ∧ d ∉ Subgroup.zpowers u ∧
      t ≠ 1 ∧ t ^ 2 = 1 ∧ u * t = t * u ∧ (β * α' * β⁻¹) u = u ∧ (β * α' * β⁻¹) d = d ∧
        (β * α' * β⁻¹) t = t := by
  have hfix : ∀ x : X, α' x = x → (β * α' * β⁻¹) (β x) = β x := fun x hx => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx]
  refine ⟨β u, β d, β t, fun h1 => hu1 ((map_eq_one_iff β β.injective).mp h1), ?_, ?_, ?_,
    fun hm => hdu ?_, fun h1 => ht1 ((map_eq_one_iff β β.injective).mp h1), ?_, ?_,
    hfix u hu, hfix d hd, hfix t ht⟩
  · rw [← map_pow, hu3, map_one]
  · rw [← map_pow, hd3, map_one]
  · rw [← map_mul, ← map_mul, hud]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, β.injective ?_⟩
    rw [map_zpow, hk]
  · rw [← map_pow, ht2, map_one]
  · rw [← map_mul, ← map_mul, hut]

theorem exists_fixed_e9_model (hb : KF148PGUFieldCent) (h9 : 2 ^ f % 9 = 8)
    (hZ : Subgroup.center (unitaryPSU h 3) = ⊥) {α : MulAut (unitaryPSU h 3)}
    (hα3 : α ^ 3 = 1) (hD : α ∉ (psuConj h).range) :
    ∃ u d t : unitaryPSU h 3, u ≠ 1 ∧ u ^ 3 = 1 ∧ d ^ 3 = 1 ∧ u * d = d * u ∧
      d ∉ Subgroup.zpowers u ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ u * t = t * u ∧
        α u = u ∧ α d = d ∧ α t = t := by
  have hq : 2 < 2 ^ f := by
    have h1 := Nat.mod_le (2 ^ f) 9
    rw [h9] at h1
    omega
  obtain ⟨σ, hσ, H, rfl⟩ := unitary_order_three_field_descent hq α hα3 hD
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨ω, hω3, hω1, hωn, hωσ⟩ := exists_omega (h := h) h9
  have hωσ' := hωσ σ hσ3
  have hn1 : h.norm (1 : K) = 1 := by simp [UnitaryFieldData.norm]
  have hinj := Sec4.RonanKChevTwo.conj_injective_of_center_eq_bot hZ
  set Au : unitaryIsom3 h := ⟨diagGL ![ω, 1, 1], diagGL_mem_unitaryIsom3 fun i => by
    fin_cases i <;> simp [hωn, hn1]⟩ with hAu
  set Ad : unitaryIsom3 h := ⟨diagGL ![1, ω, 1], diagGL_mem_unitaryIsom3 fun i => by
    fin_cases i <;> simp [hωn, hn1]⟩ with hAd
  set At : unitaryIsom3 h := ⟨swapGL, swapGL_mem_unitaryIsom3⟩ with hAt
  obtain ⟨gu, hgu, hgu'⟩ := hb f K h h9 σ hσ Au (glAut_diagGL σ fun i => by
    fin_cases i <;> simp [hωσ'])
  obtain ⟨gd, hgd, hgd'⟩ := hb f K h h9 σ hσ Ad (glAut_diagGL σ fun i => by
    fin_cases i <;> simp [hωσ'])
  obtain ⟨gt, hgt, hgt'⟩ := hb f K h h9 σ hσ At (glAut_swapGL σ)
  set u₀ := unitaryProj h 3 gu with hu₀
  set d₀ := unitaryProj h 3 gd with hd₀
  set t₀ := unitaryProj h 3 gt with ht₀
  have hAu3 : Au ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    change diagGL ![ω, 1, 1] ^ 3 = 1
    rw [diagGL_pow, ← diagGL_one]
    congr 1
    funext i
    fin_cases i <;> simp [hω3]
  have hAt2 : At ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one, sq]
    exact swapGL_mul_self
  have hAud : Au * Ad = Ad * Au := Subtype.ext (diagGL_mul_comm _ _)
  have hAut : Au * At = At * Au := Subtype.ext (diagGL_mul_swapGL ω 1)
  have hu1 : u₀ ≠ 1 := by
    intro h1
    have h2 : psuConj h Au = 1 := by rw [hgu, h1, map_one]
    have h3 := eq_of_diagGL_mem_scalars ((Sec4.psuConj_eq_one_iff Au).mp h2)
    exact hω1 h3.1
  have hu3 : u₀ ^ 3 = 1 := hinj (by rw [map_pow, ← hgu, ← map_pow, hAu3, map_one, map_one])
  have hd3 : d₀ ^ 3 = 1 := by
    have hAd3 : Ad ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      change diagGL ![1, ω, 1] ^ 3 = 1
      rw [diagGL_pow, ← diagGL_one]
      congr 1
      funext i
      fin_cases i <;> simp [hω3]
    exact hinj (by rw [map_pow, ← hgd, ← map_pow, hAd3, map_one, map_one])
  have hud : u₀ * d₀ = d₀ * u₀ := hinj (by
    rw [map_mul, map_mul, ← hgu, ← hgd, ← map_mul, ← map_mul, hAud])
  have hdu : d₀ ∉ Subgroup.zpowers u₀ := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have h1 : psuConj h (Ad * Au ^ (-k)) = 1 := by
      have e1 : d₀ * u₀ ^ (-k) = 1 := by rw [← hk, ← _root_.zpow_add, add_neg_cancel, zpow_zero]
      calc psuConj h (Ad * Au ^ (-k)) = MulAut.conj (d₀ * u₀ ^ (-k)) := by
            rw [map_mul, map_zpow, hgd, hgu, map_mul, map_zpow]
        _ = 1 := by rw [e1, map_one]
    have h2 := (Sec4.psuConj_eq_one_iff _).mp h1
    have h3 : ((Ad * Au ^ (-k) : unitaryIsom3 h) : GL (Fin 3) K) =
        diagGL (![1, ω, 1] * ![ω, 1, 1] ^ (-k)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_zpow]
      change diagHom ![1, ω, 1] * diagHom ![ω, 1, 1] ^ (-k) = _
      rw [← map_zpow, ← map_mul]
      rfl
    rw [h3] at h2
    have h4 := (eq_of_diagGL_mem_scalars h2).2
    simp at h4
    exact hω1 h4
  have ht1 : t₀ ≠ 1 := by
    intro h1
    have h2 : psuConj h At = 1 := by rw [hgt, h1, map_one]
    exact swapGL_not_mem_scalars ((Sec4.psuConj_eq_one_iff At).mp h2)
  have ht2 : t₀ ^ 2 = 1 := hinj (by rw [map_pow, ← hgt, ← map_pow, hAt2, map_one, map_one])
  have hut : u₀ * t₀ = t₀ * u₀ := hinj (by
    rw [map_mul, map_mul, ← hgu, ← hgt, ← map_mul, ← map_mul, hAut])
  exact exists_fixed_e9_conj (psuConj h H) (psuField h σ) hu1 hu3 hd3 hud hdu ht1 ht2 hut hgu'
    hgd' hgt'

end Fixed

section Abstract

theorem isElemAbelian_map_three {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    CFSG.Assembly.IsElemAbelian 3 (E.map φ) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨a, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨b, ⟨z, hz, rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_pow, hE.2 x hx, map_one]

open CFSG.Assembly.RankThreeEven (projSU)

theorem exists_fixed_e9 (hb : KF148PGUFieldCent) {X : Type} [Group X] [Finite X] {f : ℕ}
    (h9 : 2 ^ f % 9 = 8) (hX : Nonempty (X ≃* projSU 3 2 f)) {E : Subgroup (MulAut X)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) :
    ∃ ψ ∈ E, (∀ x : X, MulAut.conj x ≠ ψ) ∧ ∃ u d t : X, u ≠ 1 ∧ u ^ 3 = 1 ∧ d ^ 3 = 1 ∧
      u * d = d * u ∧ d ∉ Subgroup.zpowers u ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ u * t = t * u ∧
        ψ u = u ∧ ψ d = d ∧ ψ t = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · norm_num at h9
    · exact hf
  have hq2 : 2 < 2 ^ f := by
    have h1 := Nat.mod_le (2 ^ f) 9
    rw [h9] at h1
    omega
  set K := GaloisField 2 (2 * f) with hKdef
  have hK : Nat.card K = 2 ^ (2 * f) := GaloisField.card 2 (2 * f) (by omega)
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, hK⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  obtain ⟨eX⟩ := hX
  set φ : X ≃* unitaryPSU h 3 := eX.trans φ₀.symm with hφ
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ :=
    Sec4.RonanK429.center_eq_bot_of_mulEquiv φ₀
      (Sec13.isPerfect_center_projSU 2 f hf (by omega) hq2).2
  set E' : Subgroup (MulAut (unitaryPSU h 3)) := E.map (MulAut.congr φ).toMonoidHom with hE'
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' := isElemAbelian_map_three _ hE
  have hE'27 : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hE27]
  have h3K : (3 : K) ≠ 0 := by
    have h1 : (3 : K) = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    rw [h1]
    exact one_ne_zero
  obtain ⟨α, hαE, hαD⟩ : ∃ α ∈ E', α ∉ (psuConj h).range := by
    by_contra hall
    push Not at hall
    have := Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3K E' hE'e hall
    omega
  obtain ⟨ψ, hψE, rfl⟩ := hαE
  have hα3 : (MulAut.congr φ).toMonoidHom ψ ^ 3 = 1 := hE'e.2 _ ⟨ψ, hψE, rfl⟩
  obtain ⟨u, d, t, hu1, hu3, hd3, hud, hdu, ht1, ht2, hut, hu, hd, ht⟩ :=
    exists_fixed_e9_model hb h9 hZ hα3 hαD
  have hfix : ∀ y : unitaryPSU h 3, (MulAut.congr φ).toMonoidHom ψ y = y →
      ψ (φ.symm y) = φ.symm y := fun y hy => by
    have h1 : φ (ψ (φ.symm y)) = y := hy
    apply φ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h1
  refine ⟨ψ, hψE, fun x hx => hαD ?_, φ.symm u, φ.symm d, φ.symm t,
    fun h1 => hu1 ((map_eq_one_iff φ.symm φ.symm.injective).mp h1), ?_, ?_, ?_, fun hm => hdu ?_,
    fun h1 => ht1 ((map_eq_one_iff φ.symm φ.symm.injective).mp h1), ?_, ?_, hfix u hu,
    hfix d hd, hfix t ht⟩
  ·
    obtain ⟨g, hg⟩ := unitaryProj_surjective h 3 (φ x)
    refine ⟨⟨g, unitarySU_le_unitaryIsom3 g.2⟩, ?_⟩
    rw [← conj_mk_eq_psuConj, ← hx]
    change MulAut.conj (unitaryProj h 3 g) = MulAut.congr φ (MulAut.conj x)
    rw [congr_mulAutConj, hg]
  · rw [← map_pow, hu3, map_one]
  · rw [← map_pow, hd3, map_one]
  · rw [← map_mul, ← map_mul, hud]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, φ.symm.injective ?_⟩
    rw [map_zpow, hk]
  · rw [← map_pow, ht2, map_one]
  · rw [← map_mul, ← map_mul, hut]

end Abstract

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
