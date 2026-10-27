module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
public import CFSG.RankThree.PartTwo.Sec4.LThreePiEigen
public import CFSG.RankThree.PartTwo.Sec4.LThreePiUnitary

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {p f : ℕ}

namespace PiField

variable {π : Bool}

theorem charP (hK : PiField π p f K) : CharP K p := by
  have := hK.finite
  have := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hK.prime⟩
  cases π
  · exact charP_of_card_eq_prime_pow (f := 2 * f) (by
      rw [← Nat.card_eq_fintype_card, hK.card, piCard, Bool.cond_false, ← pow_mul, mul_comm])
  · exact charP_of_card_eq_prime_pow (f := f) (by
      rw [← Nat.card_eq_fintype_card, hK.card, piCard, Bool.cond_true])

theorem three_ne_zero (hK : PiField π p f K) (hq : ModThree π (p ^ f)) : (3 : K) ≠ 0 := by
  have := hK.charP
  intro h3
  have hp3 : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).mp (by exact_mod_cast h3)
  have hp : p = 3 := (Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_three).mp hp3
  subst hp
  have h0 : 3 ^ f % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by have := hK.one_le; omega))
  cases π
  · change 3 ^ f % 3 = 2 at hq
    omega
  · change 3 ^ f % 3 = 1 at hq
    omega

end PiField

section Scalars

variable {π : Bool}

theorem scalar_mem_glPi_false_iff (h : UnitaryFieldData p f K) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ glPi false 3 (p ^ f) K ↔ (c : K) ^ (p ^ f + 1) = 1 := by
  rw [mem_glPi_false h, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  constructor
  · intro hc
    have := congrFun (diagonal_injective hc) 0
    rw [h.bar_apply, ← pow_succ] at this
    exact this
  · intro hc
    congr 1
    funext i
    rw [h.bar_apply, ← pow_succ]
    exact hc

theorem pow_succ_eq_one_of_cube (hK : PiField false p f K) (hq : ModThree false (p ^ f)) {μ : K}
    (hμ : μ ≠ 0) (h3 : (μ ^ 3) ^ (p ^ f + 1) = 1) : μ ^ (p ^ f + 1) = 1 := by
  have := hK.finite
  have := Fintype.ofFinite K
  set ν := μ ^ (p ^ f + 1)
  have hν3 : ν ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3]
  have hcard : Fintype.card K = (p ^ f + 1) * (p ^ f - 1) + 1 := by
    rw [← Nat.card_eq_fintype_card, hK.card, piCard, Bool.cond_false]
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  have hνq : ν ^ (p ^ f - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one μ hμ
    rw [hcard, Nat.add_sub_cancel, pow_mul] at h
    exact h
  have hcop : Nat.gcd 3 (p ^ f - 1) = 1 := by
    change p ^ f % 3 = 2 at hq
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hν3) (orderOf_dvd_of_pow_eq_one hνq)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

end Scalars

section Conj

variable {π : Bool}

theorem conj_mem_slPi (hπ : π = false → UnitaryFieldData p f K) {g l : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hl : l ∈ slPi π 3 (p ^ f) K) :
    g * l * g⁻¹ ∈ slPi π 3 (p ^ f) K := by
  rw [mem_slPi_iff hπ] at hl ⊢
  refine ⟨mul_mem (mul_mem hg hl.1) (inv_mem hg), ?_⟩
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hl.2, mul_one, ← det_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, det_one]

theorem map_conj_slPi (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    (slPi π 3 (p ^ f) K).map (MulAut.conj g).toMonoidHom = slPi π 3 (p ^ f) K := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    exact conj_mem_slPi hπ hg hl
  · intro l hl
    refine ⟨g⁻¹ * l * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa using conj_mem_slPi hπ (inv_mem hg) hl

theorem map_conj_centralizer (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (D : GL (Fin 3) K) :
    (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {D}).map (MulAut.conj g).toMonoidHom =
      slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {g * D * g⁻¹} := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_slPi hπ hg]
  congr 1
  ext l
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    calc g * m * g⁻¹ * (g * D * g⁻¹) = g * (m * D) * g⁻¹ := by group
      _ = g * (D * m) * g⁻¹ := by rw [hm]
      _ = g * D * g⁻¹ * (g * m * g⁻¹) := by group
  · intro hl
    refine ⟨g⁻¹ * l * g, ?_, by group⟩
    calc g⁻¹ * l * g * D = g⁻¹ * (l * (g * D * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * D * g⁻¹) * l) * g := by rw [hl]
      _ = D * (g⁻¹ * l * g) := by group

theorem map_conj_centMod (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (D : GL (Fin 3) K) :
    (centMod (slPi π 3 (p ^ f) K) D).map (MulAut.conj g).toMonoidHom =
      centMod (slPi π 3 (p ^ f) K) (g * D * g⁻¹) := by
  ext l
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨hmL, z, hz, hzD⟩ := mem_centMod_iff_scalar.mp hm
    refine mem_centMod_iff_scalar.mpr ⟨conj_mem_slPi hπ hg hmL, z, hz, ?_⟩
    have hc := commute_of_mem_statedScalars hz g
    calc g * m * g⁻¹ * (g * D * g⁻¹) * (g * m * g⁻¹)⁻¹ = g * (m * D * m⁻¹) * g⁻¹ := by group
      _ = g * (z * D) * g⁻¹ := by rw [hzD]
      _ = (g * z) * D * g⁻¹ := by group
      _ = (z * g) * D * g⁻¹ := by rw [hc]
      _ = z * (g * D * g⁻¹) := by group
  · intro hl
    obtain ⟨hlL, z, hz, hzD⟩ := mem_centMod_iff_scalar.mp hl
    refine ⟨g⁻¹ * l * g, mem_centMod_iff_scalar.mpr ⟨?_, z, hz, ?_⟩, by group⟩
    · simpa using conj_mem_slPi hπ (inv_mem hg) hlL
    · have hc := commute_of_mem_statedScalars hz g⁻¹
      calc g⁻¹ * l * g * D * (g⁻¹ * l * g)⁻¹ = g⁻¹ * (l * (g * D * g⁻¹) * l⁻¹) * g := by group
        _ = g⁻¹ * (z * (g * D * g⁻¹)) * g := by rw [hzD]
        _ = (g⁻¹ * z) * g * D * g⁻¹ * g := by group
        _ = (z * g⁻¹) * g * D * g⁻¹ * g := by rw [hc]
        _ = z * D := by group

end Conj

section CaseA

variable {π : Bool}

open CFSG.LieType.Universal.Unitary in
theorem conjTr_unitaryInvolution_eq (hK : PiField false p f K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) :
    have := hK.finite
    have : Fact p.Prime := ⟨hK.prime⟩
    have := hK.charP
    conjTr (CFSG.LieType.BorelTits.unitaryInvolution K p f) M = (M.map hK.unitary.bar)ᵀ := by
  intro _ _ _
  ext i j
  simp [conjTr, UnitaryFieldData.bar_apply, iterateFrobenius_def]

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary in
theorem exists_diag_normal_form (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K) (hxs : x ∉ StatedScalars (Fin 3) K)
    {μ : Kˣ} (hμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) (μ ^ 3)) :
    ∃ y : GL (Fin 3) K, (∃ z ∈ zPi π 3 (p ^ f) K, y = x * z) ∧
      ∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * y * g = diagTau hτ ∨
        ∃ e : Kˣ, ((e : K) = τ ∨ (e : K) = τ ^ 2) ∧ g⁻¹ * y * g = diagE e := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
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
  set x' := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * x with hx'
  have hx'3 : (x' : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have : x' ^ 3 = 1 := by
      rw [hx', (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ⁻¹ x).symm.mul_pow, hμ, ← map_pow,
        ← map_mul, inv_pow, inv_mul_cancel, map_one]
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hx's : ∀ c : K, (x' : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hxs
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hdet := congrArg Matrix.det hc
      rw [zero_smul, det_zero] at hdet
      exact (x'.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero hdet
    have hx'Z := mem_statedScalars_of_eq_smul hc hc0
    have : x = GeneralLinearGroup.scalar (Fin 3) μ * x' := by
      rw [hx', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [this]
    exact mul_mem ⟨μ, rfl⟩ hx'Z
  obtain ⟨g₀, j, hg₀, hD⟩ := exists_normal_form hτ hτ1 h3 hx'3 hx's
  set ζ : Kˣ := Units.mk0 (τ ^ (j : ℕ)) (pow_ne_zero _ hτ0) with hζ
  set z := GeneralLinearGroup.scalar (Fin 3) (ζ * μ⁻¹) with hz
  set y := x * z with hy
  have hyx' : (y : Matrix (Fin 3) (Fin 3) K) = τ ^ (j : ℕ) • (x' : Matrix (Fin 3) (Fin 3) K) := by
    have : y = GeneralLinearGroup.scalar (Fin 3) ζ * x' := by
      rw [hy, hx', hz, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ x).eq, map_mul,
        mul_assoc]
    rw [this, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, hζ, Units.val_mk0]
  have hzZ : z ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨_, rfl⟩⟩
    cases π
    · have h := hK.unitary
      rw [hz, scalar_mem_glPi_false_iff h]
      have hτn := pow_succ_eq_one_of_modThree (hq' rfl) hτ
      have hμ3 : ((μ : K) ^ 3) ^ (p ^ f + 1) = 1 := by
        have hmem : GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) ∈ glPi false 3 (p ^ f) K := by
          rw [← hμ]
          exact pow_mem hxH 3
        have := (scalar_mem_glPi_false_iff h _).mp hmem
        rwa [Units.val_pow_eq_pow_val] at this
      have hμn := pow_succ_eq_one_of_cube hK hq μ.ne_zero hμ3
      rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, inv_pow, hμn, inv_one, mul_one, hζ,
        Units.val_mk0, ← pow_mul, mul_comm, pow_mul, hτn, one_pow]
    · exact mem_glPi_true _ _
  have hyH : y ∈ glPi π 3 (p ^ f) K := mul_mem hxH ((Subgroup.mem_inf.mp
    ((zPi_eq hπ hq' hτ hτ1) ▸ hzZ)).1)
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hD1 : ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![τ, τ ^ 2, 1] :=
    coe_diagTau_eq_diagonal hτ
  have hD2 : ((diagE τu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![τ, 1, 1] := by
    rw [coe_diagE, hτu, Units.val_mk0]
  have hD3 : ((diagE (τu ^ 2) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![τ ^ 2, 1, 1] := by
    rw [coe_diagE, Units.val_pow_eq_pow_val, hτu, Units.val_mk0]
  rw [← hyx'] at hD
  have key : ∀ {D : GL (Fin 3) K} (d : Fin 3 → K),
      ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d →
      ((d 0 ≠ d 1 ∧ d 0 ≠ d 2 ∧ d 1 ≠ d 2) ∨ (d 0 ≠ d 1 ∧ d 1 = d 2)) →
      (∀ i, d i ^ 3 = 1) →
      (y : Matrix (Fin 3) (Fin 3) K) * g₀ = g₀ * diagonal d →
      ∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * y * g = D := by
    intro D d hDd hdd hd3 hyg
    have conclude : ∀ (g' : Matrix (Fin 3) (Fin 3) K) (hg' : IsUnit g'),
        (y : Matrix (Fin 3) (Fin 3) K) * g' = g' * diagonal d →
        hg'.unit⁻¹ * y * hg'.unit = D := by
      intro g' hg' hyg'
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, Matrix.mul_assoc, hyg', ←
        Matrix.mul_assoc, IsUnit.val_inv_mul, Matrix.one_mul, hDd]
    cases π
    · have h := hK.unitary
      have := hK.finite
      have : Fact p.Prime := ⟨hK.prime⟩
      have := hK.charP
      set σ := CFSG.LieType.BorelTits.unitaryInvolution K p f
      have hσ : IsUnitaryInvolution σ :=
        isUnitaryInvolution_unitaryInvolution (by rw [hK.card]; rfl)
      have hyu : conjTr σ (y : Matrix (Fin 3) (Fin 3) K) * y = 1 := by
        rw [conjTr_unitaryInvolution_eq hK]
        exact (mem_glPi_false h).mp hyH
      have hdσ : ∀ i, σ (d i) * d i = 1 := by
        intro i
        rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
        exact pow_succ_eq_one_of_modThree (hq' rfl) (hd3 i)
      obtain ⟨g', hg'u, hyg'⟩ := exists_unitary_conj hσ hdσ hdd hyu hg₀ hyg
      have hg' : IsUnit g' :=
        (Matrix.isUnit_iff_isUnit_det g').mpr (Matrix.isUnit_det_of_left_inverse hg'u)
      refine ⟨hg'.unit, ?_, conclude g' hg' hyg'⟩
      rw [mem_glPi_false h, IsUnit.unit_spec, ← conjTr_unitaryInvolution_eq hK]
      exact hg'u
    · exact ⟨hg₀.unit, mem_glPi_true _ _, conclude g₀ hg₀ hyg⟩
  have hc3 : ∀ c : K, c = τ ∨ c = τ ^ 2 ∨ c = 1 → c ^ 3 = 1 := by
    rintro c (rfl | rfl | rfl)
    · exact hτ
    · rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
    · exact one_pow 3
  refine ⟨y, ⟨z, hzZ, rfl⟩, ?_⟩
  rcases hD with hD | hD | hD
  · obtain ⟨g, hg, hgy⟩ := key ![τ, τ ^ 2, 1] hD1 (Or.inl ⟨hττ2, hτ1, hτ2⟩)
      (fun i => by fin_cases i <;> simp [hc3]) hD
    exact ⟨g, hg, Or.inl hgy⟩
  · obtain ⟨g, hg, hgy⟩ := key ![τ, 1, 1] hD2 (Or.inr ⟨by simpa using hτ1, rfl⟩)
      (fun i => by fin_cases i <;> simp [hc3]) hD
    exact ⟨g, hg, Or.inr ⟨τu, Or.inl (by rw [hτu, Units.val_mk0]), hgy⟩⟩
  · obtain ⟨g, hg, hgy⟩ := key ![τ ^ 2, 1, 1] hD3 (Or.inr ⟨by simpa using hτ2, rfl⟩)
      (fun i => by fin_cases i <;> simp [hc3]) hD
    exact ⟨g, hg, Or.inr ⟨τu ^ 2, Or.inr (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0]),
      hgy⟩⟩

end CaseA

end CFSG.RankThree.PartTwo.Sec4
