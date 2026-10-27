module

public import CFSG.LocalAnalysis.StandardType.GGPGLQuadPhase
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.UnitaryPhase

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem diagonal_mem_primeFormUnitary (h : UnitaryFieldData 2 n K) {Δ : GL (Fin d) K}
    {δ : Fin d → K} (hΔ : (Δ : Matrix (Fin d) (Fin d) K) = diagonal δ)
    (hδ : ∀ i, δ i ^ (2 ^ n + 1) = 1) : Δ ∈ primeFormUnitary h (idGram K d) := by
  rw [mem_primeFormUnitary]
  have hprod : ∀ i, h.bar (δ i) * δ i = 1 := by
    intro i
    rw [h.bar_apply, ← pow_succ, hδ i]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  rw [hΔ, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  rw [show (fun i => h.bar (δ i) * δ i) = fun _ => (1 : K) from funext hprod]
  simp

theorem exists_unitary_phase_frame (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {x y : GL (Fin d) K}
    (hxU : x ∈ primeFormUnitary h (idGram K d)) (hx : x ^ p = 1) {u₀ : Kˣ} (hu₀ : u₀ ≠ 1)
    (hu₀p : u₀ ^ p = 1) (hxy : x * y = GeneralLinearGroup.scalar (Fin d) u₀ * (y * x)) :
    ∃ (D : GL (Fin d) K) (e : Fin d → ZMod p) (m₀ : ZMod p) (Y : GL (Fin d) K),
      D ∈ primeFormUnitary h (idGram K d) ∧
      (D : Matrix (Fin d) (Fin d) K).det =
        (ζ : K) ^ (∑ i, CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val ∧
      m₀ ≠ 0 ∧ (∀ i j, (Y : Matrix (Fin d) (Fin d) K) i j ≠ 0 → e i = e j + m₀) ∧
      ∀ (z : GL (Fin d) K) (m : ℕ),
        x * z = GeneralLinearGroup.scalar (Fin d) (ζ ^ m) * (z * x) →
          ∃ c : Kˣ, D * z * D⁻¹ = GeneralLinearGroup.scalar (Fin d) c * (z * x ^ m) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  let X : primeFormUnitary h (idGram K d) := ⟨x, hxU⟩
  have hXpow : X ^ p = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using hx
  let H₁ : Subgroup (primeFormUnitary h (idGram K d)) := Subgroup.zpowers X
  have hcomm : ∀ a ∈ H₁, ∀ b ∈ H₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.refl X).zpow_zpow i j).eq
  have hpow : ∀ a ∈ H₁, a ^ p = 1 := by
    intro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hXpZ : X ^ (p : ℤ) = 1 := by simpa using hXpow
    calc
      (X ^ i) ^ p = (X ^ i) ^ (p : ℤ) := (zpow_natCast (X ^ i) p).symm
      _ = X ^ (i * (p : ℤ)) := (zpow_mul X i (p : ℤ)).symm
      _ = X ^ ((p : ℤ) * i) := by rw [mul_comm]
      _ = (X ^ (p : ℤ)) ^ i := zpow_mul X (p : ℤ) i
      _ = 1 := by rw [hXpZ]; simp
  obtain ⟨P, hP⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag (h := h) (p := p) (n := d)
      hp hpq H₁ hcomm hpow
  let Y : primeFormUnitary h (idGram K d) := P⁻¹ * X * P
  have hYdiag : ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
    simpa [Y] using hP X (Subgroup.mem_zpowers X)
  have hYpow : Y ^ p = 1 := by
    change (P⁻¹ * X * P) ^ p = 1
    have hconj : (P⁻¹ * X * P) ^ p = P⁻¹ * X ^ p * P := by
      simpa using (conj_pow (a := P⁻¹) (b := X) (i := p))
    rw [hconj, hXpow]
    simp
  have hYmatpow : (((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p) = 1 := by
    have h := congrArg (fun z : primeFormUnitary h (idGram K d) =>
      ((z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hYpow
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using h
  have hYdiag_eq : ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) :=
    (Matrix.IsDiag.diagonal_diag hYdiag).symm
  have hYmatpow_diag : (((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p) =
      diagonal (fun i =>
        (((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) ^ p) := by
    rw [hYdiag_eq, Matrix.diagonal_pow]
    simp
  have hentry_pow : ∀ i : Fin d,
      (((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) ^ p = 1 := by
    intro i
    have h1 := hYmatpow
    rw [hYmatpow_diag] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  choose e he using fun i =>
    CFSG.StandardType.TypeA.PGLTor.exists_zmod_pow_eq (ζ := (ζ : K)) hζK (hentry_pow i)
  let A₀ : GL (Fin d) K := (P : GL (Fin d) K)⁻¹
  have hYcoe : ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((A₀ * x * A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [show Y = P⁻¹ * X * P from rfl]
    simp [A₀, X]
  have hdiag : ((A₀ * x * A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => (ζ : K) ^ (e i).val) := by
    rw [← hYcoe, hYdiag_eq]
    exact congrArg diagonal (funext fun i => (he i).symm)
  obtain ⟨Δ, hΔdiag, hΔdet, hΔact⟩ :=
    CFSG.StandardType.TypeA.PGLTor.quadPhase_spec (p := p) (K := K) (ι := Fin d) (ζ := ζ)
      hp2 hζ (h := x) (A₀ := A₀) (e := e) hdiag
  have hδ : ∀ i, ((ζ : K) ^
      (CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val) ^ (2 ^ n + 1) = 1 := by
    intro i
    obtain ⟨k, hk⟩ := hpq
    have hb : ((ζ : K) ^ (CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val) ^ p =
        ((ζ : K) ^ p) ^ (CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val := by
      rw [← pow_mul, mul_comm, pow_mul]
    calc
      ((ζ : K) ^ (CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val) ^ (2 ^ n + 1)
          = ((ζ : K) ^ (CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val) ^ (p * k) := by
            rw [hk]
      _ = (((ζ : K) ^ (CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val) ^ p) ^ k := by
            rw [pow_mul]
      _ = (((ζ : K) ^ p) ^ (CFSG.StandardType.TypeA.PGLTor.quadExp (e i)).val) ^ k := by
            rw [hb]
      _ = 1 := by rw [hζK.pow_eq_one, one_pow, one_pow]
  have hΔmem : Δ ∈ primeFormUnitary h (idGram K d) :=
    diagonal_mem_primeFormUnitary h hΔdiag hδ
  let D : GL (Fin d) K := (P : GL (Fin d) K) * Δ * (P : GL (Fin d) K)⁻¹
  have hDmem : D ∈ primeFormUnitary h (idGram K d) := by
    have hPmem : (P : GL (Fin d) K) ∈ primeFormUnitary h (idGram K d) := P.2
    have hPimem : (P : GL (Fin d) K)⁻¹ ∈ primeFormUnitary h (idGram K d) :=
      inv_mem P.2
    have h := mul_mem (mul_mem hPmem hΔmem) hPimem
    simpa [D] using h
  obtain ⟨m₀, hm₀, hXshift⟩ :=
    CFSG.StandardType.TypeA.PGLTor.exists_shift_of_partner (p := p) (K := K) (ι := Fin d)
      (ζ := ζ) hζ hdiag hu₀ hu₀p hxy
  refine ⟨D, e, m₀, A₀ * y * A₀⁻¹, hDmem, by simpa [D, A₀] using hΔdet, hm₀, hXshift, ?_⟩
  intro z m hz
  obtain ⟨c, hc⟩ := hΔact z m hz
  exact ⟨c, by simpa [D, A₀] using hc⟩

theorem exists_unitary_quadPhase (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {x y : GL (Fin d) K}
    (hxU : x ∈ primeFormUnitary h (idGram K d)) (hx : x ^ p = 1) {u₀ : Kˣ} (hu₀ : u₀ ≠ 1)
    (hu₀p : u₀ ^ p = 1) (hxy : x * y = GeneralLinearGroup.scalar (Fin d) u₀ * (y * x)) :
    ∃ D ∈ unitarySU 2 n K d, ∀ (z : GL (Fin d) K) (m : ℕ),
      x * z = GeneralLinearGroup.scalar (Fin d) (ζ ^ m) * (z * x) →
        ∃ c : Kˣ, D * z * D⁻¹ = GeneralLinearGroup.scalar (Fin d) c * (z * x ^ m) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  obtain ⟨D, e, m₀, Y, hDmem, hΔdet, hm₀, hXshift, hact⟩ :=
    exists_unitary_phase_frame h hp hp2 hpq hζ hxU hx hu₀ hu₀p hxy
  have hpcard : p ∣ Fintype.card (Fin d) := by
    have h := CFSG.StandardType.TypeA.PGLTor.card_fiber_mul_eq_of_shift
      (p := p) (K := K) (ι := Fin d) (e := e) (m := m₀) hm₀ (X := Y) hXshift (0 : ZMod p)
    exact ⟨Fintype.card {i // e i = 0}, h.symm⟩
  have hsum1 : ∑ i : Fin d, e i = 0 :=
    CFSG.StandardType.TypeA.PGLTor.sum_eq_zero_of_shift (p := p) (K := K) (ι := Fin d)
      hp2 hpcard hζK hm₀ hXshift
  have hsum2 : ∑ i : Fin d, e i ^ 2 = 0 :=
    CFSG.StandardType.TypeA.PGLTor.sum_sq_eq_zero_of_shift (p := p) (K := K) (ι := Fin d)
      hp2 hp3 hpcard hζK hm₀ hXshift
  have hsumf : ∑ i : Fin d, CFSG.StandardType.TypeA.PGLTor.quadExp (e i) = 0 := by
    have h₁ : ∑ i : Fin d, CFSG.StandardType.TypeA.PGLTor.quadExp (e i)
        = (2 : ZMod p)⁻¹ * ∑ i : Fin d, (e i ^ 2 - e i) := by
      simp only [CFSG.StandardType.TypeA.PGLTor.quadExp]
      rw [Finset.mul_sum]
    have h₂ : ∑ i : Fin d, (e i ^ 2 - e i)
        = (∑ i : Fin d, e i ^ 2) - ∑ i : Fin d, e i :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => e i ^ 2)
        (g := fun i => e i)
    rw [h₁, h₂, hsum2, hsum1, sub_self, mul_zero]
  have hDdet : (D : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [hΔdet, hsumf, ZMod.val_zero, pow_zero]
  have hDunit : ((D : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (D : Matrix (Fin d) (Fin d) K) = 1 := by
    have h := (mem_primeFormUnitary.mp hDmem)
    simpa [idGram] using h
  exact ⟨D, (mem_unitarySU_iff (n := d) h).mpr ⟨hDdet, hDunit⟩, hact⟩

theorem exists_unitary_quadPhase_three (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {x y : GL (Fin d) K}
    (hxU : x ∈ primeFormUnitary h (idGram K d)) (hx : x ^ 3 = 1) {u₀ : Kˣ} (hu₀ : u₀ ≠ 1)
    (hu₀p : u₀ ^ 3 = 1) (hxy : x * y = GeneralLinearGroup.scalar (Fin d) u₀ * (y * x)) :
    ∃ D ∈ primeFormUnitary h (idGram K d), (D : Matrix (Fin d) (Fin d) K).det =
        (ζ : K) ^ (d / 3) ∧ ∀ (z : GL (Fin d) K) (m : ℕ),
      x * z = GeneralLinearGroup.scalar (Fin d) (ζ ^ m) * (z * x) →
        ∃ c : Kˣ, D * z * D⁻¹ = GeneralLinearGroup.scalar (Fin d) c * (z * x ^ m) := by
  classical
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.mpr hζ
  obtain ⟨D, e, m₀, Y, hDmem, hΔdet, hm₀, hXshift, hact⟩ :=
    exists_unitary_phase_frame h Nat.prime_three (by norm_num) hpq hζ hxU hx hu₀ hu₀p hxy
  have hsumf := CFSG.StandardType.TypeA.PGLTor.sum_quadExp_three_of_shift hm₀ hXshift
  refine ⟨D, hDmem, ?_, hact⟩
  rw [hΔdet, hsumf, ZMod.val_natCast, Fintype.card_fin, ← pow_eq_pow_mod _ hζK.pow_eq_one]

end CFSG.StandardType.UnitaryPhase
