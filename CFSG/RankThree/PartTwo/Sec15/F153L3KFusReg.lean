module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Res2ProofPGL
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

section FusP1

open scoped Matrix
open CFSG.RankThree.PartTwo.Sec4

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusP1

theorem eq_smul_one_of_sq_smul_commute_regular {Ω : Type} [Field Ω] [CharP Ω 2]
    {b : Fin 3 → (Fin 3 → Ω)} (hb : LinearIndependent Ω b)
    {z T : Matrix (Fin 3) (Fin 3) Ω} {d : Fin 3 → Ω} (hd : Function.Injective d)
    (hz : ∀ i, z *ᵥ b i = d i • b i)
    (hT : T * z = z * T) {μ : Ω} (hμ : T * T = μ • (1 : Matrix (Fin 3) (Fin 3) Ω)) :
    ∃ c : Ω, T = c • (1 : Matrix (Fin 3) (Fin 3) Ω) := by
  choose c hc using fun i => exists_smul_of_commute_regular hb hd hz hT i
  have hsq : ∀ i, c i * c i = μ := by
    intro i
    have h1 : (T * T) *ᵥ b i = μ • b i := by
      rw [hμ, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hc i, Matrix.mulVec_smul, hc i, smul_smul] at h1
    exact smul_left_injective Ω (hb.ne_zero i) h1
  have h2 : (2 : Ω) = 0 := CharTwo.two_eq_zero
  have hceq : ∀ i, c i = c 0 := by
    intro i
    have hsq' : (c i - c 0) * (c i - c 0) = 0 := by
      linear_combination hsq i + hsq 0 + (μ - c i * c 0) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq')
  refine ⟨c 0, eq_of_mulVec_eq_of_linearIndependent hb (fun r => ?_)⟩
  rw [hc r, hceq r, Matrix.smul_mulVec, Matrix.one_mulVec]

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusP1

end FusP1

section FusEB
namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusEB

open Matrix

theorem exists_regular_eigenbasis_of_heis {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {Y Y' : Matrix (Fin 3) (Fin 3) Ω} (hY : IsUnit Y) (hY' : IsUnit Y') {ζ : Ω}
    (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1) (h : Y' * Y = ζ • (Y * Y')) :
    ∃ (b : Fin 3 → (Fin 3 → Ω)) (d : Fin 3 → Ω), LinearIndependent Ω b ∧ Function.Injective d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, Y *ᵥ b i = d i • b i := by
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0] at hζ3
    norm_num at hζ3
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    apply hζ1
    linear_combination hζ3 - ζ * h2
  have hkey : Y * Y' = ζ ^ 2 • (Y' * Y) := by
    have hζ21 : ζ ^ 2 * ζ = 1 := by linear_combination hζ3
    rw [h, smul_smul, hζ21, one_smul]
  have hstep : ∀ (u : Fin 3 → Ω) (μ : Ω), Y *ᵥ u = μ • u →
      Y *ᵥ (Y' *ᵥ u) = (ζ ^ 2 * μ) • (Y' *ᵥ u) := by
    intro u μ hu
    calc Y *ᵥ (Y' *ᵥ u) = (Y * Y') *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = ζ ^ 2 • (Y' *ᵥ (Y *ᵥ u)) := by rw [hkey, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
      _ = ζ ^ 2 • (Y' *ᵥ (μ • u)) := by rw [hu]
      _ = (ζ ^ 2 * μ) • (Y' *ᵥ u) := by rw [Matrix.mulVec_smul, smul_smul]
  have hmv : ∀ (M : Matrix (Fin 3) (Fin 3) Ω) (u : Fin 3 → Ω), IsUnit M → u ≠ 0 →
      M *ᵥ u ≠ 0 := by
    intro M u hM hu hMu
    apply hu
    apply Matrix.mulVec_injective_iff_isUnit.mpr hM
    rw [hMu, Matrix.mulVec_zero]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv_eq : Y *ᵥ v = c • v := by
    have h1 := hv.apply_eq_smul
    rw [Matrix.toLin'_apply] at h1
    exact h1
  have hv_ne : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  have hc0 : c ≠ 0 := by
    intro hc'
    apply hv_ne
    apply Matrix.mulVec_injective_iff_isUnit.mpr hY
    rw [hv_eq, hc', zero_smul, Matrix.mulVec_zero]
  have hw_ne : Y' *ᵥ v ≠ 0 := hmv Y' v hY' hv_ne
  have hx_ne : Y' *ᵥ (Y' *ᵥ v) ≠ 0 := hmv Y' (Y' *ᵥ v) hY' hw_ne
  have hw_eq : Y *ᵥ (Y' *ᵥ v) = (ζ ^ 2 * c) • (Y' *ᵥ v) := hstep v c hv_eq
  have hx_eq : Y *ᵥ (Y' *ᵥ (Y' *ᵥ v)) = (ζ * c) • (Y' *ᵥ (Y' *ᵥ v)) := by
    have h2 := hstep (Y' *ᵥ v) (ζ ^ 2 * c) hw_eq
    have harith : ζ ^ 2 * (ζ ^ 2 * c) = ζ * c := by linear_combination (ζ * c) * hζ3
    rw [harith] at h2
    exact h2
  have h01 : c ≠ ζ ^ 2 * c := fun heq =>
    mul_ne_zero (sub_ne_zero.mpr hζ2) hc0 (by linear_combination -heq)
  have h02 : c ≠ ζ * c := fun heq =>
    mul_ne_zero (sub_ne_zero.mpr hζ1) hc0 (by linear_combination -heq)
  have h12 : ζ ^ 2 * c ≠ ζ * c := fun heq =>
    mul_ne_zero (mul_ne_zero hζ0 (sub_ne_zero.mpr hζ1)) hc0 (by linear_combination heq)
  have hd_inj : Function.Injective ![c, ζ ^ 2 * c, ζ * c] := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
  have hd_ne : ∀ i, (![c, ζ ^ 2 * c, ζ * c] : Fin 3 → Ω) i ≠ 0 := by
    intro i
    fin_cases i
    · exact hc0
    · exact mul_ne_zero (pow_ne_zero 2 hζ0) hc0
    · exact mul_ne_zero hζ0 hc0
  have hEV : ∀ (u : Fin 3 → Ω) (μ : Ω), Y *ᵥ u = μ • u → u ≠ 0 →
      Module.End.HasEigenvector (Matrix.toLin' Y) μ u := by
    intro u μ hu hu0
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact ⟨hu, hu0⟩
  have hli : LinearIndependent Ω ![v, Y' *ᵥ v, Y' *ᵥ (Y' *ᵥ v)] := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' Y)
      ![c, ζ ^ 2 * c, ζ * c] hd_inj _ ?_
    intro i
    fin_cases i
    · exact hEV v c hv_eq hv_ne
    · exact hEV (Y' *ᵥ v) (ζ ^ 2 * c) hw_eq hw_ne
    · exact hEV (Y' *ᵥ (Y' *ᵥ v)) (ζ * c) hx_eq hx_ne
  refine ⟨![v, Y' *ᵥ v, Y' *ᵥ (Y' *ᵥ v)], ![c, ζ ^ 2 * c, ζ * c], hli, hd_inj, hd_ne, ?_⟩
  intro i
  fin_cases i
  · exact hv_eq
  · exact hw_eq
  · exact hx_eq

theorem exists_regular_eigenbasis_of_heis_extend {L : Type} [Field L]
    {Y Y' : Matrix (Fin 3) (Fin 3) L} (hY : IsUnit Y) (hY' : IsUnit Y') {ζ : L}
    (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1) (h : Y' * Y = ζ • (Y * Y')) :
    ∃ (b : Fin 3 → (Fin 3 → AlgebraicClosure L)) (d : Fin 3 → AlgebraicClosure L),
      LinearIndependent (AlgebraicClosure L) b ∧ Function.Injective d ∧ (∀ i, d i ≠ 0) ∧
      ∀ i, (Y.map (algebraMap L (AlgebraicClosure L))) *ᵥ b i = d i • b i := by
  have hYφ : IsUnit (Y.map (algebraMap L (AlgebraicClosure L))) :=
    hY.map (RingHom.mapMatrix (algebraMap L (AlgebraicClosure L)))
  have hY'φ : IsUnit (Y'.map (algebraMap L (AlgebraicClosure L))) :=
    hY'.map (RingHom.mapMatrix (algebraMap L (AlgebraicClosure L)))
  have hrel : Y'.map (algebraMap L (AlgebraicClosure L)) * Y.map (algebraMap L (AlgebraicClosure L)) =
      algebraMap L (AlgebraicClosure L) ζ •
        (Y.map (algebraMap L (AlgebraicClosure L)) * Y'.map (algebraMap L (AlgebraicClosure L))) := by
    ext i j
    have hij := congrArg (algebraMap L (AlgebraicClosure L)) (congrFun (congrFun h i) j)
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul] using hij
  have hζ1φ : algebraMap L (AlgebraicClosure L) ζ ≠ 1 := by
    intro hc
    apply hζ1
    apply (algebraMap L (AlgebraicClosure L)).injective
    rw [hc, map_one]
  have hζ3φ : algebraMap L (AlgebraicClosure L) ζ ^ 3 = 1 := by
    rw [← map_pow, hζ3, map_one]
  exact exists_regular_eigenbasis_of_heis hYφ hY'φ hζ1φ hζ3φ hrel

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusEB

end FusEB

section FusNI

open scoped Matrix
open Matrix (ProjGenLinGroup)

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusNI

theorem l3ni_coe_scalar {K : Type} [Field K] (u : K) :
    (Matrix.scalar (Fin 3) u : Matrix (Fin 3) (Fin 3) K) = u • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem l3ni_smul_of_mk_eq {K : Type} [Field K] {A B : GL (Fin 3) K}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    ∃ κ : K, (B : Matrix (Fin 3) (Fin 3) K) = κ • (A : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  refine ⟨(u : K), ?_⟩
  rw [← hu, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, l3ni_coe_scalar, Matrix.mul_smul,
    Matrix.mul_one]

theorem l3ni_smul_one_of_mk_sq {K : Type} [Field K] {A : GL (Fin 3) K}
    (h : Matrix.ProjGenLinGroup.mk (A * A) = 1) :
    ∃ μ : K, μ ≠ 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
        μ • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar,
    MonoidHom.mem_range] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨(u : K), u.ne_zero, ?_⟩
  rw [← Units.val_mul, ← hu, Matrix.GeneralLinearGroup.coe_scalar, l3ni_coe_scalar]

theorem l3ni_mk_eq_one_of_smul_one {K : Type} [Field K] {g : GL (Fin 3) K} {c : K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    Matrix.ProjGenLinGroup.mk g = 1 := by
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
  intro x
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem l3ni_map_mul_eq {K Ω : Type} [Field K] [Field Ω] (φ : K →+* Ω)
    {A B : Matrix (Fin 3) (Fin 3) K} {κ : K} (h : A * B = κ • (B * A)) :
    A.map φ * B.map φ = φ κ • (B.map φ * A.map φ) := by
  ext i j
  have hij := congrArg φ (congrFun (congrFun h i) j)
  simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul] using hij

theorem l3ni_map_sq_eq {K Ω : Type} [Field K] [Field Ω] (φ : K →+* Ω)
    {A : Matrix (Fin 3) (Fin 3) K} {μ : K} (h : A * A = μ • (1 : Matrix (Fin 3) (Fin 3) K)) :
    A.map φ * A.map φ = φ μ • (1 : Matrix (Fin 3) (Fin 3) Ω) := by
  ext i j
  have hij := congrArg φ (congrFun (congrFun h i) j)
  by_cases hi : i = j
  · subst hi
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul,
      Matrix.one_apply] using hij
  · simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul,
      Matrix.one_apply, hi] using hij

theorem l3ni_descend {K Ω : Type} [Field K] [Field Ω] (φ : K →+* Ω)
    (hφ : Function.Injective φ) {T : Matrix (Fin 3) (Fin 3) K} {c : Ω}
    (h : T.map φ = c • (1 : Matrix (Fin 3) (Fin 3) Ω)) :
    ∃ c0 : K, T = c0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h00 : φ (T 0 0) = c := by
    simpa [Matrix.map_apply] using congrFun (congrFun h 0) 0
  refine ⟨T 0 0, Matrix.ext fun i j => hφ ?_⟩
  have hij := congrFun (congrFun h i) j
  by_cases hi : i = j
  · subst hi
    simpa [Matrix.map_apply, Matrix.one_apply, h00] using hij
  · simpa [Matrix.map_apply, Matrix.one_apply, hi] using hij

theorem l3ni_commute_mod {Ω : Type} [Field Ω] [CharP Ω 2]
    {b : Fin 3 → (Fin 3 → Ω)} (hb : LinearIndependent Ω b)
    {z T : Matrix (Fin 3) (Fin 3) Ω} {d : Fin 3 → Ω} (hd : Function.Injective d)
    (hz : ∀ i, z *ᵥ b i = d i • b i) (hz0 : ∀ i, d i ≠ 0)
    {μ : Ω} (hμ0 : μ ≠ 0) (hμ : T * T = μ • (1 : Matrix (Fin 3) (Fin 3) Ω))
    {κ : Ω} (hκ : T * z = κ • (z * T)) :
    ∃ c : Ω, T = c • (1 : Matrix (Fin 3) (Fin 3) Ω) := by
  have key : T * T * z = (κ * κ) • (z * (T * T)) := by
    calc T * T * z = T * (T * z) := Matrix.mul_assoc _ _ _
      _ = T * (κ • (z * T)) := by rw [hκ]
      _ = κ • (T * (z * T)) := by rw [Matrix.mul_smul]
      _ = κ • ((T * z) * T) := by rw [Matrix.mul_assoc]
      _ = κ • ((κ • (z * T)) * T) := by rw [hκ]
      _ = κ • (κ • ((z * T) * T)) := by rw [Matrix.smul_mul]
      _ = (κ * κ) • ((z * T) * T) := by rw [smul_smul]
      _ = (κ * κ) • (z * (T * T)) := by rw [Matrix.mul_assoc]
  have h1 : T * T * z = μ • z := by rw [hμ, Matrix.smul_mul, Matrix.one_mul]
  have h1' : z * (T * T) = μ • z := by rw [hμ, Matrix.mul_smul, Matrix.mul_one]
  rw [h1, h1', smul_smul] at key
  have hv : (μ * d 0) • b 0 = (κ * κ * μ * d 0) • b 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) Ω => M *ᵥ b 0) key
    simpa only [Matrix.smul_mulVec, hz 0, smul_smul] using h
  have hμd : μ * d 0 ≠ 0 := mul_ne_zero hμ0 (hz0 0)
  have hκκ : κ * κ = 1 := by
    have e := smul_left_injective Ω (hb.ne_zero (0 : Fin 3)) hv
    have e' : μ * d 0 * (κ * κ) = μ * d 0 * 1 := by linear_combination -e
    exact mul_left_cancel₀ hμd e'
  have h2 : (2 : Ω) = 0 := CharTwo.two_eq_zero
  have hκ1 : κ = 1 := by
    have hsq1 : (κ - 1) * (κ - 1) = 0 := by
      linear_combination hκκ + (1 - κ) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq1)
  have hT' : T * z = z * T := by rw [hκ, hκ1, one_smul]
  exact CFSG.RankThree.PartTwo.Sec15.F153L3K.FusP1.eq_smul_one_of_sq_smul_commute_regular hb hd hz hT' hμ

theorem not_commute_involution_of_regular {K : Type} [Field K] [CharP K 2]
    {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b) {z : GL (Fin 3) K} {d : Fin 3 → K}
    (hd : Function.Injective d) (hz : ∀ i, (z : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i)
    {t : ProjGenLinGroup (Fin 3) K} (ht : orderOf t = 2) :
    t * ProjGenLinGroup.mk z ≠ ProjGenLinGroup.mk z * t := by
  intro hcomm
  obtain ⟨T, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  obtain ⟨κ, hκ⟩ := l3ni_smul_of_mk_eq (A := z * T) (B := T * z)
    (by rw [map_mul, map_mul]; exact hcomm.symm)
  rw [Units.val_mul, Units.val_mul] at hκ
  have hsq : Matrix.ProjGenLinGroup.mk T ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one (Matrix.ProjGenLinGroup.mk T)
    rwa [ht] at h2
  have hTT : Matrix.ProjGenLinGroup.mk (T * T) = 1 := by
    rw [map_mul, ← pow_two, hsq]
  obtain ⟨μ, hμ0, hμ⟩ := l3ni_smul_one_of_mk_sq hTT
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hb.ne_zero i
    apply Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit z)
    rw [hz i, hi, zero_smul, Matrix.mulVec_zero]
  obtain ⟨c, hc⟩ := l3ni_commute_mod hb hd hz hd0 hμ0 hμ hκ
  have hmk := l3ni_mk_eq_one_of_smul_one hc
  rw [hmk, orderOf_one] at ht
  norm_num at ht

theorem not_commute_involution_of_heis {K : Type} [Field K] [CharP K 2] {Y Y' : GL (Fin 3) K}
    {ζ : K} (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (h : (Y' : Matrix (Fin 3) (Fin 3) K) * (Y : Matrix (Fin 3) (Fin 3) K) =
      ζ • ((Y : Matrix (Fin 3) (Fin 3) K) * (Y' : Matrix (Fin 3) (Fin 3) K)))
    {t : ProjGenLinGroup (Fin 3) K} (ht : orderOf t = 2) :
    t * ProjGenLinGroup.mk Y ≠ ProjGenLinGroup.mk Y * t := by
  intro hcomm
  obtain ⟨T, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  obtain ⟨κ, hκ⟩ := l3ni_smul_of_mk_eq (A := Y * T) (B := T * Y)
    (by rw [map_mul, map_mul]; exact hcomm.symm)
  rw [Units.val_mul, Units.val_mul] at hκ
  have hsq : Matrix.ProjGenLinGroup.mk T ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one (Matrix.ProjGenLinGroup.mk T)
    rwa [ht] at h2
  have hTT : Matrix.ProjGenLinGroup.mk (T * T) = 1 := by
    rw [map_mul, ← pow_two, hsq]
  obtain ⟨μ, hμ0, hμ⟩ := l3ni_smul_one_of_mk_sq hTT
  obtain ⟨b, d, hb, hd, hd0, hz⟩ :=
    CFSG.RankThree.PartTwo.Sec15.F153L3K.FusEB.exists_regular_eigenbasis_of_heis_extend (Units.isUnit Y) (Units.isUnit Y') hζ1 hζ3 h
  have hφ : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
    (algebraMap K (AlgebraicClosure K)).injective
  have hμφ : algebraMap K (AlgebraicClosure K) μ ≠ 0 := by
    intro h0
    exact hμ0 (hφ (h0.trans (map_zero (algebraMap K (AlgebraicClosure K))).symm))
  obtain ⟨c, hc⟩ := l3ni_commute_mod hb hd hz hd0 hμφ
    (l3ni_map_sq_eq (algebraMap K (AlgebraicClosure K)) hμ)
    (l3ni_map_mul_eq (algebraMap K (AlgebraicClosure K)) hκ)
  obtain ⟨c0, hc0⟩ := l3ni_descend (algebraMap K (AlgebraicClosure K)) hφ hc
  have hmk := l3ni_mk_eq_one_of_smul_one hc0
  rw [hmk, orderOf_one] at ht
  norm_num at ht

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusNI

end FusNI

section FusHB

open scoped Matrix

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusHB

theorem comm_of_mem_isElemAbelian {G : Type} [Group G] {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

theorem commute_of_conj_one {K : Type} [Field K] {Y y : GL (Fin 3) K}
    (h : Y * y * Y⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) (1 : Kˣ) * y) :
    Y * y = y * Y := by
  rw [map_one, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem not_commute_of_conj_scalar {K : Type} [Field K] [CharP K 2] {Y Y' : GL (Fin 3) K}
    {c : Kˣ} (hc1 : c ≠ 1) (hc : Y * Y' * Y⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c * Y')
    {t : Matrix.ProjGenLinGroup (Fin 3) K} (ht : orderOf t = 2) :
    t * Matrix.ProjGenLinGroup.mk Y ≠ Matrix.ProjGenLinGroup.mk Y * t := by
  have hc3 : c ^ 3 = 1 := CFSG.RankThree.PartTwo.Sec4.pow_three_eq_one_of_conj_eq_scalar_mul hc
  have hcK : (c : K) ≠ 1 := fun h => hc1 (Units.val_eq_one.mp h)
  have hcK3 : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hGL : Y * Y' = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (Y' * Y) := by
    calc Y * Y' = Y * Y' * Y⁻¹ * Y := (inv_mul_cancel_right _ _).symm
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) c * Y') * Y := by rw [hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (Y' * Y) := mul_assoc _ _ _
  have hM : (Y : Matrix (Fin 3) (Fin 3) K) * (Y' : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • ((Y' : Matrix (Fin 3) (Fin 3) K) * (Y : Matrix (Fin 3) (Fin 3) K)) := by
    have h := congrArg Units.val hGL
    simp only [Units.val_mul] at h
    rw [h, CFSG.RankThree.PartTwo.Sec4.coe_scalar_eq_smul, smul_mul_assoc, one_mul]
  have hinv : (Y' : Matrix (Fin 3) (Fin 3) K) * (Y : Matrix (Fin 3) (Fin 3) K) =
      (c : K)⁻¹ • ((Y : Matrix (Fin 3) (Fin 3) K) * (Y' : Matrix (Fin 3) (Fin 3) K)) := by
    rw [hM, smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
  have hζ1 : (c : K)⁻¹ ≠ 1 := fun h => hcK (inv_eq_one.mp h)
  have hζ3 : (c : K)⁻¹ ^ 3 = 1 := by
    rw [inv_pow, hcK3, inv_one]
  exact CFSG.RankThree.PartTwo.Sec15.F153L3K.FusNI.not_commute_involution_of_heis (Y := Y) (Y' := Y') hζ1 hζ3 hinv ht

theorem noInvolution_of_heis {K : Type} [Field K] [CharP K 2] (h3 : (3 : K) ≠ 0)
    {E : Subgroup (Matrix.ProjGenLinGroup (Fin 3) K)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    {y₁ y₂ : GL (Fin 3) K} (h₁ : Matrix.ProjGenLinGroup.mk y₁ ∈ E)
    (h₂ : Matrix.ProjGenLinGroup.mk y₂ ∈ E) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    ∀ a ∈ E, a ≠ 1 → ∀ t : Matrix.ProjGenLinGroup (Fin 3) K, orderOf t = 2 → t * a ≠ a * t := by
  intro a ha ha1 t ht
  obtain ⟨Y, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  obtain ⟨c₁, hc₁⟩ := CFSG.RankThree.PartTwo.Sec15.Proof1513Res2.exists_scalar_of_mk_comm
    (comm_of_mem_isElemAbelian hE ha h₁)
  obtain ⟨c₂, hc₂⟩ := CFSG.RankThree.PartTwo.Sec15.Proof1513Res2.exists_scalar_of_mk_comm
    (comm_of_mem_isElemAbelian hE ha h₂)
  by_cases hc1 : c₁ = 1
  · by_cases hc2 : c₂ = 1
    · exfalso
      subst hc1 hc2
      have hζ3 : ζ ^ 3 = 1 :=
        CFSG.RankThree.PartTwo.Sec4.pow_three_eq_one_of_conj_eq_scalar_mul hζ
      exact ha1 (CFSG.RankThree.PartTwo.Sec4.mk_eq_one_iff_mem_statedScalars.mpr
        (CFSG.RankThree.PartTwo.Sec4.mem_statedScalars_of_commute_heis h3 hζ1 hζ3 hζ
          (commute_of_conj_one hc₁) (commute_of_conj_one hc₂)))
    · exact not_commute_of_conj_scalar hc2 hc₂ ht
  · exact not_commute_of_conj_scalar hc1 hc₁ ht

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusHB

end FusHB

