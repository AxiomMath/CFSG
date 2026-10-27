module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType

namespace UnitaryCenter

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

private theorem unitaryFieldData_of_card (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f F :=
  ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩

theorem exists_scalar_of_commute_SU (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n)
    {B : GL (Fin n) F}
    (hB : ∀ u : SU (unitaryInvolution F 2 f) n, B * (u : GL (Fin n) F) = (u : GL (Fin n) F) * B) :
    ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨P, hP⟩ := exists_wittMatrix (p := 2) (f := f) hF n
  set N : GL (Fin n) F := P * B * P⁻¹ with hNdef
  have hcomm : ∀ g ∈ unitarySU 2 f F n, N * g = g * N := by
    intro g hg
    let e : SU (unitaryInvolution F 2 f) n ≃* unitarySU 2 f F n :=
      (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hF n))
    let u : SU (unitaryInvolution F 2 f) n := e.symm ⟨g, hg⟩
    have hgu : (e u : GL (Fin n) F) = g := by
      have h := MulEquiv.apply_symm_apply e ⟨g, hg⟩
      exact congrArg Subtype.val h
    have hcu : (e u : GL (Fin n) F) = P * (u : GL (Fin n) F) * P⁻¹ := by
      change ((MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hF n))
          (conjEquiv P hP u) : GL (Fin n) F) = P * (u : GL (Fin n) F) * P⁻¹
      rw [MulEquiv.subgroupCongr_apply, coe_conjEquiv]
    have hg_eq : g = P * (u : GL (Fin n) F) * P⁻¹ := hgu ▸ hcu
    have hu : (u : GL (Fin n) F) = P⁻¹ * g * P := by
      rw [hg_eq]; group
    have key1 : N * g = P * (B * (u : GL (Fin n) F)) * P⁻¹ := by
      rw [hNdef, hu]; group
    have key2 : g * N = P * ((u : GL (Fin n) F) * B) * P⁻¹ := by
      rw [hg_eq, hNdef]; group
    calc N * g = P * (B * (u : GL (Fin n) F)) * P⁻¹ := key1
      _ = P * ((u : GL (Fin n) F) * B) * P⁻¹ := by rw [hB u]
      _ = g * N := key2.symm
  have hUFD : UnitaryFieldData 2 f F := unitaryFieldData_of_card hF hf
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ f + 1 ≠ 1 by
    have := Nat.one_le_two_pow (n := f); omega)
  have hNmem := TableBUE.mem_scalars_of_commute (n := f) (d := n) (p := q) hUFD hqprime hqdvd hcomm
  rw [CFSG.Assembly.largeEvenScalars_def] at hNmem
  obtain ⟨c, hc⟩ := hNmem
  refine ⟨c, ?_⟩
  have hBexpr : B = P⁻¹ * N * P := by rw [hNdef]; group
  rw [hBexpr, ← hc]
  rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_scalar_of_mem_center (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n)
    {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    ∃ c : Fˣ, (z : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧ c ^ n = 1 ∧
      c ^ (2 ^ f + 1) = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hB : ∀ u : SU (unitaryInvolution F 2 f) n,
      (z : GL (Fin n) F) * (u : GL (Fin n) F) = (u : GL (Fin n) F) * (z : GL (Fin n) F) := by
    intro u
    have h := (Subgroup.mem_center_iff.mp hz u).symm
    simpa using congrArg Subtype.val h
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_SU hF hf hn hB
  have hdetz : Matrix.GeneralLinearGroup.det (z : GL (Fin n) F) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact ((mem_SU (σ := unitaryInvolution F 2 f)).mp z.2).1
  have hcn : c ^ n = 1 := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hc
    rw [hdetz, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
    exact h1.symm
  have hq : c ^ (2 ^ f + 1) = 1 := by
    have hUFD : UnitaryFieldData 2 f F := unitaryFieldData_of_card hF hf
    obtain ⟨P, hP⟩ := exists_wittMatrix (p := 2) (f := f) hF n
    have hval : ((conjEquiv P hP z : SUid (unitaryInvolution F 2 f) n) : GL (Fin n) F)
        = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
      rw [coe_conjEquiv, hc, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc,
        mul_inv_cancel, one_mul]
    have hscSUid : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ SUid (unitaryInvolution F 2 f) n :=
      hval ▸ (conjEquiv P hP z).2
    have hSUeq : unitarySU 2 f F n = SUid (unitaryInvolution F 2 f) n := by
      rw [SUid_eq_statedSU (p := 2) (f := f) hF n]
    have hscU : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ unitarySU 2 f F n := by
      rw [hSUeq]; exact hscSUid
    obtain ⟨-, huni⟩ := (mem_unitarySU_iff hUFD).mp hscU
    have h1 := huni
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_map (map_zero hUFD.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal] at h1
    have h2 : Matrix.scalar (Fin n) (hUFD.bar (c : F) * (c : F)) = Matrix.scalar (Fin n) 1 := by
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_one]
      exact h1
    have hbar : hUFD.bar (c : F) * (c : F) = 1 := (Matrix.scalar_inj (n := Fin n)).mp h2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one, ← hUFD.bar_apply (c : F)]
    exact hbar
  exact ⟨c, hc, hcn, hq⟩

end UnitaryCenter

end CFSG.StandardType
