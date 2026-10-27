module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Open (quasithinPSU quasithinAntidiag)

theorem statedScalars_map_mulAutConj {ι : Type} [Fintype ι] [DecidableEq ι] {L : Type} [Field L]
    (P : GL ι L) : (StatedScalars ι L).map (MulAut.conj P).toMonoidHom = StatedScalars ι L := by
  have hcent : ∀ c : Lˣ, P * GeneralLinearGroup.scalar ι c * P⁻¹ =
      GeneralLinearGroup.scalar ι c := by
    intro c
    have hc : GeneralLinearGroup.scalar ι c ∈ Subgroup.center (GL ι L) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [Subgroup.mem_center_iff.mp hc P, mul_inv_cancel_right]
  ext B
  simp only [Subgroup.mem_map, StatedScalars, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (hcent c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, hcent c⟩

theorem quasithinAntidiag_eq_antidiag {F : Type*} [Field F] (n : ℕ) :
    quasithinAntidiag n F = (antidiag n : Matrix (Fin n) (Fin n) F) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [quasithinAntidiag, antidiag, Matrix.of_apply, Fin.ext_iff, Fin.val_rev]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

theorem quasithinPSU_eq_map_SU (n p k : ℕ) [Fact p.Prime] :
    quasithinPSU n p k =
      (SU (unitaryInvolution (GaloisField p (2 * k)) p k) n).map ProjGenLinGroup.mk := by
  unfold quasithinPSU
  rw [← Subgroup.closure_eq (SU (unitaryInvolution (GaloisField p (2 * k)) p k) n)]
  congr 2
  ext A
  rw [Set.mem_ofPred_eq, SetLike.mem_coe, mem_SU, quasithinAntidiag_eq_antidiag]
  have hmat : (Matrix.of fun i j =>
      (A : Matrix (Fin n) (Fin n) (GaloisField p (2 * k))) j i ^ (p ^ k)) =
      conjTr (unitaryInvolution (GaloisField p (2 * k)) p k)
        (A : Matrix (Fin n) (Fin n) (GaloisField p (2 * k))) := by
    ext i j
    rw [conjTr, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply,
      unitaryInvolution_apply]
  have hdet : GeneralLinearGroup.det A = 1 ↔
      (A : Matrix (Fin n) (Fin n) (GaloisField p (2 * k))).det = 1 := by
    rw [Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
  rw [hmat, hdet, and_comm]

theorem card_galoisField_two_mul (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    Nat.card (GaloisField p (2 * k)) = (p ^ k) ^ 2 := by
  rw [GaloisField.card p (2 * k) (by omega), ← pow_mul, mul_comm]

theorem exists_map_conj_statedSU_eq_SU (n p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    ∃ P : GL (Fin n) (GaloisField p (2 * k)),
      (StatedSU n (p ^ k) (GaloisField p (2 * k))).map (MulAut.conj P).toMonoidHom =
        SU (unitaryInvolution (GaloisField p (2 * k)) p k) n := by
  have hL := card_galoisField_two_mul p k hk
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := GaloisField p (2 * k)) hL n
  refine ⟨P⁻¹, ?_⟩
  rw [← SUid_eq_statedSU hL n]
  ext B
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨A, hA, rfl⟩
    have h := ((conjEquiv P hP).symm ⟨A, hA⟩).2
    rw [inv_inv]
    exact h
  · intro hB
    exact ⟨P * B * P⁻¹, (conjEquiv P hP ⟨B, hB⟩).2, by group⟩

theorem nonempty_statedProj_statedSU_mulEquiv_quasithinPSU (n p k : ℕ) [Fact p.Prime]
    (hk : k ≠ 0) :
    Nonempty (StatedProj (StatedSU n (p ^ k) (GaloisField p (2 * k))) ≃* quasithinPSU n p k) := by
  obtain ⟨P, hP⟩ := exists_map_conj_statedSU_eq_SU n p k hk
  exact ⟨(statedProjCongr (MulAut.conj P) hP (statedScalars_map_mulAutConj P)).trans
    ((statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (quasithinPSU_eq_map_SU n p k).symm))⟩

theorem lieModel_quasithinPSU {n p k : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .PSU n p k) :
    CFSG.Blueprint.LieModel (quasithinPSU n p k) .PSU n p k := by
  have hk : k ≠ 0 := by
    have := hadm.2.1
    omega
  obtain ⟨f⟩ := nonempty_statedProj_statedSU_mulEquiv_quasithinPSU n p k hk
  exact Or.inl ⟨by decide, hadm, GaloisField p (2 * k), inferInstance, inferInstance,
    card_galoisField_two_mul p k hk, ⟨f.symm⟩⟩

theorem lieModel_of_mulEquiv_quasithinPSU {X : Type} [Group X] {n p k : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSU n p k) (e : X ≃* quasithinPSU n p k) :
    CFSG.Blueprint.LieModel X .PSU n p k := by
  have hk : k ≠ 0 := by
    have := hadm.2.1
    omega
  obtain ⟨f⟩ := nonempty_statedProj_statedSU_mulEquiv_quasithinPSU n p k hk
  exact Or.inl ⟨by decide, hadm, GaloisField p (2 * k), inferInstance, inferInstance,
    card_galoisField_two_mul p k hk, ⟨e.trans f.symm⟩⟩

theorem lieModel_quasithinPSU_four_two :
    CFSG.Blueprint.LieModel (quasithinPSU 4 2 1) .PSU 4 2 1 :=
  lieModel_quasithinPSU ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩

theorem lieModel_quasithinPSU_four_three :
    CFSG.Blueprint.LieModel (quasithinPSU 4 3 1) .PSU 4 3 1 :=
  lieModel_quasithinPSU ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩

end CFSG.Quasithin.H13
