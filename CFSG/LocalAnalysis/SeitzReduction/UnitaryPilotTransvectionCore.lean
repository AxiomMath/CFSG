module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreGroup

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore map_perfectCore)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem commute_of_mul_inv_mem {G : Type*} [Group G] {Z : Subgroup G} (hZc : Z ≤ center G)
    (hZ2 : ∀ z ∈ Z, z * z = 1 → z = 1) {A B : G} (hA : A * A = 1)
    (hAB : (B * A)⁻¹ * (A * B) ∈ Z) : B * A = A * B := by
  set z := (B * A)⁻¹ * (A * B) with hz
  have hcomm : ∀ x, z * x = x * z := fun x => (mem_center_iff.1 (hZc hAB) x).symm
  have hABz : A * B = B * A * z := by rw [hz, mul_inv_cancel_left]
  have hzz : z * z = 1 := by
    have e1 : B = A * (A * B) := by rw [← mul_assoc, hA, one_mul]
    have e2 : A * (A * B) = B * (z * z) := by
      calc A * (A * B) = A * (B * A * z) := by rw [hABz]
        _ = (A * B) * A * z := by simp only [mul_assoc]
        _ = B * A * z * A * z := by rw [hABz]
        _ = B * A * (z * A) * z := by simp only [mul_assoc]
        _ = B * A * (A * z) * z := by rw [hcomm A]
        _ = B * (A * A) * (z * z) := by simp only [mul_assoc]
        _ = B * (z * z) := by rw [hA, mul_one]
    have e3 : B * (z * z) = B * 1 := by rw [mul_one, ← e2, ← e1]
    exact mul_left_cancel e3
  rw [hABz, hZ2 z hAB hzz, mul_one]

theorem eq_one_of_mem_unitaryScalars_of_mul_self {z : unitarySU 2 f K n}
    (hz : z ∈ unitaryScalars h n) (hzz : z * z = 1) : z = 1 := by
  have := h.charP
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subtype.ext (Units.ext (Matrix.ext fun a _ => Fin.elim0 a))
  have hmat : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
    rw [hc, GeneralLinearGroup.coe_scalar]
  have h1 := congrArg (fun x : unitarySU 2 f K n =>
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hzz
  simp only [Subgroup.coe_mul, Units.val_mul, hmat, Subgroup.coe_one, Units.val_one, scalar_apply,
    diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h1
  have hc1 : (c : K) = 1 := by
    have h2 : (c : K) ^ 2 = 1 ^ 2 := by rw [one_pow, sq]; exact h1
    exact CharTwo.sq_inj.1 h2
  refine Subtype.ext (Units.ext ?_)
  rw [hmat, hc1, map_one]
  rfl

@[expose] noncomputable def stdTransvection {i j : Fin n} (hij : i ≠ j) : unitaryPSU h n :=
  unitaryProj h n (tvTransSU h hij)

@[expose] def stdTransvectionRadical {i j : Fin n} (hij : i ≠ j) : Subgroup (unitaryPSU h n) :=
  (tvRadical h hij).map (unitaryProj h n)

theorem tvTransSU_mul_self {i j : Fin n} (hij : i ≠ j) : tvTransSU h hij * tvTransSU h hij = 1 := by
  have := h.charP
  rw [tvTransSU, tvESU_mul, ← tvESU_zero_zero h hij]
  refine tvESU_congr h hij (add_zero 0) ?_ _ _
  rw [tvBar_zero, zero_dotProduct, add_zero, CharTwo.add_self_eq_zero]

theorem centralizer_stdTransvection {i j : Fin n} (hij : i ≠ j) :
    centralizer {stdTransvection h hij} =
      (centralizer {tvTransSU h hij}).map (unitaryProj h n) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h n x
    refine ⟨g, mem_centralizer_singleton_iff.2 ?_, rfl⟩
    have hx' := mem_centralizer_singleton_iff.1 hx
    rw [stdTransvection, ← map_mul, ← map_mul] at hx'
    refine commute_of_mul_inv_mem (unitaryScalars_le_center h n)
      (fun z hz hzz => eq_one_of_mem_unitaryScalars_of_mul_self h hz hzz)
      (tvTransSU_mul_self h hij) ?_
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hx', inv_mul_cancel]
  · rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff, stdTransvection, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 hg]

theorem isPGroup_stdTransvectionRadical {i j : Fin n} (hij : i ≠ j) :
    IsPGroup 2 (stdTransvectionRadical h hij) :=
  (isPGroup_tvRadical h hij).map _

theorem stdTransvection_mem_stdTransvectionRadical {i j : Fin n} (hij : i ≠ j) :
    stdTransvection h hij ∈ stdTransvectionRadical h hij :=
  mem_map_of_mem _ (tvTransSU_mem_tvRadical h hij)

theorem blockSU_le_normalizer_stdTransvectionRadical {i j : Fin n} (hij : i ≠ j) :
    blockSU h ({i, j}ᶜ : Finset (Fin n)) ≤
      normalizer (stdTransvectionRadical h hij : Set (unitaryPSU h n)) :=
  ((map_mono ((unitaryBlock_le_centralizer_tvTransSU h hij).trans
    (centralizer_le_normalizer_tvRadical h hij))).trans (le_normalizer_map _))

theorem stdTransvectionRadical_inf_blockSU {i j : Fin n} (hij : i ≠ j) :
    stdTransvectionRadical h hij ⊓ blockSU h ({i, j}ᶜ : Finset (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨r, hr, rfl⟩, ⟨m, hm, hmr⟩⟩
  rw [mem_bot]
  have hker : m⁻¹ * r ∈ unitaryScalars h n := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hmr, inv_mul_cancel]
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 hker
  have hrm : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) (c : K) := by
    have e : r = m * (m⁻¹ * r) := by rw [mul_inv_cancel_left]
    conv_lhs => rw [e]
    rw [Subgroup.coe_mul, Units.val_mul, hc, GeneralLinearGroup.coe_scalar]
  have hi : i ∉ ({i, j}ᶜ : Finset (Fin n)) := by simp
  have hmB := (mem_unitaryBlock h).1 hm
  have hentry : ∀ a, ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a i =
      (1 : Matrix (Fin n) (Fin n) K) a i * c := by
    intro a
    rw [hrm, scalar_apply, mul_diagonal, hmB a i (Or.inr hi)]
  have hcol := congrFun hr.2.1 i
  rw [vecMul_tvVec_apply, hentry, hentry, one_apply_eq, one_apply_ne hij.symm, zero_mul,
    add_zero, one_mul, tvVec_left hij] at hcol
  have hmr' : m = r := by
    refine eq_of_coe_eq ?_
    rw [hrm, hcol, map_one, Matrix.mul_one]
  have hr1 : r ∈ tvRadical h hij ⊓ unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) :=
    ⟨hr, hmr' ▸ hm⟩
  rw [tvRadical_inf_unitaryBlock h hij, mem_bot] at hr1
  rw [hr1, map_one]

theorem perfectCore_centralizer_stdTransvection_eq {i j : Fin n} (hij : i ≠ j)
    (hJ : 2 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    (hperf : ⁅unitaryBlock h ({i, j}ᶜ : Finset (Fin n)),
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n))⁆ = unitaryBlock h ({i, j}ᶜ : Finset (Fin n))) :
    perfectCore (centralizer {stdTransvection h hij}) =
      stdTransvectionRadical h hij ⊔ blockSU h ({i, j}ᶜ : Finset (Fin n)) := by
  have := h.finite
  rw [centralizer_stdTransvection, ← map_perfectCore,
    perfectCore_centralizer_tvTransSU h hij hJ hperf, Subgroup.map_sup, sup_comm]
  rfl

theorem perfectCore_centralizer_stdTransvection_of_perfect {i j : Fin n} (hij : i ≠ j)
    (hJ : 2 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    (hperf : ⁅unitaryBlock h ({i, j}ᶜ : Finset (Fin n)),
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n))⁆ = unitaryBlock h ({i, j}ᶜ : Finset (Fin n))) :
    ∃ Q : Subgroup (unitaryPSU h n), IsPGroup 2 Q ∧
      perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n))) =
        Q ⊔ blockSU h ({i, j}ᶜ : Finset (Fin n)) ∧
      Q ⊓ blockSU h ({i, j}ᶜ : Finset (Fin n)) = ⊥ ∧
      blockSU h ({i, j}ᶜ : Finset (Fin n)) ≤ normalizer (Q : Set (unitaryPSU h n)) ∧
      stdTransvection h hij ∈ Q :=
  ⟨stdTransvectionRadical h hij, isPGroup_stdTransvectionRadical h hij,
    perfectCore_centralizer_stdTransvection_eq h hij hJ hperf,
    stdTransvectionRadical_inf_blockSU h hij, blockSU_le_normalizer_stdTransvectionRadical h hij,
    stdTransvection_mem_stdTransvectionRadical h hij⟩

theorem commutator_unitaryBlock_compl_pair (hn : 5 ≤ n) (hnq : (n, 2 ^ f) ≠ (5, 2))
    {i j : Fin n} (hij : i ≠ j) :
    ⁅unitaryBlock h ({i, j}ᶜ : Finset (Fin n)), unitaryBlock h ({i, j}ᶜ : Finset (Fin n))⁆ =
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) := by
  refine commutator_unitaryBlock_eq h (by rw [card_compl_pair hij]; omega) ?_
  rw [card_compl_pair hij]
  intro h3
  apply hnq
  have h1 := congrArg Prod.fst h3
  have h2 := congrArg Prod.snd h3
  simp only at h1 h2
  rw [show n = 5 by omega, h2]

theorem perfectCore_centralizer_stdTransvection_of_five_le (hn : 5 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (5, 2)) {i j : Fin n} (hij : i ≠ j) :
    ∃ Q : Subgroup (unitaryPSU h n), IsPGroup 2 Q ∧
      perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n))) =
        Q ⊔ blockSU h ({i, j}ᶜ : Finset (Fin n)) ∧
      Q ⊓ blockSU h ({i, j}ᶜ : Finset (Fin n)) = ⊥ ∧
      blockSU h ({i, j}ᶜ : Finset (Fin n)) ≤ normalizer (Q : Set (unitaryPSU h n)) ∧
      stdTransvection h hij ∈ Q :=
  perfectCore_centralizer_stdTransvection_of_perfect h hij (by rw [card_compl_pair hij]; omega)
    (commutator_unitaryBlock_compl_pair h hn hnq hij)

theorem perfectCore_centralizer_stdTransvection (hn : 6 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ Q : Subgroup (unitaryPSU h n), IsPGroup 2 Q ∧
      perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n))) =
        Q ⊔ blockSU h ({i, j}ᶜ : Finset (Fin n)) ∧
      Q ⊓ blockSU h ({i, j}ᶜ : Finset (Fin n)) = ⊥ ∧
      blockSU h ({i, j}ᶜ : Finset (Fin n)) ≤ normalizer (Q : Set (unitaryPSU h n)) ∧
      stdTransvection h hij ∈ Q :=
  perfectCore_centralizer_stdTransvection_of_five_le h (by omega)
    (fun h' => by have := congrArg Prod.fst h'; simp only at this; omega) hij

theorem mem_perfectCore_centralizer_stdTransvection_of_five_le (hn : 5 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (5, 2)) {i j : Fin n} (hij : i ≠ j) :
    stdTransvection h hij ∈ perfectCore (centralizer {stdTransvection h hij}) := by
  obtain ⟨Q, -, hΛ, -, -, hz⟩ := perfectCore_centralizer_stdTransvection_of_five_le h hn hnq hij
  rw [hΛ]
  exact mem_sup_left hz

end CFSG.SeitzReduction.UnitaryPilot
