module

public import CFSG.Monster.B.E6.StdF4Points
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

abbrev orbSize
    (p q : GStar) : ℕ := (conjOrbit (Subgroup.centralizer {p}) q).ncard

theorem conj_mem_rootClassStar
    {q : GStar} (hq : q ∈ rootClassStar) (γ : GStar) :
    γ * q * γ⁻¹ ∈ rootClassStar :=
  IsConj.trans hq (isConj_iff.2 ⟨γ, rfl⟩)

theorem mul_self_of_mem_rootClassStar
    {p : GStar} (hp : p ∈ rootClassStar) : p * p = 1 := by
  obtain ⟨γ, rfl⟩ := isConj_iff.1 hp
  have h : rootStar * rootStar = 1 := by
    rw [rootStar, ← map_mul, rootInv_mul_self, map_one]
  calc γ * rootStar * γ⁻¹ * (γ * rootStar * γ⁻¹) = γ * (rootStar * rootStar) * γ⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem mem_conjOrbit_of_mem_rootClassStar
    {p q y : GStar} (hq : q ∈ rootClassStar)
    (hy : y ∈ conjOrbit (Subgroup.centralizer {p}) q) : y ∈ rootClassStar := by
  obtain ⟨c, -, rfl⟩ := hy
  exact conj_mem_rootClassStar hq c

theorem exists_orbSize_eq
    {p q : GStar} (hp : p ∈ rootClassStar) (hq : q ∈ rootClassStar) :
    ∃ i : Fin 5, orbSize p q = repSize i ∧ orderOf (p * q) = repOrder i := by
  obtain ⟨r, -, hcov, hsize, hord⟩ := fiveOrbits_of_mem_rootClassStar hp
  obtain ⟨i, hi⟩ := hcov q hq
  exact ⟨i, by rw [orbSize, conjOrbit_eq_of_mem hi, hsize i], hord i q hi⟩

theorem mem_conjOrbit_of_orbSize_eq
    {p q q' : GStar} (hp : p ∈ rootClassStar)
    (hq : q ∈ rootClassStar) (hq' : q' ∈ rootClassStar) (h : orbSize p q = orbSize p q') :
    q' ∈ conjOrbit (Subgroup.centralizer {p}) q := by
  obtain ⟨r, -, hcov, hsize, -⟩ := fiveOrbits_of_mem_rootClassStar hp
  obtain ⟨i, hi⟩ := hcov q hq
  obtain ⟨j, hj⟩ := hcov q' hq'
  have hij : i = j := by
    apply repSize_injective
    rw [← hsize i, ← hsize j, ← conjOrbit_eq_of_mem hi, ← conjOrbit_eq_of_mem hj]
    exact h
  rw [conjOrbit_eq_of_mem hi, hij]
  exact hj

theorem orbSize_conj
    (γ p q : GStar) : orbSize (γ * p * γ⁻¹) (γ * q * γ⁻¹) = orbSize p q := by
  rw [orbSize, conjOrbit_centralizer_conj, Set.ncard_image_of_injective]
  intro a b e
  simpa using e

theorem exists_conj_pair_of_orbSize_eq
    {p q p' q' : GStar} (hp : p ∈ rootClassStar)
    (hq : q ∈ rootClassStar) (hp' : p' ∈ rootClassStar) (hq' : q' ∈ rootClassStar)
    (h : orbSize p q = orbSize p' q') :
    ∃ γ : GStar, γ * p * γ⁻¹ = p' ∧ γ * q * γ⁻¹ = q' := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ((isConj_comm.1 hp).trans hp')
  have h1 : orbSize p' (g * q * g⁻¹) = orbSize p' q' :=
    calc orbSize p' (g * q * g⁻¹) = orbSize (g * p * g⁻¹) (g * q * g⁻¹) := by rw [hg]
      _ = orbSize p q := orbSize_conj g p q
      _ = orbSize p' q' := h
  obtain ⟨c, hc, hcq⟩ := mem_conjOrbit_of_orbSize_eq hp' (conj_mem_rootClassStar hq g) hq' h1
  have hcp : c * p' = p' * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  refine ⟨c * g, ?_, ?_⟩
  · calc c * g * p * (c * g)⁻¹ = c * (g * p * g⁻¹) * c⁻¹ := by group
      _ = p' := by rw [hg, hcp, mul_inv_cancel_right]
  · rw [← hcq]
    group

theorem orderOf_le_two_of_commute
    {p q : GStar} (hp : p * p = 1) (hq : q * q = 1)
    (h : Commute p q) : orderOf (p * q) ∣ 2 :=
  orderOf_dvd_of_pow_eq_one ((commute_iff_sq_eq_one hp hq).1 h)

theorem commute_iff_orbSize
    {p q : GStar} (hp : p ∈ rootClassStar) (hq : q ∈ rootClassStar) :
    (Commute p q ∧ p ≠ q) ↔ (orbSize p q = 1782 ∨ orbSize p q = 44352) := by
  obtain ⟨i, hs, ho⟩ := exists_orbSize_eq hp hq
  have hp2 := mul_self_of_mem_rootClassStar hp
  have hq2 := mul_self_of_mem_rootClassStar hq
  rw [hs, commute_iff_sq_eq_one hp2 hq2, ← orderOf_dvd_iff_pow_eq_one, ho]
  have hne : p ≠ q ↔ orderOf (p * q) ≠ 1 := by
    rw [ne_eq, ne_eq, orderOf_eq_one_iff, mul_eq_one_iff_eq_inv,
      inv_eq_of_mul_eq_one_right hq2]
  rw [hne, ho]
  fin_cases i <;> decide

theorem not_commute_iff_orbSize
    {p q : GStar} (hp : p ∈ rootClassStar) (hq : q ∈ rootClassStar) :
    ¬Commute p q ↔ (orbSize p q = 1824768 ∨ orbSize p q = 2097152) := by
  obtain ⟨i, hs, ho⟩ := exists_orbSize_eq hp hq
  rw [hs, commute_iff_sq_eq_one (mul_self_of_mem_rootClassStar hp)
    (mul_self_of_mem_rootClassStar hq), ← orderOf_dvd_iff_pow_eq_one, ho]
  fin_cases i <;> decide

theorem orderOf_eq_three_iff
    {p q : GStar} (hp : p ∈ rootClassStar) (hq : q ∈ rootClassStar) :
    orderOf (p * q) = 3 ↔ orbSize p q = 2097152 := by
  obtain ⟨i, hs, ho⟩ := exists_orbSize_eq hp hq
  rw [hs, ho]
  fin_cases i <;> decide

theorem orderOf_eq_four_iff
    {p q : GStar} (hp : p ∈ rootClassStar) (hq : q ∈ rootClassStar) :
    orderOf (p * q) = 4 ↔ orbSize p q = 1824768 := by
  obtain ⟨i, hs, ho⟩ := exists_orbSize_eq hp hq
  rw [hs, ho]
  fin_cases i <;> decide

theorem ncard_setOf_orbSize_eq
    {p : GStar} (hp : p ∈ rootClassStar) (i : Fin 5) :
    {q | q ∈ rootClassStar ∧ orbSize p q = repSize i}.ncard = repSize i := by
  obtain ⟨r, hr, hcov, hsize, -⟩ := fiveOrbits_of_mem_rootClassStar hp
  have e : {q | q ∈ rootClassStar ∧ orbSize p q = repSize i} =
      conjOrbit (Subgroup.centralizer {p}) (r i) := by
    ext q
    constructor
    · rintro ⟨hq, hqs⟩
      have h1 : orbSize p (r i) = orbSize p q := by
        rw [hqs, orbSize, hsize i]
      exact mem_conjOrbit_of_orbSize_eq hp (hr i) hq h1
    · intro hq
      refine ⟨mem_conjOrbit_of_mem_rootClassStar (hr i) hq, ?_⟩
      rw [orbSize, conjOrbit_eq_of_mem hq, hsize i]
  rw [e, hsize i]

theorem exists_orbSize_eq_repSize
    {p : GStar} (hp : p ∈ rootClassStar) (i : Fin 5) :
    ∃ q ∈ rootClassStar, orbSize p q = repSize i := by
  obtain ⟨r, hr, -, hsize, -⟩ := fiveOrbits_of_mem_rootClassStar hp
  exact ⟨r i, hr i, hsize i⟩

end CFSG.Monster.B.TwoA.Amalgam
