module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisAutAbstract
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisFrobenius
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisConjugacy

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem frobAut_pow_eq (k : ℕ) : frobAut K ^ k = minorAut K ^ (2 * k) := by
  rw [frobAut_eq_minorAut_sq, ← pow_mul]

theorem conj_mul_minorAut_pow_inj {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {g g' : antiSp K} {j j' : ℕ} (hj : j < 2 * n) (hj' : j' < 2 * n)
    (h : MulAut.conj g * minorAut K ^ j = MulAut.conj g' * minorAut K ^ j') :
    g = g' ∧ j = j' := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data hn hK
  obtain ⟨-, huniq, -⟩ := exceptionalAut_structure hn hFr hord hzp
  have key : ∀ (g : antiSp K) (j : ℕ), autCongr K (MulAut.conj g * minorAut K ^ j) =
      spInner 2 K (antiSpEquiv K g) * exceptionalAut K ^ j := by
    intro g j
    rw [map_mul, autCongr_conj, autCongr_pow, autCongr_minorAut]
  have h1 := congrArg (autCongr K) h
  rw [key, key] at h1
  have hu := (huniq (spInner 2 K (antiSpEquiv K g) * exceptionalAut K ^ j)).unique
    (y₁ := (antiSpEquiv K g, ⟨j, hj⟩)) (y₂ := (antiSpEquiv K g', ⟨j', hj'⟩)) rfl h1
  have h2 := Prod.mk.inj hu
  exact ⟨(antiSpEquiv K).injective h2.1, congrArg Fin.val h2.2⟩

theorem conj_mul_frobAut_pow_inj {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {g g' : antiSp K} {k k' : ℕ} (hk : k < n) (hk' : k' < n)
    (h : MulAut.conj g * frobAut K ^ k = MulAut.conj g' * frobAut K ^ k') :
    g = g' ∧ k = k' := by
  rw [frobAut_pow_eq, frobAut_pow_eq] at h
  obtain ⟨h1, h2⟩ := conj_mul_minorAut_pow_inj hn hK (by omega) (by omega) h
  exact ⟨h1, by omega⟩

@[expose] def Axis.swap : Axis → Axis
  | .one => .two
  | .two => .one

theorem minorAut_mem_radA1_iff (x : antiSp K) : minorAut K x ∈ radA1 K ↔ x ∈ radA2 K := by
  rw [radA1_eq_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := (minorAut K).injective hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem minorAut_mem_radA2_iff (x : antiSp K) : minorAut K x ∈ radA2 K ↔ x ∈ radA1 K := by
  have hsq : ∀ y : antiSp K, minorAut K (minorAut K y) = frobAut K y := fun y => by
    rw [frobAut_eq_minorAut_sq, pow_two, MulAut.mul_apply]
  constructor
  · intro h
    have h' : frobAut K ((frobAut K)⁻¹ (minorAut K x)) ∈ radA2 K := by
      rw [MulAut.apply_inv_self]
      exact h
    have hw := (frobAut_mem_radA2_iff _).mp h'
    have h1 : minorAut K (minorAut K ((frobAut K)⁻¹ (minorAut K x))) = minorAut K x := by
      rw [hsq, MulAut.apply_inv_self]
    have h2 : x = minorAut K ((frobAut K)⁻¹ (minorAut K x)) :=
      ((minorAut K).injective h1).symm
    rw [h2, radA1_eq_map]
    exact ⟨_, hw, rfl⟩
  · intro h
    rw [radA1_eq_map] at h
    obtain ⟨y, hy, rfl⟩ := h
    change minorAut K (minorAut K y) ∈ radA2 K
    rw [hsq]
    exact (frobAut_mem_radA2_iff y).mpr hy

theorem minorAut_mem_rootA_swap_iff (i : Axis) (x : antiSp K) :
    minorAut K x ∈ rootA K i.swap ↔ x ∈ rootA K i := by
  cases i
  · exact minorAut_mem_radA2_iff x
  · exact minorAut_mem_radA1_iff x

theorem not_autStab_odd (i : Axis) (g : antiSp K) (k : ℕ)
    (hα : MulAut.conj g * minorAut K ^ (2 * k + 1) ∈ autStab (rootA K i)) : False := by
  set α := MulAut.conj g * minorAut K ^ (2 * k + 1) with hαdef
  have happ : ∀ x, α x = g * (frobAut K ^ k) (minorAut K x) * g⁻¹ := by
    intro x
    rw [hαdef, MulAut.mul_apply, MulAut.conj_apply, pow_succ, MulAut.mul_apply,
      ← frobAut_pow_eq]
  have hFk : ∀ (i : Axis) (x : antiSp K), (frobAut K ^ k) x ∈ rootA K i ↔ x ∈ rootA K i :=
    fun i x => frobAut_pow_mem_iff (frobAut_mem_rootA_iff i) k x
  have h1 : ∀ y ∈ rootA K i.swap, g * y * g⁻¹ ∈ rootA K i := by
    intro y hy
    have hρx : minorAut K ((minorAut K)⁻¹ ((frobAut K ^ k)⁻¹ y)) = (frobAut K ^ k)⁻¹ y := by
      rw [MulAut.apply_inv_self]
    have hy' : (frobAut K ^ k)⁻¹ y ∈ rootA K i.swap := by
      have h3 : (frobAut K ^ k) ((frobAut K ^ k)⁻¹ y) ∈ rootA K i.swap := by
        rw [MulAut.apply_inv_self]
        exact hy
      exact (hFk i.swap _).mp h3
    have hx : (minorAut K)⁻¹ ((frobAut K ^ k)⁻¹ y) ∈ rootA K i := by
      rw [← minorAut_mem_rootA_swap_iff, hρx]
      exact hy'
    have h4 := (mem_autStab.mp hα _).mpr hx
    rw [happ, hρx, MulAut.apply_inv_self] at h4
    exact h4
  have h2 : ∀ z ∈ rootA K i, ∃ y ∈ rootA K i.swap, z = g * y * g⁻¹ := by
    intro z hz
    have hxz : α (α⁻¹ z) = z := by simp
    have hx : α⁻¹ z ∈ rootA K i := (mem_autStab.mp hα _).mp (by rw [hxz]; exact hz)
    refine ⟨(frobAut K ^ k) (minorAut K (α⁻¹ z)), ?_, ?_⟩
    · exact (hFk _ _).mpr ((minorAut_mem_rootA_swap_iff i _).mpr hx)
    · rw [← happ, hxz]
  cases i
  · exact not_conj_radA2_le_radA1 g fun y hy => h1 y hy
  · refine not_conj_radA2_le_radA1 g⁻¹ fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := h2 z hz
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e]
    exact hy

theorem exists_conj_mul_frobAut_pow {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (i : Axis)
    (α : MulAut (antiSp K)) (hα : α ∈ autStab (rootA K i)) :
    ∃ g ∈ Subgroup.normalizer (rootU K i : Set (antiSp K)), ∃ k : ℕ, k < n ∧
      α = MulAut.conj g * frobAut K ^ k := by
  obtain ⟨g, j, hj, rfl⟩ := aut_eq_conj_mul_pow (by omega) hK α
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · refine ⟨g, ?_, k, by omega, by rw [frobAut_pow_eq]⟩
    have hS := even_symplectic_four_root_axis_centralizer_structure hK hn i
    rw [hS.N_eq, Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := (frobAut K ^ k).surjective y
    have h1 := mem_autStab.mp hα x
    rw [← frobAut_pow_eq, MulAut.mul_apply, MulAut.conj_apply] at h1
    change (frobAut K ^ k) x ∈ rootA K i ↔ g * (frobAut K ^ k) x * g⁻¹ ∈ rootA K i
    rw [h1, frobAut_pow_mem_iff (frobAut_mem_rootA_iff i) k x]
  · exact (not_autStab_odd i g k hα).elim

end KCRootAxis

end CFSG.RankThree.PartOne
