module

public import CFSG.RankThree.SubgroupLists.RationalElements
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.SubgroupLists.CentralThreeLift

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

theorem five_eq_zero_of_rational_five {K : Type*} [Field K] {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {s g : H ⧸ Subgroup.center H}
    (hs5 : s ^ 5 = 1) (hs1 : s ≠ 1) (hg : g * s * g⁻¹ = s ^ 2) : (5 : K) = 0 := by
  have hc5 : Nat.Coprime 5 3 := by norm_num
  obtain ⟨x, rfl, hx5⟩ := exists_lift_pow_eq_one le_rfl hZ3 hc5 s hs5
  have hx1 : x ≠ 1 := fun h => hs1 (by rw [h, QuotientGroup.mk_one])
  have hconj : IsConj x (x ^ 2) := by
    refine isConj_of_isConj_mk le_rfl hZ3 hc5 hx5 ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, hx5, one_pow]
    · rw [QuotientGroup.mk_pow]
      exact isConj_iff.mpr ⟨g, hg⟩
  have hconj' : IsConj (x : GL (Fin 3) K) ((x : GL (Fin 3) K) ^ 2) := by
    have := (MonoidHom.map_isConj H.subtype) hconj
    simpa using this
  refine five_eq_zero_of_isConj_sq (hdet x x.2) ?_ ?_ hconj'
  · rw [← Subgroup.coe_pow, hx5, Subgroup.coe_one]
  · exact fun h => hx1 (Subtype.ext h)

theorem eq_five_and_not_dvd_of_rational_five {p : ℕ} [Fact p.Prime]
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {s g : H ⧸ Subgroup.center H}
    (hs5 : s ^ 5 = 1) (hs1 : s ≠ 1) (hg : g * s * g⁻¹ = s ^ 2) :
    p = 5 ∧ ¬ 9 ∣ Nat.card (H ⧸ Subgroup.center H) := by
  have h5 := five_eq_zero_of_rational_five hdet hZ3 hs5 hs1 hg
  have hp : p = 5 := by
    have hdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h5)
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp hdvd
  subst hp
  refine ⟨rfl, fun h9 => ?_⟩
  have h1 : Nat.card (H ⧸ Subgroup.center H) ∣ Nat.card H := Subgroup.card_quotient_dvd_card _
  have h2 : Nat.card H ∣ Nat.card (GL (Fin 3) (ZMod 5)) := Subgroup.card_subgroup_dvd_card H
  have hGL : Nat.card (GL (Fin 3) (ZMod 5)) = 1488000 := by
    rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num
  have := Nat.dvd_trans h9 (Nat.dvd_trans h1 h2)
  rw [hGL] at this
  norm_num at this

@[expose] def a7Five : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

@[expose] def a7Conj : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 5 6, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

theorem a7Five_pow_five : a7Five ^ 5 = 1 := by
  apply Subtype.ext
  decide

theorem a7Five_ne_one : a7Five ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  decide

theorem a7Conj_conj : a7Conj * a7Five * a7Conj⁻¹ = a7Five ^ 2 := by
  apply Subtype.ext
  decide

theorem not_mulEquiv_alternating_seven {p : ℕ} [Fact p.Prime]
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1)
    (e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 7)) : False := by
  have hs5 : (e.symm a7Five) ^ 5 = 1 := by rw [← map_pow, a7Five_pow_five, map_one]
  have hs1 : e.symm a7Five ≠ 1 := fun h => a7Five_ne_one (e.symm.injective (by rw [h, map_one]))
  have hg : e.symm a7Conj * e.symm a7Five * (e.symm a7Conj)⁻¹ = (e.symm a7Five) ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, a7Conj_conj, map_pow]
  obtain ⟨-, h9⟩ := eq_five_and_not_dvd_of_rational_five hdet hZ3 hs5 hs1 hg
  apply h9
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

@[expose] def m11A : CFSG.Assembly.LowTwoRank.StatedM11 :=
  ⟨CFSG.Assembly.LowTwoRank.StatedCyclePerm 11 [[2, 10], [4, 11], [5, 7], [8, 9]],
    Subgroup.subset_closure (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; left; decide)⟩

@[expose] def m11B : CFSG.Assembly.LowTwoRank.StatedM11 :=
  ⟨CFSG.Assembly.LowTwoRank.StatedCyclePerm 11 [[1, 4, 3, 8], [2, 5, 6, 9]],
    Subgroup.subset_closure (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; right; decide)⟩

@[expose] def m11Five : CFSG.Assembly.LowTwoRank.StatedM11 :=
  m11A * m11B * m11A * m11B ^ 3 * m11A * m11B ^ 2

theorem m11Five_pow_five : m11Five ^ 5 = 1 := by
  apply Subtype.ext
  decide +kernel

theorem m11Five_ne_one : m11Five ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  decide +kernel

theorem m11B_conj : m11B * m11Five * m11B⁻¹ = m11Five ^ 2 := by
  apply Subtype.ext
  decide +kernel

theorem not_mulEquiv_m11 {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1)
    (e : (H ⧸ Subgroup.center H) ≃* CFSG.Assembly.LowTwoRank.StatedM11) : False := by
  have hs5 : (e.symm m11Five) ^ 5 = 1 := by rw [← map_pow, m11Five_pow_five, map_one]
  have hs1 : e.symm m11Five ≠ 1 := fun h =>
    m11Five_ne_one (e.symm.injective (by rw [h, map_one]))
  have hg : e.symm m11B * e.symm m11Five * (e.symm m11B)⁻¹ = (e.symm m11Five) ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, m11B_conj, map_pow]
  obtain ⟨-, h9⟩ := eq_five_and_not_dvd_of_rational_five hdet hZ3 hs5 hs1 hg
  apply h9
  rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.GL2Recognition.card_lowTwoRankStatedM11]
  norm_num

end CFSG.RankThree.SubgroupLists
