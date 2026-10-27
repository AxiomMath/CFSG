module

public import CFSG.Quasithin.H13.NQCatJ4Local
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Quasithin.H13.NQCat.Native CFSG.SectionRank CFSG.SectionRank.LocalWitness
open scoped commutatorElement

theorem mem_closure_pair_left {G : Type*} [Group G] (x y : G) :
    x ∈ Subgroup.closure ({x, y} : Set G) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem mem_closure_pair_right {G : Type*} [Group G] (x y : G) :
    y ∈ Subgroup.closure ({x, y} : Set G) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

structure ElevenData {G : Type*} [Group G] (x y : G) : Prop where
  hx : x ^ 11 = 1
  hy : y ^ 11 = 1
  hzx : Commute ⁅x, y⁆ x
  hzy : Commute ⁅x, y⁆ y
  hxy : ∀ i < 11, ∀ j < 11, (x ^ i * y ^ j) ^ 11 = 1
  hz : ⁅x, y⁆ ≠ 1

namespace ElevenData

variable {G : Type*} [Group G] {x y : G} (D : ElevenData x y)
include D

theorem z_pow : ⁅x, y⁆ ^ 11 = 1 := by
  rw [commutator_pow_eq D.hzx, D.hx, commutatorElement_one_left]

omit D in
theorem z_mem : ⁅x, y⁆ ∈ Subgroup.closure ({x, y} : Set G) := by
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_closure_pair_left x y)
    (mem_closure_pair_right x y)) (Subgroup.inv_mem _ (mem_closure_pair_left x y)))
    (Subgroup.inv_mem _ (mem_closure_pair_right x y))

omit D in
theorem word_mem (i j k : ℕ) : x ^ i * y ^ j * ⁅x, y⁆ ^ k ∈ Subgroup.closure ({x, y} : Set G) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (mem_closure_pair_left x y) i)
    (Subgroup.pow_mem _ (mem_closure_pair_right x y) j)) (Subgroup.pow_mem _ z_mem k)

theorem exists_word {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ i j k : ℕ, i < 11 ∧ j < 11 ∧ k < 11 ∧ g = x ^ i * y ^ j * ⁅x, y⁆ ^ k :=
  mem_closure_normalForm (by norm_num) D.hx D.hy D.hzx D.hzy hg

theorem pow_eleven {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g ^ 11 = 1 := by
  obtain ⟨i, j, k, hi, hj, -, rfl⟩ := D.exists_word hg
  have hc : Commute (x ^ i * y ^ j) (⁅x, y⁆ ^ k) :=
    (((D.hzx.pow_right i).mul_right (D.hzy.pow_right j)).pow_left k).symm
  rw [hc.mul_pow, D.hxy i hi j hj, ← pow_mul, mul_comm k 11, pow_mul, D.z_pow, one_pow,
    one_mul]

omit D in
noncomputable def wordMap (x y : G) : Fin 11 × Fin 11 × Fin 11 →
    Subgroup.closure ({x, y} : Set G) :=
  fun t => ⟨x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ), word_mem _ _ _⟩

theorem wordMap_surjective : Function.Surjective (wordMap x y) := by
  rintro ⟨g, hg⟩
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := D.exists_word hg
  exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), rfl⟩

theorem isPGroup : IsPGroup 11 (Subgroup.closure ({x, y} : Set G)) := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact D.pow_eleven g.2)⟩

theorem not_isMulCommutative : ¬ IsMulCommutative (Subgroup.closure ({x, y} : Set G)) := by
  intro h
  apply D.hz
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val
    (h.is_comm.comm ⟨x, mem_closure_pair_left x y⟩ ⟨y, mem_closure_pair_right x y⟩)

theorem card_closure [Finite G] : Nat.card (Subgroup.closure ({x, y} : Set G)) = 11 ^ 3 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := D.isPGroup.exists_card_eq
  have hle : Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ 11 ^ 3 := by
    have h := Nat.card_le_card_of_surjective _ D.wordMap_surjective
    simp only [Nat.card_prod, Nat.card_fin] at h
    exact h.trans (by norm_num)
  rw [hm] at hle ⊢
  have hm3 : m ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  by_contra hne
  have hm' : m ≠ 3 := fun h => hne (by rw [h])
  apply D.not_isMulCommutative
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
  · have : Subsingleton (Subgroup.closure ({x, y} : Set G)) := by
      rw [← Finite.card_le_one_iff_subsingleton, hm, pow_zero]
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : IsCyclic (Subgroup.closure ({x, y} : Set G)) :=
      isCyclic_of_prime_card (hm.trans (pow_one 11))
    exact IsCyclic.isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hm

theorem wordMap_bijective [Finite G] : Function.Bijective (wordMap x y) :=
  D.wordMap_surjective.bijective_of_nat_card_le (by
    rw [D.card_closure]
    simp only [Nat.card_prod, Nat.card_fin]
    norm_num)

theorem word_injective [Finite G] {i j k i' j' k' : ℕ} (hi : i < 11) (hj : j < 11) (hk : k < 11)
    (hi' : i' < 11) (hj' : j' < 11) (hk' : k' < 11)
    (h : x ^ i * y ^ j * ⁅x, y⁆ ^ k = x ^ i' * y ^ j' * ⁅x, y⁆ ^ k') :
    i = i' ∧ j = j' ∧ k = k' := by
  have := D.wordMap_bijective.1 (a₁ := (⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩))
    (a₂ := (⟨i', hi'⟩, ⟨j', hj'⟩, ⟨k', hk'⟩)) (Subtype.ext h)
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  exact this

theorem pow_eleven' (g : Subgroup.closure ({x, y} : Set G)) : g ^ 11 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact D.pow_eleven g.2)

theorem isExtraspecial [Finite G] :
    IsExtraspecialPGroup 11 (Subgroup.closure ({x, y} : Set G)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three D.isPGroup
    D.pow_eleven' D.card_closure D.not_isMulCommutative

theorem exponent_eq : Monoid.exponent (Subgroup.closure ({x, y} : Set G)) = 11 := by
  have hdvd : Monoid.exponent (Subgroup.closure ({x, y} : Set G)) ∣ 11 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one D.pow_eleven'
  rcases (Nat.prime_def.1 (by norm_num : Nat.Prime 11)).2 _ hdvd with h | h
  · exfalso
    apply D.hz
    have h1 := Monoid.pow_exponent_eq_one (⟨⁅x, y⁆, z_mem⟩ : Subgroup.closure ({x, y} : Set G))
    rw [h, pow_one] at h1
    exact congrArg Subtype.val h1
  · exact h

theorem orderOf_z : orderOf ⁅x, y⁆ = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime D.z_pow D.hz

theorem center_eq [Finite G] :
    (Subgroup.center (Subgroup.closure ({x, y} : Set G))).map
      (Subgroup.closure ({x, y} : Set G)).subtype = Subgroup.zpowers ⁅x, y⁆ := by
  have hZ := D.isExtraspecial.2.2.2
  have hz : (⟨⁅x, y⁆, z_mem⟩ : Subgroup.closure ({x, y} : Set G)) ∈
      Subgroup.center (Subgroup.closure ({x, y} : Set G)) := by
    rw [← D.isExtraspecial.2.1]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨x, mem_closure_pair_left x y⟩ : Subgroup.closure ({x, y} : Set G)))
      (Subgroup.mem_top (⟨y, mem_closure_pair_right x y⟩ : Subgroup.closure ({x, y} : Set G)))
  have hle : Subgroup.zpowers ⁅x, y⁆ ≤ (Subgroup.center (Subgroup.closure ({x, y} : Set G))).map
      (Subgroup.closure ({x, y} : Set G)).subtype := by
    rw [Subgroup.zpowers_le]
    exact ⟨_, hz, rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, D.orderOf_z, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    hZ]

theorem mem_zpowers_iff [Finite G] {i j k : ℕ} (hi : i < 11) (hj : j < 11) (hk : k < 11) :
    x ^ i * y ^ j * ⁅x, y⁆ ^ k ∈ Subgroup.zpowers ⁅x, y⁆ ↔ i = 0 ∧ j = 0 := by
  classical
  constructor
  · intro h
    rw [mem_zpowers_iff_mem_range_orderOf, D.orderOf_z, Finset.mem_image] at h
    obtain ⟨m, hm, hme⟩ := h
    rw [Finset.mem_range] at hm
    have e : x ^ i * y ^ j * ⁅x, y⁆ ^ k = x ^ 0 * y ^ 0 * ⁅x, y⁆ ^ m := by
      rw [← hme, pow_zero, pow_zero, one_mul, one_mul]
    have := D.word_injective hi hj hk (by norm_num) (by norm_num) hm e
    exact ⟨this.1, this.2.1⟩
  · rintro ⟨rfl, rfl⟩
    rw [pow_zero, pow_zero, one_mul, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end ElevenData

theorem j4Data :
    ElevenData j4x j4y :=
  ⟨j4x_pow, j4y_pow, j4z_comm_x, j4z_comm_y, fun _ hi _ hj => j4xy_pow hi hj, j4z_ne_one⟩

noncomputable abbrev j4Q
    : Subgroup Sporadic.J4.J := Subgroup.closure {j4x, j4y}

theorem fixDim_of_mem_j4Q
    {u : Sporadic.J4.J} (hu : u ∈ j4Q) (hu1 : u ≠ 1) :
    (u ∈ Subgroup.zpowers j4z → fixDim u = 2) ∧ (u ∉ Subgroup.zpowers j4z → fixDim u = 12) := by
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := j4Data.exists_word hu
  constructor
  · intro hz
    obtain ⟨rfl, rfl⟩ := (j4Data.mem_zpowers_iff hi hj hk).1 hz
    rw [pow_zero, pow_zero, one_mul, one_mul] at hu1 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hu1 (pow_zero _)
    exact fixDim_z_pow hk hk0
  · intro hz
    exact fixDim_word (fixDimOK_noncentral hi hj hk (fun h => hz
      ((j4Data.mem_zpowers_iff hi hj hk).2 h)))

end CFSG.Quasithin.H13.NQCat
