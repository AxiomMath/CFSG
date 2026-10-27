module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.RankThree.Asc83Table.E9

public section

namespace CFSG.RankThree.PartTwo.KFacts

open Equiv Subgroup CFSG.RankThree.PartTwo.Sec4

abbrev S3A4 : Type := Perm (Fin 3) × alternatingGroup (Fin 4)

def s3Cyc : Perm (Fin 3) := List.formPerm [0, 1, 2]

def a4Cyc : alternatingGroup (Fin 4) :=
  ⟨List.formPerm [0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

def s3a4X : S3A4 := (s3Cyc, 1)

def s3a4Y : S3A4 := (1, a4Cyc)

def s3a4E : Subgroup S3A4 := Subgroup.closure {s3a4X, s3a4Y}

theorem eq_of_mem_zpowers_of_pow_three {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk : x ^ k = x ^ (k % 3) := by
    have e : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
    conv_lhs => rw [e]
    rw [zpow_add, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hx, one_zpow,
      one_mul]
  rw [hk]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left; exact zpow_zero x
  · right; left; exact zpow_one x
  · right; right; exact zpow_natCast x 2

theorem s3a4X_pow_three : s3a4X ^ 3 = 1 := by decide

theorem s3a4Y_pow_three : s3a4Y ^ 3 = 1 := by decide

theorem s3a4X_mul_s3a4Y : s3a4X * s3a4Y = s3a4Y * s3a4X := by decide

theorem s3a4X_ne_one : s3a4X ≠ 1 := by decide

theorem s3a4Y_not_mem_zpowers : s3a4Y ∉ Subgroup.zpowers s3a4X := by
  intro h
  rcases eq_of_mem_zpowers_of_pow_three s3a4X_pow_three h with h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem card_s3a4E : Nat.card s3a4E = 9 :=
  Asc83Table.card_closure_pair_eq_nine s3a4X_pow_three s3a4Y_pow_three s3a4X_mul_s3a4Y
    s3a4X_ne_one s3a4Y_not_mem_zpowers

theorem s3a4X_mem : s3a4X ∈ s3a4E := Subgroup.subset_closure (Set.mem_insert _ _)

theorem s3a4Y_mem : s3a4Y ∈ s3a4E :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem s3_commute_cases : ∀ s : Perm (Fin 3), s * s3Cyc = s3Cyc * s →
    s = 1 ∨ s = s3Cyc ∨ s = s3Cyc * s3Cyc := by decide

theorem a4_commute_cases : ∀ a : alternatingGroup (Fin 4), a * a4Cyc = a4Cyc * a →
    a = 1 ∨ a = a4Cyc ∨ a = a4Cyc * a4Cyc := by decide

theorem centralizer_s3a4E_le : Subgroup.centralizer (s3a4E : Set S3A4) ≤ s3a4E := by
  intro g hg
  obtain ⟨s, a⟩ := g
  have hx : s3a4X * (s, a) = (s, a) * s3a4X :=
    Subgroup.mem_centralizer_iff.mp hg s3a4X s3a4X_mem
  have hy : s3a4Y * (s, a) = (s, a) * s3a4Y :=
    Subgroup.mem_centralizer_iff.mp hg s3a4Y s3a4Y_mem
  have h1 : s * s3Cyc = s3Cyc * s := (congrArg Prod.fst hx).symm
  have h2 : a * a4Cyc = a4Cyc * a := (congrArg Prod.snd hy).symm
  have hxx : s3a4X * s3a4X ∈ s3a4E := s3a4E.mul_mem s3a4X_mem s3a4X_mem
  have hxy : s3a4X * s3a4Y ∈ s3a4E := s3a4E.mul_mem s3a4X_mem s3a4Y_mem
  have hyy : s3a4Y * s3a4Y ∈ s3a4E := s3a4E.mul_mem s3a4Y_mem s3a4Y_mem
  have hxxy : s3a4X * s3a4X * s3a4Y ∈ s3a4E := s3a4E.mul_mem hxx s3a4Y_mem
  have hxyy : s3a4X * (s3a4Y * s3a4Y) ∈ s3a4E := s3a4E.mul_mem s3a4X_mem hyy
  have hxxyy : s3a4X * s3a4X * (s3a4Y * s3a4Y) ∈ s3a4E := s3a4E.mul_mem hxx hyy
  rcases s3_commute_cases s h1 with rfl | rfl | rfl <;>
    rcases a4_commute_cases a h2 with rfl | rfl | rfl
  · exact s3a4E.one_mem
  · exact s3a4Y_mem
  · exact hyy
  · exact s3a4X_mem
  · exact hxy
  · exact hxyy
  · exact hxx
  · exact hxxy
  · exact hxxyy

theorem centralizer_le_of_card_nine (S : Subgroup S3A4) (hS : Nat.card S = 9) :
    Subgroup.centralizer (S : Set S3A4) ≤ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card S3A4 = 72 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hE : Nat.card s3a4E = 3 ^ (Nat.card S3A4).factorization 3 := by
    rw [hcard, show (72 : ℕ) = 3 ^ 2 * 8 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 2 (by norm_num), card_s3a4E]
    norm_num
  have hSp : IsPGroup 3 S := IsPGroup.of_card (n := 2) (by rw [hS]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hE hSp
  have hSeq : S = s3a4E.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hg (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_s3a4E, hS])
  intro y hy
  have hy' : g⁻¹ * y * g ∈ s3a4E := by
    apply centralizer_s3a4E_le
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hmem : g * e * g⁻¹ ∈ S := by
      rw [hSeq]
      exact ⟨e, he, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hy _ hmem
    calc e * (g⁻¹ * y * g) = g⁻¹ * ((g * e * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * e * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * y * g * e := by group
  rw [hSeq]
  refine ⟨g⁻¹ * y * g, hy', ?_⟩
  change g * (g⁻¹ * y * g) * g⁻¹ = y
  group

end CFSG.RankThree.PartTwo.KFacts
