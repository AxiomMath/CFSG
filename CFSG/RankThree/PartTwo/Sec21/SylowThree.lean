module

public import CFSG.RankThree.PartTwo.Sec21.PairExistence
import CFSG.Quasithin.Background.BlueprintB2Thompson

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG

variable {G : Type} [Group G]

theorem mem_normalizer_elemThompson [Finite G] {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer (((CFSG.elemThompson ↥P 3).map P.subtype : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar := CFSG.Quasithin.BlueprintB2.elemThompson_characteristic (↥P) 3
  let φ : ↥P ≃* ↥P := ((MulAut.conj g).subgroupMap P).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer hg))
  have hJ : (CFSG.elemThompson ↥P 3).map φ.toMonoidHom = CFSG.elemThompson ↥P 3 :=
    (Subgroup.characteristic_iff_map_eq.mp hchar) φ
  apply mem_normalizer_of_map_conj_eq
  conv_rhs => rw [← hJ]
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem rank3II_23_2_four [Finite G] {A N : Subgroup G} (P : Sylow 3 N)
    (h2 : (CFSG.elemThompson ↥((P : Subgroup N).map N.subtype) 3).map
      ((P : Subgroup N).map N.subtype).subtype = A)
    (h3 : Subgroup.normalizer (A : Set G) ≤ N) :
    ∃ S : Sylow 3 G, (S : Subgroup G) = (P : Subgroup N).map N.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P' := (P : Subgroup N).map N.subtype with hP'def
  have hP' : IsPGroup 3 P' := P.isPGroup'.map N.subtype
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hS⟩
  by_contra hSP
  have hlt : P'.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hSP fun s hs => ?_
    have hs' : (⟨s, hs⟩ : S) ∈ P'.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hs'
  have hnil : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  obtain ⟨x, hxN, hxP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hxNG : (x : G) ∈ Subgroup.normalizer (P' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : (⟨y, hS hy⟩ : S) ∈ P'.subgroupOf S := Subgroup.mem_subgroupOf.mpr hy
      have h2' := (Subgroup.mem_normalizer_iff.mp hxN ⟨y, hS hy⟩).mp h1
      exact Subgroup.mem_subgroupOf.mp h2'
    · intro hy
      have hyS : y ∈ S := by
        have h1 : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) = y := by group
        rw [← h1]
        exact S.mul_mem (S.mul_mem (S.inv_mem x.2) (hS hy)) x.2
      have h1 : x * (⟨y, hyS⟩ : S) * x⁻¹ ∈ P'.subgroupOf S := Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hxN ⟨y, hyS⟩).mpr h1)
  have hxA : (x : G) ∈ Subgroup.normalizer (A : Set G) := h2 ▸ mem_normalizer_elemThompson hxNG
  have hxNN : (x : G) ∈ N := h3 hxA
  set x' : N := ⟨x, hxNN⟩
  have hx'3 : IsPGroup 3 (Subgroup.zpowers x') := by
    obtain ⟨k, hk⟩ := S.isPGroup' x
    have hk' : x' ^ (3 ^ k) = 1 := Subtype.ext (by simpa [x'] using congrArg Subtype.val hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hx'N : x' ∈ Subgroup.normalizer ((P : Subgroup N) : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← Subgroup.mem_map_iff_mem N.subtype_injective (K := (P : Subgroup N)) (x := y),
      ← Subgroup.mem_map_iff_mem N.subtype_injective (K := (P : Subgroup N)) (x := x' * y * x'⁻¹)]
    exact Subgroup.mem_normalizer_iff.mp hxNG y
  have hsup : IsPGroup 3 ((P : Subgroup N) ⊔ Subgroup.zpowers x' : Subgroup N) :=
    P.isPGroup'.to_sup_of_normal_left' hx'3 ((Subgroup.zpowers_le).mpr hx'N)
  have heq := P.is_maximal' hsup le_sup_left
  have hx'P : x' ∈ (P : Subgroup N) := by
    rw [← heq]
    exact (le_sup_right : Subgroup.zpowers x' ≤ _) (Subgroup.mem_zpowers x')
  exact hxP (Subgroup.mem_subgroupOf.mpr ⟨x', hx'P, rfl⟩)

end CFSG.RankThree.PartTwo.Sec21
