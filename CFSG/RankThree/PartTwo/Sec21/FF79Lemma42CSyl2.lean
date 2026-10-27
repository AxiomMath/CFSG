module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem exists_nor_of_ne {P Q : Subgroup G} (hQ : IsPGroup 3 Q) (hPQ : P ≤ Q) (hne : Q ≠ P) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ Nor P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm (fun x hx => ?_) hPQ)
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem eq_of_normalizer {P Q : Subgroup G} (hQ : IsPGroup 3 Q) (hPQ : P ≤ Q)
    (hN : ∀ g ∈ Q, g ∈ Nor P → g ∈ P) : Q = P := by
  by_contra hne
  obtain ⟨x, hxQ, hxP, hxN⟩ := exists_nor_of_ne hQ hPQ hne
  exact hxP (hN x hxQ hxN)

theorem isSylowOf_of_max {B C : Subgroup G} (hBC : B ≤ C) (hBp : IsPGroup 3 B)
    (hN : ∀ y ∈ C, y ∈ Nor B → (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ B) : IsSylowOf 3 B C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB' : IsPGroup 3 (B.subgroupOf C) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBC).symm
  obtain ⟨S, hS⟩ := hB'.exists_le_sylow
  have hSp : IsPGroup 3 (S : Subgroup C) := S.isPGroup'
  have hQ : IsPGroup 3 ((S : Subgroup C).map C.subtype) := hSp.map _
  have hBQ : B ≤ (S : Subgroup C).map C.subtype := fun x hx =>
    ⟨⟨x, hBC hx⟩, hS (show (⟨x, hBC hx⟩ : C) ∈ B.subgroupOf C from hx), rfl⟩
  have hQC : (S : Subgroup C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hQB : (S : Subgroup C).map C.subtype = B := by
    refine eq_of_normalizer hQ hBQ (fun g hg hgN => hN g (hQC hg) hgN ?_)
    obtain ⟨k, hk⟩ := hQ ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hSeq : B.subgroupOf C = S := by
    refine le_antisymm hS (fun s hs => ?_)
    show (s : G) ∈ B
    rw [← hQB]
    exact ⟨s, hs, rfl⟩
  refine ⟨hBC, hBp, ?_⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  have h := S.not_dvd_index
  rw [← hSeq] at h
  exact h

theorem mem_of_normalizes {B C : Subgroup G} (h : IsSylowOf 3 B C) {y : G} (hyC : y ∈ C)
    (hyN : y ∈ Nor B) {k : ℕ} (hk : y ^ 3 ^ k = 1) : y ∈ B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hBC, hBp, hcop⟩ := h
  have hp : IsPGroup 3 (B.subgroupOf C) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBC).symm
  have hidx : ¬ 3 ∣ (B.subgroupOf C).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  let Q : Sylow 3 C := hp.toSylow hidx
  let y' : C := ⟨y, hyC⟩
  have hP : IsPGroup 3 (Subgroup.zpowers y') := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (orderOf_dvd_of_pow_eq_one (show y' ^ 3 ^ k = 1 from Subtype.ext (by simpa [y'] using hk)))
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hy'N : y' ∈ Subgroup.normalizer (Q : Set C) := by
    have : y' ∈ (Subgroup.normalizer (B : Set G)).subgroupOf C := hyN
    rw [Subgroup.subgroupOf_normalizer_eq hBC] at this
    exact this
  have hmem : y' ∈ Subgroup.zpowers y' ⊓ Subgroup.normalizer (Q : Set C) :=
    ⟨Subgroup.mem_zpowers y', hy'N⟩
  rw [hP.inf_normalizer_sylow Q] at hmem
  exact hmem.2

end CFSG.RankThree.PartTwo.Sec21.FF79
