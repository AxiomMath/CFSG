module

public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofU4
public import CFSG.RankThree.PartTwo.Sec21.Star22

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

namespace Item223PrintProof

theorem center_eq_bot_of_isSimpleGroup_of_isPerfect {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : Group.IsPerfect Q) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    exact not_subsingleton Q
      (subsingleton_of_isPerfect_of_isSolvable hQ (Group.isSolvable_of_comm hcomm))

theorem inf_eq_bot_of_isSimpleGroup_of_isSolvable {Y : Type*} [Group Y] {K T : Subgroup Y}
    [T.Normal] (hTs : Group.IsSolvable T) [IsSimpleGroup K] (hKp : Group.IsPerfect K) :
    K ⊓ T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf K) with h | h
  · rw [inf_comm]
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  · exfalso
    have hKT : K ≤ T := Subgroup.subgroupOf_eq_top.mp h
    have hKs : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKT)
        (Subgroup.inclusion_injective hKT)
    exact not_subsingleton K (subsingleton_of_isPerfect_of_isSolvable hKp hKs)

theorem exists_mulEquiv_kOf_odd [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) {φ : MulAut A}
    (hφ : φ ∈ dStar A) :
    ∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 n)) := by
  obtain ⟨-, X, hX, hφX⟩ := id hφ
  obtain ⟨-, E', hE', U', hU', c', hXpair⟩ := hX
  have hcase := (h222 G A E' U' c' X ⟨hpair.toSec21Std, hE', hU', hXpair⟩).2.2 φ hφX hφ
  rcases hcase with ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨-, n, hn, hno, -, hKn, -⟩
  · rw [hA81] at h27
    norm_num at h27
  · rw [hA81] at h27
    norm_num at h27
  · rw [hA81] at h27
    norm_num at h27
  · rw [hA81] at h27
    norm_num at h27
  · exact ⟨n, hn, hno, hKn⟩

theorem exists_mem_inf_kOf [Finite G] {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hK : KOfWellDefined A) {φ : MulAut A} (hφ : φ ∈ dStar A) {n : ℕ}
    (eK : kOf A φ ≃* projSL 2 (GaloisField 2 n)) :
    ∃ z ∈ A, z ∈ kOf A φ ∧ orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hAF.1
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hAK := le_normalizer_kOf hAe.1 hK hφ
  obtain ⟨z, hzK, hz3, hzC⟩ := exists_orderOf_eq_mem_centralizer hA3
    (fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hAK ha) x).mp hx)
    (three_dvd_card_of_mulEquiv_projSL eK)
  exact ⟨z, mem_of_mem_centralizer_of_orderOf_eq_three' hAF hzC hz3, hzK, hz3⟩

end Item223PrintProof

open Item223PrintProof

@[expose] def Item223ThetaTrivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 →
      ∀ φ ∈ dStar A, ∀ X ∈ lStar A, kOf A φ ≤ X → ∀ m : ℕ, 1 < m →
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 m) →
          inSubgroup (aschbacherSolvableCore 3) X = ⊥

end CFSG.RankThree.PartTwo.Sec21
