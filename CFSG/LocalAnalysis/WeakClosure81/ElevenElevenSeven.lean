module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenPair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem card_add_mul_le_of_inf_eq {ι : Type*} [Finite ι] {B Q : Subgroup G} {K : ι → Subgroup G}
    {b k : ℕ} (hB : Nat.card B = b) (hK : ∀ i, Nat.card (K i) = k) (hBQ : B ≤ Q)
    (hBK : ∀ i, B ≤ K i) (hKQ : ∀ i, K i ≤ Q) (hinf : ∀ i j, i ≠ j → K i ⊓ K j = B) :
    b + Nat.card ι * (k - b) ≤ Nat.card Q := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype G := Fintype.ofFinite G
  let F : Subgroup G → Finset G := fun H => Finset.univ.filter (fun g => g ∈ H)
  have hF : ∀ H : Subgroup G, (F H).card = Nat.card H := by
    intro H
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let S : ι → Finset G := fun i => F (K i) \ F B
  have hFle : ∀ {H H' : Subgroup G}, H ≤ H' → F H ⊆ F H' := by
    intro H H' h g hg
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact h hg
  have hScard : ∀ i, (S i).card = k - b := by
    intro i
    rw [Finset.card_sdiff_of_subset (hFle (hBK i)), hF, hF, hB, hK]
  have hSdisj : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      Disjoint (S i) (S j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro g hgi hgj
    simp only [S, F, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hgi hgj
    have : g ∈ K i ⊓ K j := ⟨hgi.1, hgj.1⟩
    rw [hinf i j hij] at this
    exact hgi.2 this
  have hdisj : Disjoint (F B) (Finset.univ.biUnion S) := by
    rw [Finset.disjoint_left]
    intro g hgB hg
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.1 hg
    exact (Finset.mem_sdiff.1 hgi).2 hgB
  have hsub : F B ∪ Finset.univ.biUnion S ⊆ F Q := by
    intro g hg
    rcases Finset.mem_union.1 hg with h | h
    · exact hFle hBQ h
    · obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.1 h
      exact hFle (hKQ i) (Finset.mem_sdiff.1 hgi).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_biUnion hSdisj, hF, hF] at hcard
  simp only [hScard, Finset.sum_const, Finset.card_univ, smul_eq_mul, hB] at hcard
  rw [Nat.card_eq_fintype_card (α := ι)]
  exact hcard

theorem eleven11_exists_family {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) :
    ∃ A L' X' : Fin 7 → Subgroup G,
      (∀ i, ∃ hd' : Eleven11Data M V Q (A i) (L' i) (X' i),
        Nat.card (autI hd'.setting.isElemAbelian (X' i)) = 3) ∧
      ∀ i j, i ≠ j → A i ≠ A j := by
  classical
  have hV := hd.setting.isElemAbelian
  have hcard : Nat.card {v : ↥V // v ≠ 1} = 7 := by
    haveI : Fintype ↥V := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, h8]
  let e : Fin 7 ≃ {v : ↥V // v ≠ 1} := (Finite.equivFinOfCardEq hcard).symm
  have hv2 : ∀ i, ((e i).1 : G) ^ 2 = 1 := fun i => hV.2 _ (e i).1.2
  have hv1 : ∀ i, ((e i).1 : G) ≠ 1 := fun i h => (e i).2 (Subtype.ext h)
  have hB : ∀ i, Subgroup.zpowers ((e i).1 : G) ≤ V := fun i => Subgroup.zpowers_le.2 (e i).1.2
  have hord : ∀ i, orderOf ((e i).1 : G) = 2 := fun i => orderOf_eq_prime (hv2 i) (hv1 i)
  have hB2 : ∀ i, Nat.card (Subgroup.zpowers ((e i).1 : G)) = 2 := fun i => by
    rw [Nat.card_zpowers, hord i]
  have key : ∀ i, ∃ L' X' : Subgroup G,
      ∃ hd' : Eleven11Data M V Q (Subgroup.zpowers ((e i).1 : G)) L' X',
        Nat.card (autI hd'.setting.isElemAbelian X') = 3 := fun i =>
    eleven11_exists_data_point hd h21 h3 h8 (hB i) (hB2 i)
  choose L' X' hd' h3' using key
  refine ⟨fun i => Subgroup.zpowers ((e i).1 : G), L', X', fun i => ⟨hd' i, h3' i⟩, ?_⟩
  intro i j hij hz
  have hmem : ((e j).1 : G) ∈ Subgroup.zpowers ((e i).1 : G) := by
    have hz' : Subgroup.zpowers ((e i).1 : G) = Subgroup.zpowers ((e j).1 : G) := hz
    rw [hz']
    exact Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h1 : ((e i).1 : G) ^ (n % 2) = ((e i).1 : G) ^ n := by
    have := zpow_mod_orderOf ((e i).1 : G) n
    rwa [hord i] at this
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · rw [h, zpow_zero, hn] at h1
    exact hv1 j h1.symm
  · rw [h, zpow_one, hn] at h1
    exact hij (e.injective (Subtype.ext (Subtype.ext h1)))

end CFSG.LocalAnalysis.WeakClosure81
