module

public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2Defining

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

theorem mixed_field_commuting_SL2_actual_central_cover_defining_local_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {H : Type*} [Group H] {p m : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hm : 1 ≤ m) (f : Fin m → ℕ) (hf : ∀ i, 1 ≤ f i) {K : Fin m → Type*} [∀ i, Field (K i)]
    [∀ i, Fintype (K i)] (hK : ∀ i, Fintype.card (K i) = p ^ f i) (φ : Y →* H)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (ι : ∀ i, SL(2, K i) →* H) (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ (A : SL(2, K i)) (B : SL(2, K j)),
      ι i A * ι j B = ι j B * ι i A) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ (∑ i, f i) ∧ (∑ i, f i) ≤ localRank p G :=
  commuting_SL2_defining_witness Y hφ hker hp (by omega) hm f hK
    (fun i => (three_lt_pow_and_ne_nine hp hp3 (hf i)).1)
    (fun i => (three_lt_pow_and_ne_nine hp hp3 (hf i)).2) ι hι hcomm

end CFSG.RankThree.CentralCover
