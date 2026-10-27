module

public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2DefiningCore

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

theorem commuting_SL2_odd_field_actual_central_cover_local_rank {X : Type*} [Group X] [Finite X]
    (Y : Subgroup X) {H : Type*} [Group H] {p f m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (_hf : 1 ≤ f) (hm : 1 ≤ m) {k : Type*} [Field k] [Fintype k] (hk : Fintype.card k = p ^ f)
    (hk3 : 3 < p ^ f) (hk9 : p ^ f ≠ 9) (η : Y →* H) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center Y) (ι : Fin m → SL(2, k) →* H)
    (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, k), ι i A * ι j B = ι j B * ι i A) :
    ∃ u : X, u ∈ Y ∧ orderOf u = 2 ∧ ∃ V : Subgroup X, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ (m * f) ∧ m * f ≤ localRank p X := by
  have hsum : ∑ _i : Fin m, f = m * f := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have := commuting_SL2_defining_witness Y hη hker hp hp2 hm (K := fun _ => k) (fun _ => f)
    (fun _ => hk) (fun _ => hk3) (fun _ => hk9) ι hι hcomm
  rwa [hsum] at this

end CFSG.RankThree.CentralCover
