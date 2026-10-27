module

public import CFSG.RankThree.CentralCover.SteinbergBNCoordinateInversion
public import CFSG.RankThree.Chevalley.SteinbergBNHigherExceptionalSmallField

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven

@[expose] def IsInverterData {M : Type*} [Group M] (C : Subgroup M) (r : ℕ) (h w : Fin 4 → M)
    (z : M) : Prop :=
  (∀ i, h i ∈ C ∧ orderOf (h i) = r) ∧ (∀ i j, Commute (h i) (h j)) ∧ (∀ i, w i ∈ C) ∧
  (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
  (∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) ∧ z ∈ C ∧ orderOf z = 2 ∧ ∀ i, Commute z (h i)

@[expose] def FourRankWitness (X : Type) [Group X] [Finite X] (Y : Subgroup X) (r : ℕ) : Prop :=
  ∃ u : X, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup X, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
    IsElemAbelian r A ∧ Nat.card A = r ^ 4 ∧
    A ≤ Subgroup.normalizer (Subgroup.zpowers u : Set X) ∧
    IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set X)) ∧ 4 ≤ localRank r X

theorem fourRankWitness_of_inverterData {X : Type} [Group X] [Finite X] (Y : Subgroup X)
    {M : Type*} [Group M] {C : Subgroup M} (φ : Y →* C) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {h w : Fin 4 → M}
    {z : M} (hd : IsInverterData C r h w z) : FourRankWitness X Y r := by
  obtain ⟨hh, hcomm, hw, hinv, hfix, hz, hz2, hzh⟩ := hd
  have key := CFSG.RankThree.CentralCover.coordinate_inversion_actual_central_cover_local_rank Y φ
    hφ hker hr hr2 (m := 4) (by norm_num) (fun i => ⟨h i, (hh i).1⟩) (fun i => ⟨w i, hw i⟩)
    (fun i j => Subtype.ext (hcomm i j).eq)
    (fun i => by rw [Subgroup.orderOf_mk]; exact (hh i).2)
    (fun i => Subtype.ext (hinv i))
    (fun i j hij => Subtype.ext (hfix i j hij)) (z := ⟨z, hz⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz2) (fun i => Subtype.ext (hzh i).eq)
  obtain ⟨-, -, -, u, huY, hu, A, hA, hAab, hAcard, hAn, hloc, hrank⟩ := key
  exact ⟨u, huY, hu, A, hA, hAab, hAcard, hAn, hloc, hrank⟩

theorem four_le_twoLocalOddRank_of_fourRankWitness {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hw : FourRankWitness X Y r) :
    4 ≤ CFSG.twoLocalOddRank X := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hrank⟩ := hw
  exact CFSG.RankThree.Chevalley.four_le_twoLocalOddRank_of_four_le_localRank hr hr2 hrank

theorem four_le_localRank_of_fourRankWitness {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    {r : ℕ} (hw : FourRankWitness X Y r) : 4 ≤ localRank r X := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hrank⟩ := hw
  exact hrank

theorem fourRankPackage_of_inverterData {X : Type} [Group X] [Finite X] (Y : Subgroup X)
    {M : Type*} [Group M] {C : Subgroup M} (φ : Y →* C) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {h w : Fin 4 → M}
    {z : M} (hd : IsInverterData C r h w z) :
    FourRankWitness X Y r ∧ 4 ≤ localRank r X ∧ 4 ≤ CFSG.twoLocalOddRank X :=
  let hw := fourRankWitness_of_inverterData Y φ hφ hker hr hr2 hd
  ⟨hw, four_le_localRank_of_fourRankWitness hw,
    four_le_twoLocalOddRank_of_fourRankWitness hr hr2 hw⟩

end CFSG.RankThree.PartOne
