module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6S898c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229c3_four_le_pRank {M Y : Subgroup G} (hY : Y ∈ calC M) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q)
    (hZ : ¬ q ∣ Nat.card (center (Bar2 Y))) {g : Fin 4 → G} (hg : ∀ i, g i ∈ M)
    (hne : ∀ i j, i ≠ j → (g j)⁻¹ * g i ∉ normalizer (Y : Set G)) :
    4 ≤ CFSG.Open.pRank q M := by
  classical
  let f : Fin 4 → MulAut G := fun i => MulAut.conj (g i)
  have hM : ∀ i, M.map (f i).toMonoidHom = M := fun i =>
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer (hg i))
  have hYi : ∀ i, Y.map (f i).toMonoidHom ∈ calC M := fun i => UC6S846.calC_map M (f i) (hM i) hY
  have hYiM : ∀ i, Y.map (f i).toMonoidHom ≤ M := fun i => (hYi i).1.le
  have hdist : ∀ i j : Fin 4, i ≠ j → Y.map (f i).toMonoidHom ≠ Y.map (f j).toMonoidHom := by
    intro i j hij heq
    have hcomp : f i = f j * MulAut.conj ((g j)⁻¹ * g i) := by
      show MulAut.conj (g i) = MulAut.conj (g j) * MulAut.conj ((g j)⁻¹ * g i)
      rw [← map_mul, mul_inv_cancel_left]
    have h1 : Y.map (f i).toMonoidHom =
        (Y.map (MulAut.conj ((g j)⁻¹ * g i)).toMonoidHom).map (f j).toMonoidHom := by
      rw [hcomp, Subgroup.map_map]
      rfl
    rw [h1] at heq
    have h2 : Y.map (MulAut.conj ((g j)⁻¹ * g i)).toMonoidHom = Y :=
      Subgroup.map_injective (f j).injective heq
    exact hne i j hij (UC6S846.mem_normalizer_iff_map_conj.2 h2)
  have hXel : IsElemAbelian q X := UC6S898.isElemAbelian_of_card_prime hq hXc
  have hEi : ∀ i, X.map (f i).toMonoidHom ≤ Y.map (f i).toMonoidHom := fun i =>
    Subgroup.map_mono hXY
  have hcalC := fun i => UC6S846.calC_subgroupOf (hYi i)
  obtain ⟨W, hWel, hWcard⟩ := UC6S898.rank_sum_of_family (Y := ↥M) (ι := Fin 4)
    (A := fun i => (Y.map (f i).toMonoidHom).subgroupOf M)
    (E := fun i => (X.map (f i).toMonoidHom).subgroupOf M) (q := q) (a := fun _ => 1) hq hq2
    (fun i => (hcalC i).1) (fun i => (hcalC i).2.1) (fun i => (hcalC i).2.2.1)
    (by
      intro i j hij
      by_contra hne'
      have hmap := congrArg (Subgroup.map M.subtype) hij
      rw [Subgroup.map_subgroupOf_eq_of_le (hYiM i), Subgroup.map_subgroupOf_eq_of_le (hYiM j)]
        at hmap
      exact hdist i j hne' hmap)
    (fun i => by
      rw [(hcalC i).2.2.2, UC6S846.card_center_bar2_map]
      exact hZ)
    (fun i x hx => hEi i hx) (fun i => (hXel.map _).subgroupOf M)
    (fun i => by
      have hEM : X.map (f i).toMonoidHom ≤ M := (hEi i).trans (hYiM i)
      show Nat.card ((X.map (f i).toMonoidHom).subgroupOf M) = q ^ 1
      rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv,
        Subgroup.card_map_of_injective (f i).injective, hXc])
    Finset.univ
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin 4)), (fun _ : Fin 4 => 1) i) = 4 := by simp
  rw [hsum] at hWcard
  exact UC6S846.le_pRank' hq (E := W.map M.subtype) (H := M) (Subgroup.map_subtype_le W)
    (hWel.map _) (by rw [Subgroup.card_map_of_injective M.subtype_injective, hWcard])

theorem uc22ine229c3_index_le_three {M Y : Subgroup G} (hY : Y ∈ calC M) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q)
    (hZ : ¬ q ∣ Nat.card (center (Bar2 Y))) (hrank : CFSG.Open.pRank q M ≤ 3) {E : Subgroup G}
    (hEM : E ≤ M) : ((normalizer (Y : Set G)).subgroupOf E).index ≤ 3 := by
  classical
  by_contra hlt
  push Not at hlt
  set N : Subgroup E := (normalizer (Y : Set G)).subgroupOf E with hN
  letI : Fintype (↥E ⧸ N) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card (↥E ⧸ N) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hlt
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard
  have h4 := uc22ine229c3_four_le_pRank hY hq hq2 hXY hXc hZ
    (g := fun i => (((φ i).out : E) : G)) (fun i => hEM ((φ i).out).2) (by
      intro i j hij hmem
      have h2 := QuotientGroup.eq.2 (show ((φ j).out)⁻¹ * (φ i).out ∈ N from hmem)
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
      exact hij (φ.injective h2).symm)
  omega

theorem uc22ine229c3_card_le_mul {M Y : Subgroup G} (hY : Y ∈ calC M) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q)
    (hZ : ¬ q ∣ Nat.card (center (Bar2 Y))) (hrank : CFSG.Open.pRank q M ≤ 3) {E : Subgroup G}
    (hEM : E ≤ M) : Nat.card E ≤ 3 * Nat.card ↥(E ⊓ normalizer (Y : Set G)) := by
  have hi := uc22ine229c3_index_le_three hY hq hq2 hXY hXc hZ hrank hEM
  have hm : Nat.card ((normalizer (Y : Set G)).subgroupOf E) *
      ((normalizer (Y : Set G)).subgroupOf E).index = Nat.card E := Subgroup.card_mul_index _
  have hc : Nat.card ((normalizer (Y : Set G)).subgroupOf E) =
      Nat.card ↥(E ⊓ normalizer (Y : Set G)) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective E.subtype_injective]
  rw [hc] at hm
  calc Nat.card E = Nat.card ↥(E ⊓ normalizer (Y : Set G)) *
        ((normalizer (Y : Set G)).subgroupOf E).index := hm.symm
    _ ≤ Nat.card ↥(E ⊓ normalizer (Y : Set G)) * 3 := Nat.mul_le_mul_left _ hi
    _ = 3 * Nat.card ↥(E ⊓ normalizer (Y : Set G)) := mul_comm _ _

theorem uc22ine229c3_card_inf_normalizer {M Y : Subgroup G} (hY : Y ∈ calC M) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q)
    (hZ : ¬ q ∣ Nat.card (center (Bar2 Y))) (hrank : CFSG.Open.pRank q M ≤ 3) {E : Subgroup G}
    (hEM : E ≤ M) (hEc : Nat.card E = 3 ^ 4) :
    27 ≤ Nat.card ↥(E ⊓ normalizer (Y : Set G)) := by
  have h := uc22ine229c3_card_le_mul hY hq hq2 hXY hXc hZ hrank hEM
  rw [hEc] at h
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
