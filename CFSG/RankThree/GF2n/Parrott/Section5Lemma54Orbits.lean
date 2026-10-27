module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

def lemma54Sizes : Fin 7 → ℕ := ![1, 2, 6, 6, 8, 4, 4]

private def S (X : Finset (Fin 7)) : ℕ := ∑ j ∈ X, lemma54Sizes j

private lemma blocks_mem_iff {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i) (i j : Fin 7) :
    j ∈ blk i ↔ blk j = blk i :=
  ⟨heq i j, fun h => h ▸ hrefl j⟩

private lemma blocks_disjoint {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    {i j : Fin 7} (hij : i ∉ blk j) : Disjoint (blk i) (blk j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have h1 : blk x = blk i := (blocks_mem_iff hrefl heq i x).mp hxi
  have h2 : blk x = blk j := (blocks_mem_iff hrefl heq j x).mp hxj
  exact hij ((h1.symm.trans h2) ▸ hrefl i)

private lemma block_subset_sdiff {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    {i : Fin 7} (h0 : i ∉ blk 0) (h1 : i ∉ blk 1) :
    blk i ⊆ (Finset.univ : Finset (Fin 7)) \ (blk 0 ∪ blk 1) := by
  intro x hx
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ x, ?_⟩
  intro hxAB
  rcases Finset.mem_union.mp hxAB with hx0 | hx1
  · exact (Finset.disjoint_left.mp (blocks_disjoint hrefl heq h0)) hx hx0
  · exact (Finset.disjoint_left.mp (blocks_disjoint hrefl heq h1)) hx hx1

private lemma block_subset_of_eq {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (i : Fin 7) {A B C : Finset (Fin 7)} (hA : blk 0 = A) (hB : blk 1 = B)
    (hC : (Finset.univ : Finset (Fin 7)) \ (A ∪ B) = C)
    (h0 : i ∉ A) (h1 : i ∉ B) : blk i ⊆ C := by
  have h := block_subset_sdiff hrefl heq (i := i) (by rwa [hA]) (by rwa [hB])
  rwa [hA, hB, hC] at h

private lemma dvd_of_block_eq {blk : Fin 7 → Finset (Fin 7)}
    {i : Fin 7} {A : Finset (Fin 7)} {d : ℕ}
    (hdiv : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hA : blk 0 = A) (hd : S A * lemma54Sizes i = d) : S (blk i) ∣ d := by
  have h := hdiv i
  rwa [hA, hd] at h

set_option maxRecDepth 10000 in
private lemma AB_cases_not_four {A B : Finset (Fin 7)}
    (h0A : (0 : Fin 7) ∈ A) (h1A : (1 : Fin 7) ∉ A) (hA0 : A ≠ {0})
    (h4A : (4 : Fin 7) ∉ A)
    (hBsub : B ⊆ ({1, 4, 5, 6} : Finset (Fin 7))) (h1B : (1 : Fin 7) ∈ B)
    (hB1 : B ≠ {1}) (hAB : Disjoint A B) (hdiv : S B ∣ 2 * S A) :
    (A = {0, 2} ∧ B = {1, 4, 5}) ∨ (A = {0, 2} ∧ B = {1, 4, 6}) ∨
      (A = {0, 3} ∧ B = {1, 4, 5}) ∨ (A = {0, 3} ∧ B = {1, 4, 6}) ∨
      (A = {0, 5} ∧ B = {1, 4}) ∨ (A = {0, 6} ∧ B = {1, 4}) ∨
      (A = {0, 2, 5, 6} ∧ B = {1, 4}) ∨ (A = {0, 3, 5, 6} ∧ B = {1, 4}) := by
  have h : ∀ A B : Finset (Fin 7), (0 : Fin 7) ∈ A → (1 : Fin 7) ∉ A → A ≠ {0} →
      (4 : Fin 7) ∉ A → B ⊆ ({1, 4, 5, 6} : Finset (Fin 7)) → (1 : Fin 7) ∈ B →
      B ≠ {1} → Disjoint A B → S B ∣ 2 * S A →
      (A = {0, 2} ∧ B = {1, 4, 5}) ∨ (A = {0, 2} ∧ B = {1, 4, 6}) ∨
        (A = {0, 3} ∧ B = {1, 4, 5}) ∨ (A = {0, 3} ∧ B = {1, 4, 6}) ∨
        (A = {0, 5} ∧ B = {1, 4}) ∨ (A = {0, 6} ∧ B = {1, 4}) ∨
        (A = {0, 2, 5, 6} ∧ B = {1, 4}) ∨ (A = {0, 3, 5, 6} ∧ B = {1, 4}) := by
    decide
  exact h A B h0A h1A hA0 h4A hBsub h1B hB1 hAB hdiv

set_option maxRecDepth 10000 in
private lemma AB_cases_four {A B : Finset (Fin 7)}
    (h0A : (0 : Fin 7) ∈ A) (h1A : (1 : Fin 7) ∉ A) (hA0 : A ≠ {0})
    (h4A : (4 : Fin 7) ∈ A)
    (hBsub : B ⊆ ({1, 4, 5, 6} : Finset (Fin 7))) (h1B : (1 : Fin 7) ∈ B)
    (hB1 : B ≠ {1}) (hAB : Disjoint A B) (hdiv : S B ∣ 2 * S A) :
    (A = {0, 4} ∧ B = {1, 5}) ∨ (A = {0, 4} ∧ B = {1, 6}) ∨
      (A = {0, 2, 4} ∧ B = {1, 5}) ∨ (A = {0, 2, 4} ∧ B = {1, 6}) ∨
      (A = {0, 2, 4} ∧ B = {1, 5, 6}) ∨
      (A = {0, 3, 4} ∧ B = {1, 5}) ∨ (A = {0, 3, 4} ∧ B = {1, 6}) ∨
      (A = {0, 3, 4} ∧ B = {1, 5, 6}) ∨
      (A = {0, 2, 3, 4} ∧ B = {1, 5}) ∨ (A = {0, 2, 3, 4} ∧ B = {1, 6}) := by
  have h : ∀ A B : Finset (Fin 7), (0 : Fin 7) ∈ A → (1 : Fin 7) ∉ A → A ≠ {0} →
      (4 : Fin 7) ∈ A → B ⊆ ({1, 4, 5, 6} : Finset (Fin 7)) → (1 : Fin 7) ∈ B →
      B ≠ {1} → Disjoint A B → S B ∣ 2 * S A →
      (A = {0, 4} ∧ B = {1, 5}) ∨ (A = {0, 4} ∧ B = {1, 6}) ∨
        (A = {0, 2, 4} ∧ B = {1, 5}) ∨ (A = {0, 2, 4} ∧ B = {1, 6}) ∨
        (A = {0, 2, 4} ∧ B = {1, 5, 6}) ∨
        (A = {0, 3, 4} ∧ B = {1, 5}) ∨ (A = {0, 3, 4} ∧ B = {1, 6}) ∨
        (A = {0, 3, 4} ∧ B = {1, 5, 6}) ∨
        (A = {0, 2, 3, 4} ∧ B = {1, 5}) ∨ (A = {0, 2, 3, 4} ∧ B = {1, 6}) := by
    decide
  exact h A B h0A h1A hA0 h4A hBsub h1B hB1 hAB hdiv

private lemma block_singleton_36 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({3, 6} : Finset (Fin 7))) (h3 : (3 : Fin 7) ∈ X) (hdiv : S X ∣ 42) :
    X = {3} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({3, 6} : Finset (Fin 7)) → (3 : Fin 7) ∈ X →
      S X ∣ 42 → X = {3} := by decide
  exact h X hsub h3 hdiv

private lemma block_singleton_35 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({3, 5} : Finset (Fin 7))) (h3 : (3 : Fin 7) ∈ X) (hdiv : S X ∣ 42) :
    X = {3} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({3, 5} : Finset (Fin 7)) → (3 : Fin 7) ∈ X →
      S X ∣ 42 → X = {3} := by decide
  exact h X hsub h3 hdiv

private lemma block_singleton_26 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({2, 6} : Finset (Fin 7))) (h2 : (2 : Fin 7) ∈ X) (hdiv : S X ∣ 42) :
    X = {2} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({2, 6} : Finset (Fin 7)) → (2 : Fin 7) ∈ X →
      S X ∣ 42 → X = {2} := by decide
  exact h X hsub h2 hdiv

private lemma block_singleton_25 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({2, 5} : Finset (Fin 7))) (h2 : (2 : Fin 7) ∈ X) (hdiv : S X ∣ 42) :
    X = {2} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({2, 5} : Finset (Fin 7)) → (2 : Fin 7) ∈ X →
      S X ∣ 42 → X = {2} := by decide
  exact h X hsub h2 hdiv

private lemma block_pair_236 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({2, 3, 6} : Finset (Fin 7))) (h2 : (2 : Fin 7) ∈ X) (hdiv : S X ∣ 30) :
    X = {2} ∨ X = {2, 6} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({2, 3, 6} : Finset (Fin 7)) → (2 : Fin 7) ∈ X →
      S X ∣ 30 → X = {2} ∨ X = {2, 6} := by decide
  exact h X hsub h2 hdiv

private lemma block_pair_235 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({2, 3, 5} : Finset (Fin 7))) (h2 : (2 : Fin 7) ∈ X) (hdiv : S X ∣ 30) :
    X = {2} ∨ X = {2, 5} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({2, 3, 5} : Finset (Fin 7)) → (2 : Fin 7) ∈ X →
      S X ∣ 30 → X = {2} ∨ X = {2, 5} := by decide
  exact h X hsub h2 hdiv

private lemma block_singleton_236 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({2, 3, 6} : Finset (Fin 7))) (h2 : (2 : Fin 7) ∈ X) (hdiv : S X ∣ 54) :
    X = {2} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({2, 3, 6} : Finset (Fin 7)) → (2 : Fin 7) ∈ X →
      S X ∣ 54 → X = {2} := by decide
  exact h X hsub h2 hdiv

private lemma block_singleton_235 {X : Finset (Fin 7)}
    (hsub : X ⊆ ({2, 3, 5} : Finset (Fin 7))) (h2 : (2 : Fin 7) ∈ X) (hdiv : S X ∣ 54) :
    X = {2} := by
  have h : ∀ X : Finset (Fin 7), X ⊆ ({2, 3, 5} : Finset (Fin 7)) → (2 : Fin 7) ∈ X →
      S X ∣ 54 → X = {2} := by decide
  exact h X hsub h2 hdiv

private lemma blocks_AB_data {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (h01 : 1 ∉ blk 0) (h12 : 2 ∉ blk 1) (h13 : 3 ∉ blk 1)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i) :
    blk 1 ⊆ ({1, 4, 5, 6} : Finset (Fin 7)) ∧ Disjoint (blk 0) (blk 1) ∧
      S (blk 1) ∣ 2 * S (blk 0) := by
  have hBsub : blk 1 ⊆ ({1, 4, 5, 6} : Finset (Fin 7)) := by
    intro j hj
    have h0B : (0 : Fin 7) ∉ blk 1 := by
      intro h
      have hblk : blk 0 = blk 1 := (blocks_mem_iff hrefl heq 1 0).mp h
      exact h01 (hblk ▸ hrefl 1)
    fin_cases j <;> simp_all
  have hAB : Disjoint (blk 0) (blk 1) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    have h1 : blk x = blk 0 := (blocks_mem_iff hrefl heq 0 x).mp hx0
    have h2 : blk x = blk 1 := (blocks_mem_iff hrefl heq 1 x).mp hx1
    exact h01 ((h1.symm.trans h2) ▸ hrefl 1)
  have hdivB : S (blk 1) ∣ 2 * S (blk 0) := by
    rw [Nat.mul_comm]
    simpa [lemma54Sizes] using hdiv' 1
  exact ⟨hBsub, hAB, hdivB⟩

private lemma kill_A02_B145 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hJW : blk 2 ⊆ {0, 1, 2, 3} → blk 3 ⊆ {0, 1, 2, 3} → blk 1 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 2}) (hB : blk 1 = {1, 4, 5}) : False := by
  have hsub3 : blk 3 ⊆ ({3, 6} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide)
  have hd3 : S (blk 3) ∣ 42 := dvd_of_block_eq hdiv' hA (by decide)
  have h3eq : blk 3 = {3} := block_singleton_36 hsub3 (hrefl 3) hd3
  have h2eq : blk 2 = blk 0 := heq 0 2 (by rw [hA]; decide)
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hJW (by rw [h2eq, hA]; decide) (by rw [h3eq]; decide) (by rw [hB]; decide))

private lemma kill_A02_B146 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hJW : blk 2 ⊆ {0, 1, 2, 3} → blk 3 ⊆ {0, 1, 2, 3} → blk 1 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 2}) (hB : blk 1 = {1, 4, 6}) : False := by
  have hsub3 : blk 3 ⊆ ({3, 5} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide)
  have hd3 : S (blk 3) ∣ 42 := dvd_of_block_eq hdiv' hA (by decide)
  have h3eq : blk 3 = {3} := block_singleton_35 hsub3 (hrefl 3) hd3
  have h2eq : blk 2 = blk 0 := heq 0 2 (by rw [hA]; decide)
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hJW (by rw [h2eq, hA]; decide) (by rw [h3eq]; decide) (by rw [hB]; decide))

private lemma kill_A03_B145 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hJW : blk 2 ⊆ {0, 1, 2, 3} → blk 3 ⊆ {0, 1, 2, 3} → blk 1 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 3}) (hB : blk 1 = {1, 4, 5}) : False := by
  have hsub2 : blk 2 ⊆ ({2, 6} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide)
  have hd2 : S (blk 2) ∣ 42 := dvd_of_block_eq hdiv' hA (by decide)
  have h2eq : blk 2 = {2} := block_singleton_26 hsub2 (hrefl 2) hd2
  have h3eq : blk 3 = blk 0 := heq 0 3 (by rw [hA]; decide)
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hJW (by rw [h2eq]; decide) (by rw [h3eq, hA]; decide) (by rw [hB]; decide))

private lemma kill_A03_B146 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hJW : blk 2 ⊆ {0, 1, 2, 3} → blk 3 ⊆ {0, 1, 2, 3} → blk 1 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 3}) (hB : blk 1 = {1, 4, 6}) : False := by
  have hsub2 : blk 2 ⊆ ({2, 5} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide)
  have hd2 : S (blk 2) ∣ 42 := dvd_of_block_eq hdiv' hA (by decide)
  have h2eq : blk 2 = {2} := block_singleton_25 hsub2 (hrefl 2) hd2
  have h3eq : blk 3 = blk 0 := heq 0 3 (by rw [hA]; decide)
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hJW (by rw [h2eq]; decide) (by rw [h3eq, hA]; decide) (by rw [hB]; decide))

private lemma kill_A05_B14 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 5}) (hB : blk 1 = {1, 4}) : False := by
  have hsub2 : blk 2 ⊆ ({2, 3, 6} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide)
  have hd2 : S (blk 2) ∣ 30 := dvd_of_block_eq hdiv' hA (by decide)
  rcases block_pair_236 hsub2 (hrefl 2) hd2 with h2eq | h2eq
  · have hmem : (5 : Fin 7) ∈ ({0, 1, 2, 3} : Finset (Fin 7)) :=
      hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide)
    exact (by decide : (5 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7))) hmem
  · have h3sub : blk 3 ⊆ ({3} : Finset (Fin 7)) := by
      intro y hy
      have hyC : y ∈ ({2, 3, 6} : Finset (Fin 7)) :=
        block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide) hy
      have hy2 : y ∉ ({2, 6} : Finset (Fin 7)) := by
        intro hy2mem
        exact (Finset.disjoint_left.mp
          (blocks_disjoint hrefl heq (i := 3) (j := 2) (by rw [h2eq]; decide)))
          hy (by rwa [h2eq])
      fin_cases y <;> simp_all
    have h3eq : blk 3 = {3} :=
      Finset.Subset.antisymm h3sub (Finset.singleton_subset_iff.mpr (hrefl 3))
    exact (by decide : (5 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
      (hspan3 (by rw [h3eq]; decide) (by rw [hA]; decide))

private lemma kill_A06_B14 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 6}) (hB : blk 1 = {1, 4}) : False := by
  have hsub2 : blk 2 ⊆ ({2, 3, 5} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide)
  have hd2 : S (blk 2) ∣ 30 := dvd_of_block_eq hdiv' hA (by decide)
  rcases block_pair_235 hsub2 (hrefl 2) hd2 with h2eq | h2eq
  · have hmem : (6 : Fin 7) ∈ ({0, 1, 2, 3} : Finset (Fin 7)) :=
      hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide)
    exact (by decide : (6 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7))) hmem
  · have h3sub : blk 3 ⊆ ({3} : Finset (Fin 7)) := by
      intro y hy
      have hyC : y ∈ ({2, 3, 5} : Finset (Fin 7)) :=
        block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide) hy
      have hy2 : y ∉ ({2, 5} : Finset (Fin 7)) := by
        intro hy2mem
        exact (Finset.disjoint_left.mp
          (blocks_disjoint hrefl heq (i := 3) (j := 2) (by rw [h2eq]; decide)))
          hy (by rwa [h2eq])
      fin_cases y <;> simp_all
    have h3eq : blk 3 = {3} :=
      Finset.Subset.antisymm h3sub (Finset.singleton_subset_iff.mpr (hrefl 3))
    exact (by decide : (6 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
      (hspan3 (by rw [h3eq]; decide) (by rw [hA]; decide))

private lemma kill_A0256_B14 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 2, 5, 6}) (hB : blk 1 = {1, 4}) : False := by
  have hsub3 : blk 3 ⊆ ({3} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide)
  have h3eq : blk 3 = {3} :=
    Finset.Subset.antisymm hsub3 (Finset.singleton_subset_iff.mpr (hrefl 3))
  exact (by decide : (5 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hspan3 (by rw [h3eq]; decide) (by rw [hA]; decide))

private lemma kill_A0356_B14 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 3, 5, 6}) (hB : blk 1 = {1, 4}) : False := by
  have hsub2 : blk 2 ⊆ ({2} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide)
  have h2eq : blk 2 = {2} :=
    Finset.Subset.antisymm hsub2 (Finset.singleton_subset_iff.mpr (hrefl 2))
  exact (by decide : (5 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide))

private lemma lemma54_four_mem {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hk : blk 0 ≠ {0}) (h01 : 1 ∉ blk 0) (h12 : 2 ∉ blk 1) (h13 : 3 ∉ blk 1)
    (h11 : blk 1 ≠ {1})
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hJW : blk 2 ⊆ {0, 1, 2, 3} → blk 3 ⊆ {0, 1, 2, 3} → blk 1 ⊆ {0, 1, 2, 3}) :
    (4 : Fin 7) ∈ blk 0 := by
  obtain ⟨hBsub, hAB, hdivB⟩ := blocks_AB_data hrefl heq h01 h12 h13 hdiv'
  by_contra h4not
  rcases AB_cases_not_four (hrefl 0) h01 hk h4not hBsub (hrefl 1) h11 hAB hdivB with
    ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ |
      ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact kill_A02_B145 hrefl heq hdiv' hJW hA hB
  · exact kill_A02_B146 hrefl heq hdiv' hJW hA hB
  · exact kill_A03_B145 hrefl heq hdiv' hJW hA hB
  · exact kill_A03_B146 hrefl heq hdiv' hJW hA hB
  · exact kill_A05_B14 hrefl heq hdiv' hspan2 hspan3 hA hB
  · exact kill_A06_B14 hrefl heq hdiv' hspan2 hspan3 hA hB
  · exact kill_A0256_B14 hrefl heq hspan3 hA hB
  · exact kill_A0356_B14 hrefl heq hspan2 hA hB

private lemma kill_A04_B15 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 4}) (hB : blk 1 = {1, 5}) : False := by
  have hsub2 : blk 2 ⊆ ({2, 3, 6} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide)
  have hd2 : S (blk 2) ∣ 54 := dvd_of_block_eq hdiv' hA (by decide)
  have h2eq : blk 2 = {2} := block_singleton_236 hsub2 (hrefl 2) hd2
  have hmem : (4 : Fin 7) ∈ ({0, 1, 2, 3} : Finset (Fin 7)) :=
    hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide)
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7))) hmem

private lemma kill_A04_B16 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 4}) (hB : blk 1 = {1, 6}) : False := by
  have hsub2 : blk 2 ⊆ ({2, 3, 5} : Finset (Fin 7)) :=
    block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide)
  have hd2 : S (blk 2) ∣ 54 := dvd_of_block_eq hdiv' hA (by decide)
  have h2eq : blk 2 = {2} := block_singleton_235 hsub2 (hrefl 2) hd2
  have hmem : (4 : Fin 7) ∈ ({0, 1, 2, 3} : Finset (Fin 7)) :=
    hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide)
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7))) hmem

private lemma lemma54_two_or_three_mem {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hk : blk 0 ≠ {0}) (h01 : 1 ∉ blk 0) (h12 : 2 ∉ blk 1) (h13 : 3 ∉ blk 1)
    (h11 : blk 1 ≠ {1})
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (h4 : (4 : Fin 7) ∈ blk 0) :
    (2 : Fin 7) ∈ blk 0 ∨ (3 : Fin 7) ∈ blk 0 := by
  obtain ⟨hBsub, hAB, hdivB⟩ := blocks_AB_data hrefl heq h01 h12 h13 hdiv'
  rcases AB_cases_four (hrefl 0) h01 hk h4 hBsub (hrefl 1) h11 hAB hdivB with
    ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ |
      ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact (kill_A04_B15 hrefl heq hdiv' hspan2 hA hB).elim
  · exact (kill_A04_B16 hrefl heq hdiv' hspan2 hA hB).elim
  · left; rw [hA]; decide
  · left; rw [hA]; decide
  · left; rw [hA]; decide
  · right; rw [hA]; decide
  · right; rw [hA]; decide
  · right; rw [hA]; decide
  · left; rw [hA]; decide
  · left; rw [hA]; decide

private lemma lemma54_five_six_not_mem {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hk : blk 0 ≠ {0}) (h01 : 1 ∉ blk 0) (h12 : 2 ∉ blk 1) (h13 : 3 ∉ blk 1)
    (h11 : blk 1 ≠ {1})
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (h4 : (4 : Fin 7) ∈ blk 0) :
    (5 : Fin 7) ∉ blk 0 ∧ (6 : Fin 7) ∉ blk 0 := by
  obtain ⟨hBsub, hAB, hdivB⟩ := blocks_AB_data hrefl heq h01 h12 h13 hdiv'
  rcases AB_cases_four (hrefl 0) h01 hk h4 hBsub (hrefl 1) h11 hAB hdivB with
    ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ |
      ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  all_goals
    rw [hA]
    decide

private lemma lemma54_final {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hk : blk 0 ≠ {0}) (h01 : 1 ∉ blk 0) (h12 : 2 ∉ blk 1) (h13 : 3 ∉ blk 1)
    (h11 : blk 1 ≠ {1})
    (hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i)
    (h4 : (4 : Fin 7) ∈ blk 0)
    (h23 : (2 : Fin 7) ∈ blk 0 ∨ (3 : Fin 7) ∈ blk 0) :
    ((5 : Fin 7) ∈ blk 1 ∨ (6 : Fin 7) ∈ blk 1) ∧
      S (blk 1) ≠ 2 * S (blk 0) := by
  obtain ⟨hBsub, hAB, hdivB⟩ := blocks_AB_data hrefl heq h01 h12 h13 hdiv'
  rcases AB_cases_four (hrefl 0) h01 hk h4 hBsub (hrefl 1) h11 hAB hdivB with
    ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ |
      ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exfalso
    exact absurd h23 (by rw [hA]; decide)
  · exfalso
    exact absurd h23 (by rw [hA]; decide)
  all_goals
    rw [hA, hB]
    decide

theorem lemma54_blocks (blk : Fin 7 → Finset (Fin 7))
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hk : blk 0 ≠ {0}) (h01 : 1 ∉ blk 0) (h12 : 2 ∉ blk 1) (h13 : 3 ∉ blk 1)
    (h11 : blk 1 ≠ {1})
    (hdiv : ∀ i, (∑ j ∈ blk i, lemma54Sizes j) ∣ (∑ j ∈ blk 0, lemma54Sizes j) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hJW : blk 2 ⊆ {0, 1, 2, 3} → blk 3 ⊆ {0, 1, 2, 3} → blk 1 ⊆ {0, 1, 2, 3}) :
    4 ∈ blk 0 ∧ (2 ∈ blk 0 ∨ 3 ∈ blk 0) ∧ 5 ∉ blk 0 ∧ 6 ∉ blk 0 ∧ (5 ∈ blk 1 ∨ 6 ∈ blk 1) ∧
      ∑ j ∈ blk 1, lemma54Sizes j ≠ 2 * ∑ j ∈ blk 0, lemma54Sizes j := by
  have hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i := hdiv
  have h4 := lemma54_four_mem hrefl heq hk h01 h12 h13 h11 hdiv' hspan2 hspan3 hJW
  have h23 := lemma54_two_or_three_mem hrefl heq hk h01 h12 h13 h11 hdiv' hspan2 h4
  have h56 := lemma54_five_six_not_mem hrefl heq hk h01 h12 h13 h11 hdiv' h4
  have hlast := lemma54_final hrefl heq hk h01 h12 h13 h11 hdiv' h4 h23
  exact ⟨h4, h23, h56.1, h56.2, hlast.1, hlast.2⟩

private lemma blk_six_mem_three_of_A024_B15 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 2, 4}) (hB : blk 1 = {1, 5}) :
    (6 : Fin 7) ∈ blk 3 := by
  by_contra h6
  have hsub : blk 3 ⊆ ({3} : Finset (Fin 7)) := by
    intro x hx
    have hxC : x ∈ ({3, 6} : Finset (Fin 7)) :=
      block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide) hx
    fin_cases x <;> simp_all
  have h3eq : blk 3 = {3} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr (hrefl 3))
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hspan3 (by rw [h3eq]; decide) (by rw [hA]; decide))

private lemma blk_five_mem_three_of_A024_B16 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 2, 4}) (hB : blk 1 = {1, 6}) :
    (5 : Fin 7) ∈ blk 3 := by
  by_contra h5
  have hsub : blk 3 ⊆ ({3} : Finset (Fin 7)) := by
    intro x hx
    have hxC : x ∈ ({3, 5} : Finset (Fin 7)) :=
      block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide) hx
    fin_cases x <;> simp_all
  have h3eq : blk 3 = {3} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr (hrefl 3))
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hspan3 (by rw [h3eq]; decide) (by rw [hA]; decide))

private lemma blk_six_mem_two_of_A034_B15 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 3, 4}) (hB : blk 1 = {1, 5}) :
    (6 : Fin 7) ∈ blk 2 := by
  by_contra h6
  have hsub : blk 2 ⊆ ({2} : Finset (Fin 7)) := by
    intro x hx
    have hxC : x ∈ ({2, 6} : Finset (Fin 7)) :=
      block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide) hx
    fin_cases x <;> simp_all
  have h2eq : blk 2 = {2} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr (hrefl 2))
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide))

private lemma blk_five_mem_two_of_A034_B16 {blk : Fin 7 → Finset (Fin 7)}
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hA : blk 0 = {0, 3, 4}) (hB : blk 1 = {1, 6}) :
    (5 : Fin 7) ∈ blk 2 := by
  by_contra h5
  have hsub : blk 2 ⊆ ({2} : Finset (Fin 7)) := by
    intro x hx
    have hxC : x ∈ ({2, 5} : Finset (Fin 7)) :=
      block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide) hx
    fin_cases x <;> simp_all
  have h2eq : blk 2 = {2} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr (hrefl 2))
  exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
    (hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide))

theorem lemma54_blocks_five_six (blk : Fin 7 → Finset (Fin 7))
    (hrefl : ∀ i, i ∈ blk i) (heq : ∀ i j, j ∈ blk i → blk j = blk i)
    (hk : blk 0 ≠ {0}) (h01 : 1 ∉ blk 0) (h12 : 2 ∉ blk 1) (h13 : 3 ∉ blk 1)
    (h11 : blk 1 ≠ {1})
    (hdiv : ∀ i, (∑ j ∈ blk i, lemma54Sizes j) ∣ (∑ j ∈ blk 0, lemma54Sizes j) * lemma54Sizes i)
    (hspan2 : blk 2 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hspan3 : blk 3 ⊆ {2, 3} → blk 0 ⊆ {0, 1, 2, 3})
    (hJW : blk 2 ⊆ {0, 1, 2, 3} → blk 3 ⊆ {0, 1, 2, 3} → blk 1 ⊆ {0, 1, 2, 3})
    (h7 : ∑ j ∈ blk 0, lemma54Sizes j = 21 → 6 < ∑ j ∈ blk 1, lemma54Sizes j) :
    (5 ∈ blk 1 ∧ (6 ∈ blk 2 ∨ 6 ∈ blk 3)) ∨ (6 ∈ blk 1 ∧ (5 ∈ blk 2 ∨ 5 ∈ blk 3)) := by
  have hdiv' : ∀ i, S (blk i) ∣ S (blk 0) * lemma54Sizes i := hdiv
  have h4 := lemma54_four_mem hrefl heq hk h01 h12 h13 h11 hdiv' hspan2 hspan3 hJW
  obtain ⟨hBsub, hAB, hdivB⟩ := blocks_AB_data hrefl heq h01 h12 h13 hdiv'
  rcases AB_cases_four (hrefl 0) h01 hk h4 hBsub (hrefl 1) h11 hAB hdivB with
    ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ |
      ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact (kill_A04_B15 hrefl heq hdiv' hspan2 hA hB).elim
  · exact (kill_A04_B16 hrefl heq hdiv' hspan2 hA hB).elim
  · exact Or.inl ⟨by rw [hB]; decide,
      Or.inr (blk_six_mem_three_of_A024_B15 hrefl heq hspan3 hA hB)⟩
  · exact Or.inr ⟨by rw [hB]; decide,
      Or.inr (blk_five_mem_three_of_A024_B16 hrefl heq hspan3 hA hB)⟩
  · exfalso
    have h3eq : blk 3 = {3} := by
      refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr (hrefl 3))
      intro x hx
      have hxC : x ∈ ({3} : Finset (Fin 7)) :=
        block_subset_of_eq hrefl heq 3 hA hB (by decide) (by decide) (by decide) hx
      simpa using hxC
    exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
      (hspan3 (by rw [h3eq]; decide) (by rw [hA]; decide))
  · exact Or.inl ⟨by rw [hB]; decide,
      Or.inl (blk_six_mem_two_of_A034_B15 hrefl heq hspan2 hA hB)⟩
  · exact Or.inr ⟨by rw [hB]; decide,
      Or.inl (blk_five_mem_two_of_A034_B16 hrefl heq hspan2 hA hB)⟩
  · exfalso
    have h2eq : blk 2 = {2} := by
      refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr (hrefl 2))
      intro x hx
      have hxC : x ∈ ({2} : Finset (Fin 7)) :=
        block_subset_of_eq hrefl heq 2 hA hB (by decide) (by decide) (by decide) hx
      simpa using hxC
    exact (by decide : (4 : Fin 7) ∉ ({0, 1, 2, 3} : Finset (Fin 7)))
      (hspan2 (by rw [h2eq]; decide) (by rw [hA]; decide))
  · exfalso
    have hS0 : S (blk 0) = 21 := by rw [hA]; decide
    have hS1 : (∑ j ∈ blk 1, lemma54Sizes j) = 6 := by rw [hB]; decide
    have hgt := h7 (by simpa [S] using hS0)
    rw [hS1] at hgt
    omega
  · exfalso
    have hS0 : S (blk 0) = 21 := by rw [hA]; decide
    have hS1 : (∑ j ∈ blk 1, lemma54Sizes j) = 6 := by rw [hB]; decide
    have hgt := h7 (by simpa [S] using hS0)
    rw [hS1] at hgt
    omega

section

variable [DecidableEq G]

private noncomputable instance conjMulAction (N : Subgroup G) : MulAction N G :=
  MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)

private lemma conj_smul_def (N : Subgroup G) (n : N) (a : G) :
    n • a = (n : G) * a * (n : G)⁻¹ := rfl

private noncomputable instance fintypeSubgroup (N : Subgroup G) : Fintype N :=
  Fintype.ofFinite N

private noncomputable def conjOrbit (N : Subgroup G) (a : G) : Finset G :=
  Finset.univ.image fun n : N => (n : G) * a * (n : G)⁻¹

private lemma mem_conjOrbit {N : Subgroup G} {a b : G} :
    b ∈ conjOrbit N a ↔ ∃ n ∈ N, n * a * n⁻¹ = b := by
  classical
  rw [conjOrbit, Finset.mem_image]
  constructor
  · rintro ⟨n, -, rfl⟩
    exact ⟨n, n.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩

private lemma conjOrbit_eq_of_mem {N : Subgroup G} {a b : G} (h : b ∈ conjOrbit N a) :
    conjOrbit N b = conjOrbit N a := by
  obtain ⟨n, hnN, rfl⟩ := mem_conjOrbit.mp h
  ext c
  rw [mem_conjOrbit, mem_conjOrbit]
  constructor
  · rintro ⟨m, hmN, rfl⟩
    exact ⟨m * n, N.mul_mem hmN hnN, by group⟩
  · rintro ⟨m, hmN, rfl⟩
    exact ⟨m * n⁻¹, N.mul_mem hmN (N.inv_mem hnN), by group⟩

private noncomputable def blockOf (N : Subgroup G) (O : Fin 7 → Finset G) (i : Fin 7) :
    Finset (Fin 7) := by
  classical
  exact Finset.univ.filter fun j => ∃ b ∈ O j, ∃ n ∈ N, n * b * n⁻¹ ∈ O i

private lemma mem_blockOf {N : Subgroup G} {O : Fin 7 → Finset G} {i j : Fin 7} :
    j ∈ blockOf N O i ↔ ∃ b ∈ O j, ∃ n ∈ N, n * b * n⁻¹ ∈ O i := by
  classical
  simp [blockOf]

private lemma mem_blockOf_iff {N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    {i j : Fin 7} {a b : G} (ha : a ∈ O i) (hb : b ∈ O j) :
    j ∈ blockOf N O i ↔ b ∈ conjOrbit N a := by
  classical
  constructor
  · intro hj
    rw [mem_blockOf] at hj
    obtain ⟨b', hb'j, n, hnN, hnb'i⟩ := hj
    obtain ⟨c, hcN₀, hcb⟩ := hORB j b hb b' hb'j
    obtain ⟨d, hdN₀, hda⟩ := hORB i (n * b' * n⁻¹) hnb'i a ha
    rw [mem_conjOrbit]
    refine ⟨(d * n * c)⁻¹,
      N.inv_mem (N.mul_mem (N.mul_mem hdN₀.1 hnN) hcN₀.1), ?_⟩
    have h1 : d⁻¹ * a * d = n * b' * n⁻¹ := by rw [← hda]; group
    have h2 : c⁻¹ * b' * c = b := by rw [← hcb]; group
    have hcalc : (d * n * c)⁻¹ * a * (d * n * c) = b := by
      calc (d * n * c)⁻¹ * a * (d * n * c)
          = c⁻¹ * (n⁻¹ * (d⁻¹ * a * d) * n) * c := by group
        _ = c⁻¹ * b' * c := by rw [h1]; group
        _ = b := h2
    simpa only [inv_inv] using hcalc
  · intro hb
    rw [mem_conjOrbit] at hb
    obtain ⟨n, hnN, hnb⟩ := hb
    rw [mem_blockOf]
    refine ⟨b, hb, n⁻¹, N.inv_mem hnN, ?_⟩
    have h : n⁻¹ * b * n = a := by rw [← hnb]; group
    simpa only [inv_inv] using h ▸ ha

private lemma conjOrbit_eq_biUnion {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hN : N ≤ normalizer (W : Set G)) {i : Fin 7} {a : G} (ha : a ∈ O i) :
    conjOrbit N a = (blockOf N O i).biUnion O := by
  classical
  ext b
  rw [Finset.mem_biUnion]
  constructor
  · intro hb
    obtain ⟨n, hnN, rfl⟩ := mem_conjOrbit.mp hb
    have haW : a ∈ W := (hOW i a ha).1
    have hane : a ≠ 1 := (hOW i a ha).2
    have hbW : n * a * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hN hnN) a).mp haW
    have hbne : n * a * n⁻¹ ≠ 1 := by
      intro h
      apply hane
      calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    obtain ⟨j, hbj⟩ := hcover _ hbW hbne
    exact ⟨j, (mem_blockOf_iff hORB ha hbj).mpr hb, hbj⟩
  · rintro ⟨j, hj, hbj⟩
    exact (mem_blockOf_iff hORB ha hbj).mp hj

private lemma conjOrbit_inf_H_eq {N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hINV : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    {i : Fin 7} {a : G} (ha : a ∈ O i) :
    conjOrbit (N ⊓ H z) a = O i := by
  classical
  ext b
  rw [mem_conjOrbit]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hINV i a ha c hc
  · intro hb
    exact hORB i a ha b hb

private lemma stabilizer_eq_subgroupOf (N : Subgroup G) (a : G) :
    MulAction.stabilizer N a = (N ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf N := by
  classical
  ext n
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, conj_smul_def]
  constructor
  · intro h
    refine ⟨n.2, ?_⟩
    calc (n : G) * a = ((n : G) * a * (n : G)⁻¹) * (n : G) := by group
      _ = a * (n : G) := by rw [h]
  · intro h
    calc (n : G) * a * (n : G)⁻¹ = (a * (n : G)) * (n : G)⁻¹ := by rw [h.2]
      _ = a := by group

private lemma card_conjOrbit_eq_relIndex (N : Subgroup G) (a : G) :
    (conjOrbit N a).card = (N ⊓ Subgroup.centralizer ({a} : Set G)).relIndex N := by
  classical
  have horbit : (MulAction.orbit N a).ncard = (conjOrbit N a).card := by
    rw [← Set.ncard_coe_finset (conjOrbit N a)]
    congr 1
    ext b
    constructor
    · rintro ⟨n, hn⟩
      exact mem_conjOrbit.mpr ⟨n, n.2, by simpa [conj_smul_def] using hn⟩
    · intro hb
      obtain ⟨n, hn, hnb⟩ := mem_conjOrbit.mp hb
      exact ⟨⟨n, hn⟩, by simpa [conj_smul_def] using hnb⟩
  calc (conjOrbit N a).card = (MulAction.orbit N a).ncard := horbit.symm
    _ = (MulAction.stabilizer N a).index := (MulAction.index_stabilizer N a).symm
    _ = ((N ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf N).index := by
        rw [stabilizer_eq_subgroupOf]
    _ = (N ⊓ Subgroup.centralizer ({a} : Set G)).relIndex N := rfl

private lemma block_divisibility {N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hINV : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    {i : Fin 7} {a : G} (ha : a ∈ O i) :
    (conjOrbit N a).card ∣ (conjOrbit N z).card * lemma54Sizes i := by
  classical
  let C : Subgroup G := N ⊓ Subgroup.centralizer ({a} : Set G)
  let C₀ : Subgroup G := (N ⊓ H z) ⊓ Subgroup.centralizer ({a} : Set G)
  have hC : (conjOrbit N a).card = C.relIndex N := card_conjOrbit_eq_relIndex N a
  have hC₀ : (conjOrbit (N ⊓ H z) a).card = C₀.relIndex (N ⊓ H z) :=
    card_conjOrbit_eq_relIndex (N ⊓ H z) a
  have hzcard : (conjOrbit N z).card = (N ⊓ H z).relIndex N := by
    rw [card_conjOrbit_eq_relIndex N z]
    simp [H]
  have hO : (conjOrbit (N ⊓ H z) a).card = lemma54Sizes i := by
    rw [conjOrbit_inf_H_eq hORB hINV ha, hCARD i]
  have hdvd : C.relIndex N ∣ C₀.relIndex N :=
    Subgroup.relIndex_dvd_of_le_left (L := N) (by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩)
  have hmul : C₀.relIndex N = C₀.relIndex (N ⊓ H z) * (N ⊓ H z).relIndex N :=
    (Subgroup.relIndex_mul_relIndex (H := C₀) (K := N ⊓ H z) (L := N)
      inf_le_left inf_le_left).symm
  calc (conjOrbit N a).card = C.relIndex N := hC
    _ ∣ C₀.relIndex N := hdvd
    _ = lemma54Sizes i * (conjOrbit N z).card := by
        rw [hmul, ← hC₀, hO, ← hzcard]
    _ = (conjOrbit N z).card * lemma54Sizes i := by rw [Nat.mul_comm]

private lemma nonempty_O {O : Fin 7 → Finset G} (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (i : Fin 7) : (O i).Nonempty := by
  rw [← Finset.card_pos, hCARD i]
  fin_cases i <;> decide

private lemma blocks_refl {N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i) (i : Fin 7) :
    i ∈ blockOf N O i := by
  classical
  obtain ⟨a, ha⟩ := nonempty_O hCARD i
  rw [mem_blockOf_iff hORB ha ha]
  exact mem_conjOrbit.mpr ⟨1, N.one_mem, by simp⟩

private lemma blockOf_eq_of_orbit_eq {N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    {i j : Fin 7} {a b : G} (ha : a ∈ O i) (hb : b ∈ O j)
    (h : conjOrbit N b = conjOrbit N a) : blockOf N O j = blockOf N O i := by
  classical
  ext l
  obtain ⟨c, hc⟩ := nonempty_O hCARD l
  rw [mem_blockOf_iff hORB hb hc, mem_blockOf_iff hORB ha hc, h]

private lemma blocks_eq {N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    {i j : Fin 7} (hj : j ∈ blockOf N O i) : blockOf N O j = blockOf N O i := by
  classical
  obtain ⟨a, ha⟩ := nonempty_O hCARD i
  obtain ⟨b, hb⟩ := nonempty_O hCARD j
  exact blockOf_eq_of_orbit_eq hORB hCARD ha hb
    (conjOrbit_eq_of_mem ((mem_blockOf_iff hORB ha hb).mp hj))

private lemma card_conjOrbit_eq_sum {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hINV : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hDISJ : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G)) {i : Fin 7} {a : G} (ha : a ∈ O i) :
    (conjOrbit N a).card = ∑ j ∈ blockOf N O i, lemma54Sizes j := by
  classical
  rw [conjOrbit_eq_biUnion hOW hcover hORB hN ha, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun j _ => hCARD j)
  · intro j _ l _ hjl
    exact hDISJ j l hjl

private lemma z_eq_z1_mul_z1z {W : Subgroup G} (hW2 : ∀ a ∈ W, a * a = 1) {z₁ : G}
    (hz₁W : z₁ ∈ W) : z = z₁ * (z₁ * z) := by
  rw [← mul_assoc, hW2 z₁ hz₁W, one_mul]

private lemma mul_eq_z_of_pair {W : Subgroup G}
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    {z₁ : G} (hz₁W : z₁ ∈ W) (hzW : z ∈ W) {a b : G}
    (ha : a = z₁ ∨ a = z₁ * z) (hb : b = z₁ ∨ b = z₁ * z) (hne : a ≠ b) :
    a * b = z := by
  have hz₁sq : z₁ * z₁ = 1 := hW2 z₁ hz₁W
  have hcomm : z * z₁ = z₁ * z := hWab z hzW z₁ hz₁W
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exfalso
    rw [ha, hb] at hne
    exact hne rfl
  · rw [ha, hb, ← mul_assoc, hz₁sq, one_mul]
  · rw [ha, hb]
    calc (z₁ * z) * z₁ = z₁ * (z * z₁) := by group
      _ = z₁ * (z₁ * z) := by rw [hcomm]
      _ = (z₁ * z₁) * z := by group
      _ = z := by rw [hz₁sq, one_mul]
  · exfalso
    rw [ha, hb] at hne
    exact hne rfl

private lemma block_one_ne_singleton {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hN : N ≤ normalizer (W : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hblk1 : blockOf N O 1 = {1}) (hk : ∃ n ∈ N, n ∉ H z) :
    False := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  have hz₁zO1 : z₁ * z ∈ O 1 := by rw [hO1]; simp
  have hzW : z ∈ W := (hOW 0 z hzO0).1
  have hz_ne : z ≠ 1 := (hOW 0 z hzO0).2
  have hz₁W : z₁ ∈ W := (hOW 1 z₁ hz₁O1).1
  have horb1 : conjOrbit N z₁ = O 1 := by
    rw [conjOrbit_eq_biUnion hOW hcover hORB hN hz₁O1, hblk1]
    simp
  have horb1z : conjOrbit N (z₁ * z) = O 1 := by
    rw [conjOrbit_eq_biUnion hOW hcover hORB hN hz₁zO1, hblk1]
    simp
  have hNH : N ≤ H z := by
    intro n hnN
    have hn1 : n * z₁ * n⁻¹ ∈ O 1 := by
      rw [← horb1]
      exact mem_conjOrbit.mpr ⟨n, hnN, rfl⟩
    have hn2 : n * (z₁ * z) * n⁻¹ ∈ O 1 := by
      rw [← horb1z]
      exact mem_conjOrbit.mpr ⟨n, hnN, rfl⟩
    have hn1' : n * z₁ * n⁻¹ = z₁ ∨ n * z₁ * n⁻¹ = z₁ * z := by
      simpa [hO1] using hn1
    have hn2' : n * (z₁ * z) * n⁻¹ = z₁ ∨ n * (z₁ * z) * n⁻¹ = z₁ * z := by
      simpa [hO1] using hn2
    have hne : n * z₁ * n⁻¹ ≠ n * (z₁ * z) * n⁻¹ := by
      intro h
      have hzz : z₁ = z₁ * z := by
        calc z₁ = n⁻¹ * (n * z₁ * n⁻¹) * n := by group
          _ = n⁻¹ * (n * (z₁ * z) * n⁻¹) * n := by rw [h]
          _ = z₁ * z := by group
      have hz1 : z = 1 := by
        have h' := congrArg (fun t => z₁⁻¹ * t) hzz
        simpa [mul_assoc] using h'.symm
      exact hz_ne hz1
    have hprod : (n * z₁ * n⁻¹) * (n * (z₁ * z) * n⁻¹) = z :=
      mul_eq_z_of_pair hWab hW2 hz₁W hzW hn1' hn2' hne
    have hnz : n * z * n⁻¹ = z := by
      calc n * z * n⁻¹ = n * (z₁ * (z₁ * z)) * n⁻¹ := by
            conv_lhs => rw [z_eq_z1_mul_z1z (W := W) (z := z) (z₁ := z₁) hW2 hz₁W]
        _ = (n * z₁ * n⁻¹) * (n * (z₁ * z) * n⁻¹) := by group
        _ = z := hprod
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [hnz]
  obtain ⟨n, hnN, hnH⟩ := hk
  exact hnH (hNH hnN)

private lemma conj_mem_closure_of_conj_mem {S : Set G} {K : Subgroup G} {n : G}
    (hn : ∀ x ∈ S, n * x * n⁻¹ ∈ K) {x : G} (hx : x ∈ Subgroup.closure S) :
    n * x * n⁻¹ ∈ K := by
  have hmap : (Subgroup.closure S).map (MulAut.conj n).toMonoidHom ≤ K := by
    rw [MonoidHom.map_closure]
    exact (Subgroup.closure_le (K := K)).mpr (by
      rintro y ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hn x hx)
  exact hmap (Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩)

private lemma mem_J_of_mem_biUnion_of_subset {O : Fin 7 → Finset G} {s : Finset (Fin 7)}
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hsub : s ⊆ ({0, 1, 2, 3} : Finset (Fin 7))) {x : G} (hx : x ∈ s.biUnion O) :
    x ∈ J z := by
  rw [Finset.mem_biUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  have hi4 : (i : ℕ) < 4 := by
    have hmem : i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) := hsub hi
    fin_cases i <;> simp_all
  exact hJ i hi4 x hxi

private lemma normalizer_closure_conjOrbit (N : Subgroup G) (j : G) :
    N ≤ Subgroup.normalizer (Subgroup.closure (conjOrbit N j : Set G) : Set G) := by
  classical
  intro n hn
  apply Subgroup.normalizer_le_normalizer_closure (conjOrbit N j : Set G)
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, hmN, rfl⟩ := mem_conjOrbit.mp hy
    exact mem_conjOrbit.mpr ⟨n * m, N.mul_mem hn hmN, by
      rw [MulAut.conj_apply]; group⟩
  · intro hx
    refine ⟨n⁻¹ * x * n, ?_, ?_⟩
    · obtain ⟨m, hmN, rfl⟩ := mem_conjOrbit.mp hx
      exact mem_conjOrbit.mpr ⟨n⁻¹ * m, N.mul_mem (N.inv_mem hn) hmN, by group⟩
    · rw [MulAut.conj_apply]; group

private lemma span_block_common {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO0 : O 0 = {z}) {k : Fin 7} (hOkz : ∀ a ∈ O k, a * z ∈ O k)
    (hksub : blockOf N O k ⊆ {2, 3}) : blockOf N O 0 ⊆ {0, 1, 2, 3} := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  obtain ⟨j, hj⟩ := nonempty_O hCARD k
  let R : Subgroup G := Subgroup.closure (conjOrbit N j : Set G)
  have hNR : N ≤ Subgroup.normalizer (R : Set G) := normalizer_closure_conjOrbit N j
  have hRJ : R ≤ J z := by
    apply (Subgroup.closure_le (K := J z)).mpr
    intro x hx
    have hx' : x ∈ (blockOf N O k).biUnion O := by
      rw [← conjOrbit_eq_biUnion hOW hcover hORB hN hj]
      exact hx
    exact mem_J_of_mem_biUnion_of_subset hJ (hksub.trans (by decide)) hx'
  have hj_orb : j ∈ conjOrbit N j := by
    rw [mem_conjOrbit]; exact ⟨1, N.one_mem, by simp⟩
  have hjR : j ∈ R := Subgroup.subset_closure (by simpa using hj_orb)
  have hjz_orb : j * z ∈ conjOrbit N j := by
    have hsub : O k ⊆ conjOrbit N j := by
      intro b hb
      rw [conjOrbit_eq_biUnion hOW hcover hORB hN hj]
      exact Finset.mem_biUnion.mpr ⟨k, blocks_refl hORB hCARD k, hb⟩
    exact hsub (hOkz j hj)
  have hjzR : j * z ∈ R := Subgroup.subset_closure (by simpa using hjz_orb)
  have hzR : z ∈ R := by
    have h : z = j⁻¹ * (j * z) := by group
    rw [h]
    exact Subgroup.mul_mem R (Subgroup.inv_mem R hjR) hjzR
  have horbzR : ∀ x ∈ conjOrbit N z, x ∈ R := by
    intro x hx
    obtain ⟨n, hnN, rfl⟩ := mem_conjOrbit.mp hx
    exact (Subgroup.mem_normalizer_iff.mp (hNR hnN) z).mp hzR
  intro i hi
  have hi4 : (i : ℕ) < 4 := by
    by_contra h
    have h4 : 4 ≤ (i : ℕ) := by omega
    obtain ⟨b, hb⟩ := nonempty_O hCARD i
    have hb_orb : b ∈ conjOrbit N z := (mem_blockOf_iff hORB hzO0 hb).mp hi
    exact hnJ i h4 b hb (hRJ (horbzR b hb_orb))
  fin_cases i <;> simp_all

private lemma span_block_two {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO0 : O 0 = {z}) (hO2z : ∀ a ∈ O 2, a * z ∈ O 2) :
    blockOf N O 2 ⊆ {2, 3} → blockOf N O 0 ⊆ {0, 1, 2, 3} :=
  fun hsub => span_block_common hOW hcover hORB hCARD hN hJ hnJ hO0 (k := 2) hO2z hsub

private lemma span_block_three {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO0 : O 0 = {z}) (hO3z : ∀ a ∈ O 3, a * z ∈ O 3) :
    blockOf N O 3 ⊆ {2, 3} → blockOf N O 0 ⊆ {0, 1, 2, 3} :=
  fun hsub => span_block_common hOW hcover hORB hCARD hN hJ hnJ hO0 (k := 3) hO3z hsub

private lemma block_one_subset_of_blocks_two_three {W N : Subgroup G} {O : Fin 7 → Finset G}
    {z₁ : G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO1 : O 1 = {z₁, z₁ * z})
    (hgen : J z ⊓ W ≤ closure ((O 2 : Set G) ∪ (O 3 : Set G)))
    (h2sub : blockOf N O 2 ⊆ {0, 1, 2, 3}) (h3sub : blockOf N O 3 ⊆ {0, 1, 2, 3}) :
    blockOf N O 1 ⊆ {0, 1, 2, 3} := by
  classical
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  have hz₁JW : z₁ ∈ J z ⊓ W :=
    Subgroup.mem_inf.mpr ⟨hJ 1 (by decide) z₁ hz₁O1, (hOW 1 z₁ hz₁O1).1⟩
  have hJW_eq : J z ⊓ W = Subgroup.closure ((O 2 : Set G) ∪ (O 3 : Set G)) := by
    apply le_antisymm hgen
    apply (Subgroup.closure_le (K := J z ⊓ W)).mpr
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.mem_inf.mpr
        ⟨hJ 2 (by decide) x (by simpa using hx), (hOW 2 x (by simpa using hx)).1⟩
    · exact Subgroup.mem_inf.mpr
        ⟨hJ 3 (by decide) x (by simpa using hx), (hOW 3 x (by simpa using hx)).1⟩
  have hmaps : ∀ y ∈ ((O 2 : Set G) ∪ (O 3 : Set G)), ∀ n ∈ N,
      n * y * n⁻¹ ∈ J z ⊓ W := by
    intro y hy n hn
    rcases hy with hy | hy
    · have hy' : n * y * n⁻¹ ∈ (blockOf N O 2).biUnion O := by
        rw [← conjOrbit_eq_biUnion hOW hcover hORB hN (by simpa using hy)]
        exact mem_conjOrbit.mpr ⟨n, hn, rfl⟩
      exact Subgroup.mem_inf.mpr
        ⟨mem_J_of_mem_biUnion_of_subset hJ h2sub hy',
          (Subgroup.mem_normalizer_iff.mp (hN hn) y).mp (hOW 2 y (by simpa using hy)).1⟩
    · have hy' : n * y * n⁻¹ ∈ (blockOf N O 3).biUnion O := by
        rw [← conjOrbit_eq_biUnion hOW hcover hORB hN (by simpa using hy)]
        exact mem_conjOrbit.mpr ⟨n, hn, rfl⟩
      exact Subgroup.mem_inf.mpr
        ⟨mem_J_of_mem_biUnion_of_subset hJ h3sub hy',
          (Subgroup.mem_normalizer_iff.mp (hN hn) y).mp (hOW 3 y (by simpa using hy)).1⟩
  have hfix : ∀ n ∈ N, n * z₁ * n⁻¹ ∈ J z ⊓ W := by
    intro n hn
    have hz₁cl : z₁ ∈ Subgroup.closure ((O 2 : Set G) ∪ (O 3 : Set G)) := by
      rw [← hJW_eq]
      exact hz₁JW
    exact conj_mem_closure_of_conj_mem (fun y hy => hmaps y hy n hn) hz₁cl
  intro i hi
  have hi4 : (i : ℕ) < 4 := by
    by_contra h
    have h4 : 4 ≤ (i : ℕ) := by omega
    obtain ⟨b, hb⟩ := nonempty_O hCARD i
    have hb_orb : b ∈ conjOrbit N z₁ := (mem_blockOf_iff hORB hz₁O1 hb).mp hi
    obtain ⟨n, hnN, rfl⟩ := mem_conjOrbit.mp hb_orb
    exact hnJ i h4 (n * z₁ * n⁻¹) hb (hfix n hnN).1
  fin_cases i <;> simp_all

private lemma blk_zero_ne {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hN : N ≤ normalizer (W : Set G))
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hO0 : O 0 = {z}) (hk : ∃ n ∈ N, n ∉ H z) :
    blockOf N O 0 ≠ {0} := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  intro hblk0
  obtain ⟨n, hnN, hnH⟩ := hk
  have hmem : n * z * n⁻¹ ∈ conjOrbit N z := mem_conjOrbit.mpr ⟨n, hnN, rfl⟩
  have hz_fixed : n * z * n⁻¹ = z := by
    have h' : n * z * n⁻¹ ∈ (blockOf N O 0).biUnion O := by
      rw [← conjOrbit_eq_biUnion hOW hcover hORB hN hzO0]
      exact hmem
    simp only [hblk0, Finset.singleton_biUnion, hO0] at h'
    simpa using h'
  apply hnH
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc n * z = (n * z * n⁻¹) * n := by group
    _ = z * n := by rw [hz_fixed]

private lemma blk_one_not_mem_zero {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hN : N ≤ normalizer (W : Set G)) (hO0 : O 0 = {z})
    (hO1 : O 1 = {z₁, z₁ * z}) (hz₁z : ¬ IsConj z₁ z) :
    (1 : Fin 7) ∉ blockOf N O 0 := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  intro h1
  have hsub : O 1 ⊆ conjOrbit N z := by
    intro b hb
    exact (mem_blockOf_iff hORB hzO0 hb).mp h1
  obtain ⟨n, hnN, hconj⟩ := mem_conjOrbit.mp (hsub hz₁O1)
  exact hz₁z (isConj_comm.mpr (isConj_iff.mpr ⟨n, hconj⟩))

private lemma blk_two_not_mem_one {N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hO1 : O 1 = {z₁, z₁ * z})
    (hz₁j : ∀ a, a ∈ O 2 ∨ a ∈ O 3 → ¬ IsConj z₁ a) :
    (2 : Fin 7) ∉ blockOf N O 1 := by
  classical
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  intro h2
  have hsub : O 2 ⊆ conjOrbit N z₁ := by
    intro b hb
    exact (mem_blockOf_iff hORB hz₁O1 hb).mp h2
  obtain ⟨a, ha⟩ := nonempty_O hCARD 2
  obtain ⟨n, hnN, hconj⟩ := mem_conjOrbit.mp (hsub ha)
  exact hz₁j a (Or.inl ha) (isConj_iff.mpr ⟨n, hconj⟩)

private lemma blk_three_not_mem_one {N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hO1 : O 1 = {z₁, z₁ * z})
    (hz₁j : ∀ a, a ∈ O 2 ∨ a ∈ O 3 → ¬ IsConj z₁ a) :
    (3 : Fin 7) ∉ blockOf N O 1 := by
  classical
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  intro h3
  have hsub : O 3 ⊆ conjOrbit N z₁ := by
    intro b hb
    exact (mem_blockOf_iff hORB hz₁O1 hb).mp h3
  obtain ⟨a, ha⟩ := nonempty_O hCARD 3
  obtain ⟨n, hnN, hconj⟩ := mem_conjOrbit.mp (hsub ha)
  exact hz₁j a (Or.inr ha) (isConj_iff.mpr ⟨n, hconj⟩)

private lemma blk_one_ne_singleton {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hN : N ≤ normalizer (W : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hk : ∃ n ∈ N, n ∉ H z) : blockOf N O 1 ≠ {1} := by
  intro hblk1
  exact block_one_ne_singleton hOW hcover hORB hN hWab hW2 hO0 hO1 hblk1 hk

private lemma blk_divisibility {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hINV : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hDISJ : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G)) (hO0 : O 0 = {z}) :
    ∀ i, (∑ j ∈ blockOf N O i, lemma54Sizes j) ∣
      (∑ j ∈ blockOf N O 0, lemma54Sizes j) * lemma54Sizes i := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  intro i
  obtain ⟨a, ha⟩ := nonempty_O hCARD i
  have h1 : (∑ j ∈ blockOf N O i, lemma54Sizes j) = (conjOrbit N a).card :=
    (card_conjOrbit_eq_sum hOW hcover hORB hINV hDISJ hCARD hN ha).symm
  have h2 : (∑ j ∈ blockOf N O 0, lemma54Sizes j) = (conjOrbit N z).card :=
    (card_conjOrbit_eq_sum hOW hcover hORB hINV hDISJ hCARD hN hzO0).symm
  rw [h1, h2]
  exact block_divisibility hORB hINV hCARD ha

private lemma blk_span_two {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO0 : O 0 = {z}) (hO2z : ∀ a ∈ O 2, a * z ∈ O 2) :
    blockOf N O 2 ⊆ {2, 3} → blockOf N O 0 ⊆ {0, 1, 2, 3} :=
  fun hsub => span_block_two hOW hcover hORB hCARD hN hJ hnJ hO0 hO2z hsub

private lemma blk_span_three {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO0 : O 0 = {z}) (hO3z : ∀ a ∈ O 3, a * z ∈ O 3) :
    blockOf N O 3 ⊆ {2, 3} → blockOf N O 0 ⊆ {0, 1, 2, 3} :=
  fun hsub => span_block_three hOW hcover hORB hCARD hN hJ hnJ hO0 hO3z hsub

private lemma blk_JW {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO1 : O 1 = {z₁, z₁ * z})
    (hgen : J z ⊓ W ≤ closure ((O 2 : Set G) ∪ (O 3 : Set G))) :
    blockOf N O 2 ⊆ {0, 1, 2, 3} → blockOf N O 3 ⊆ {0, 1, 2, 3} →
      blockOf N O 1 ⊆ {0, 1, 2, 3} :=
  fun h2sub h3sub =>
    block_one_subset_of_blocks_two_three hOW hcover hORB hCARD hN hJ hnJ hO1 hgen h2sub h3sub

private lemma blk_hypotheses {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hN : N ≤ normalizer (W : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hDISJ : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hINV : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO2z : ∀ a ∈ O 2, a * z ∈ O 2) (hO3z : ∀ a ∈ O 3, a * z ∈ O 3)
    (hgen : J z ⊓ W ≤ closure ((O 2 : Set G) ∪ (O 3 : Set G)))
    (hz₁z : ¬ IsConj z₁ z) (hz₁j : ∀ a, a ∈ O 2 ∨ a ∈ O 3 → ¬ IsConj z₁ a)
    (hk : ∃ n ∈ N, n ∉ H z) :
    (∀ i, i ∈ blockOf N O i) ∧
    (∀ i j, j ∈ blockOf N O i → blockOf N O j = blockOf N O i) ∧
    blockOf N O 0 ≠ {0} ∧
    (1 : Fin 7) ∉ blockOf N O 0 ∧
    (2 : Fin 7) ∉ blockOf N O 1 ∧
    (3 : Fin 7) ∉ blockOf N O 1 ∧
    blockOf N O 1 ≠ {1} ∧
    (∀ i, (∑ j ∈ blockOf N O i, lemma54Sizes j) ∣
      (∑ j ∈ blockOf N O 0, lemma54Sizes j) * lemma54Sizes i) ∧
    (blockOf N O 2 ⊆ {2, 3} → blockOf N O 0 ⊆ {0, 1, 2, 3}) ∧
    (blockOf N O 3 ⊆ {2, 3} → blockOf N O 0 ⊆ {0, 1, 2, 3}) ∧
    (blockOf N O 2 ⊆ {0, 1, 2, 3} → blockOf N O 3 ⊆ {0, 1, 2, 3} →
      blockOf N O 1 ⊆ {0, 1, 2, 3}) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact blocks_refl hORB hCARD i
  · intro i j hj
    exact blocks_eq hORB hCARD hj
  · exact blk_zero_ne hN hOW hcover hORB hO0 hk
  · exact blk_one_not_mem_zero hOW hcover hORB hN hO0 hO1 hz₁z
  · exact blk_two_not_mem_one hORB hCARD hO1 hz₁j
  · exact blk_three_not_mem_one hORB hCARD hO1 hz₁j
  · exact blk_one_ne_singleton hOW hcover hORB hN hWab hW2 hO0 hO1 hk
  · exact blk_divisibility hOW hcover hORB hINV hDISJ hCARD hN hO0
  · exact blk_span_two hOW hcover hORB hCARD hN hJ hnJ hO0 hO2z
  · exact blk_span_three hOW hcover hORB hCARD hN hJ hnJ hO0 hO3z
  · exact blk_JW hOW hcover hORB hCARD hN hJ hnJ hO1 hgen

private lemma lemma54_conj_four {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hO0 : O 0 = {z}) (h4 : (4 : Fin 7) ∈ blockOf N O 0) :
    ∀ a ∈ O 4, ∃ n ∈ N, n * z * n⁻¹ = a := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  intro a ha
  exact mem_conjOrbit.mp ((mem_blockOf_iff hORB hzO0 ha).mp h4)

private lemma lemma54_conj_two_or_three {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i) (hO0 : O 0 = {z})
    (h23 : (2 : Fin 7) ∈ blockOf N O 0 ∨ (3 : Fin 7) ∈ blockOf N O 0) :
    ∃ a, (a ∈ O 2 ∨ a ∈ O 3) ∧ ∃ n ∈ N, n * z * n⁻¹ = a := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  rcases h23 with h2 | h3
  · obtain ⟨a, ha⟩ := nonempty_O hCARD 2
    exact ⟨a, Or.inl ha, mem_conjOrbit.mp ((mem_blockOf_iff hORB hzO0 ha).mp h2)⟩
  · obtain ⟨a, ha⟩ := nonempty_O hCARD 3
    exact ⟨a, Or.inr ha, mem_conjOrbit.mp ((mem_blockOf_iff hORB hzO0 ha).mp h3)⟩

private lemma lemma54_conj_five_six {W N : Subgroup G} {O : Fin 7 → Finset G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hO0 : O 0 = {z})
    (h5 : (5 : Fin 7) ∉ blockOf N O 0) (h6 : (6 : Fin 7) ∉ blockOf N O 0) :
    ∀ a, (a ∈ O 5 ∨ a ∈ O 6) → ∀ n ∈ N, n * z * n⁻¹ ≠ a := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  intro a ha n hn heq
  have hmem : a ∈ conjOrbit N z := mem_conjOrbit.mpr ⟨n, hn, heq⟩
  rcases ha with ha | ha
  · exact h5 ((mem_blockOf_iff hORB hzO0 ha).mpr hmem)
  · exact h6 ((mem_blockOf_iff hORB hzO0 ha).mpr hmem)

private lemma lemma54_conj_one_five_six {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hO1 : O 1 = {z₁, z₁ * z})
    (h56 : (5 : Fin 7) ∈ blockOf N O 1 ∨ (6 : Fin 7) ∈ blockOf N O 1) :
    ∃ a, (a ∈ O 5 ∨ a ∈ O 6) ∧ ∃ n ∈ N, n * z₁ * n⁻¹ = a := by
  classical
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  rcases h56 with h5 | h6
  · obtain ⟨a, ha⟩ := nonempty_O hCARD 5
    exact ⟨a, Or.inl ha, mem_conjOrbit.mp ((mem_blockOf_iff hORB hz₁O1 ha).mp h5)⟩
  · obtain ⟨a, ha⟩ := nonempty_O hCARD 6
    exact ⟨a, Or.inr ha, mem_conjOrbit.mp ((mem_blockOf_iff hORB hz₁O1 ha).mp h6)⟩

private lemma lemma54_conj_centralizer {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hINV : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hDISJ : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hN : N ≤ normalizer (W : Set G))
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hlast : (∑ j ∈ blockOf N O 1, lemma54Sizes j) ≠
      2 * ∑ j ∈ blockOf N O 0, lemma54Sizes j) :
    ∃ n ∈ N, n * z₁ * n⁻¹ = z₁ ∧ n ∉ H z := by
  classical
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  by_contra h
  push Not at h
  let C : Subgroup G := N ⊓ Subgroup.centralizer ({z₁} : Set G)
  let C₀ : Subgroup G := (N ⊓ H z) ⊓ Subgroup.centralizer ({z₁} : Set G)
  have hC_le_H : C ≤ H z := by
    intro n hn
    apply h n hn.1
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hn.2
    calc n * z₁ * n⁻¹ = (z₁ * n) * n⁻¹ := by rw [hcomm]
      _ = z₁ := by group
  have hC_eq : C = C₀ := by
    ext n
    constructor
    · intro hn
      exact ⟨⟨hn.1, hC_le_H hn⟩, hn.2⟩
    · intro hn
      exact ⟨hn.1.1, hn.2⟩
  have hcard1 : (conjOrbit N z₁).card = C₀.relIndex N := by
    rw [card_conjOrbit_eq_relIndex N z₁]
    change C.relIndex N = C₀.relIndex N
    rw [hC_eq]
  have hmul : C₀.relIndex N = C₀.relIndex (N ⊓ H z) * (N ⊓ H z).relIndex N :=
    (Subgroup.relIndex_mul_relIndex (H := C₀) (K := N ⊓ H z) (L := N)
      inf_le_left inf_le_left).symm
  have hC₀ : C₀.relIndex (N ⊓ H z) = 2 := by
    rw [← card_conjOrbit_eq_relIndex (N ⊓ H z) z₁,
      conjOrbit_inf_H_eq hORB hINV hz₁O1, hCARD 1]
    rfl
  have hN₀ : (N ⊓ H z).relIndex N = (conjOrbit N z).card := by
    rw [card_conjOrbit_eq_relIndex N z]
    simp [H]
  have h2k : (conjOrbit N z₁).card = 2 * (conjOrbit N z).card := by
    rw [hcard1, hmul, hC₀, hN₀]
  have hS1 : (∑ j ∈ blockOf N O 1, lemma54Sizes j) = (conjOrbit N z₁).card :=
    (card_conjOrbit_eq_sum hOW hcover hORB hINV hDISJ hCARD hN hz₁O1).symm
  have hS0 : (∑ j ∈ blockOf N O 0, lemma54Sizes j) = (conjOrbit N z).card :=
    (card_conjOrbit_eq_sum hOW hcover hORB hINV hDISJ hCARD hN hzO0).symm
  exact hlast (by rw [hS1, hS0, h2k])

private lemma eq_one_of_dvd_seven_pow {d n : ℕ} (hd : d ∣ 7 ^ n) (h6 : d ≤ 6) : d = 1 := by
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hd
  have hk0 : k = 0 := by
    by_contra hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h7 : 7 ≤ 7 ^ k := by
      simpa using le_self_pow (show 1 ≤ 7 by norm_num) (Nat.ne_zero_of_lt hk1)
    omega
  rw [hk0, pow_zero]

private lemma le_centralizer_of_orbit_subset {N Q : Subgroup G} {x z₁ : G}
    (hQp : IsPGroup 7 Q) (hsub : conjOrbit Q x ⊆ conjOrbit N z₁)
    (h6 : (conjOrbit N z₁).card ≤ 6) :
    Q ≤ Subgroup.centralizer ({x} : Set G) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hcard : (conjOrbit Q x).card = 1 := by
    have hdvd : (conjOrbit Q x).card ∣ 7 ^ n := by
      calc (conjOrbit Q x).card = (Q ⊓ Subgroup.centralizer ({x} : Set G)).relIndex Q :=
            card_conjOrbit_eq_relIndex Q x
        _ ∣ Nat.card Q := Subgroup.relIndex_dvd_card _ _
        _ = 7 ^ n := hn
    exact eq_one_of_dvd_seven_pow hdvd ((Finset.card_le_card hsub).trans h6)
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxmem : x ∈ conjOrbit Q x := mem_conjOrbit.mpr ⟨1, Q.one_mem, by simp⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
  have hxy : x = y := by
    rw [hy] at hxmem
    simpa using hxmem
  have hqmem : q * x * q⁻¹ ∈ conjOrbit Q x := mem_conjOrbit.mpr ⟨q, hq, rfl⟩
  rw [hy] at hqmem
  calc q * x = (q * x * q⁻¹) * q := by group
    _ = y * q := by rw [show q * x * q⁻¹ = y by simpa using hqmem]
    _ = x * q := by rw [← hxy]

private lemma le_centralizer_mul {Q : Subgroup G} {a b : G}
    (ha : Q ≤ Subgroup.centralizer ({a} : Set G))
    (hb : Q ≤ Subgroup.centralizer ({b} : Set G)) :
    Q ≤ Subgroup.centralizer ({a * b} : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hqa : q * a = a * q :=
    Subgroup.mem_centralizer_singleton_iff.mp (ha hq)
  have hqb : q * b = b * q :=
    Subgroup.mem_centralizer_singleton_iff.mp (hb hq)
  calc q * (a * b) = (q * a) * b := by group
    _ = (a * q) * b := by rw [hqa]
    _ = a * (q * b) := by group
    _ = a * (b * q) := by rw [hqb]
    _ = (a * b) * q := by group

private lemma seven_dvd_of_isSylow_le_inf_centralizer {N Q : Subgroup G}
    (hQ : IsSylowOf 7 Q N) (hQC : Q ≤ N ⊓ Subgroup.centralizer ({z} : Set G))
    (hrel : (N ⊓ Subgroup.centralizer ({z} : Set G)).relIndex N = 21) : False := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hQnot : ¬ 7 ∣ Q.relIndex N := (isSylowOf_iff.mp hQ).2.2
  have hdvd : 21 ∣ Q.relIndex N := by
    rw [← hrel]
    exact Subgroup.relIndex_dvd_of_le_left (L := N) hQC
  exact hQnot ((by decide : 7 ∣ 21).trans hdvd)

private lemma blk_seven {W N : Subgroup G} {O : Fin 7 → Finset G} {z₁ : G}
    (hN : N ≤ normalizer (W : Set G)) (hW2 : ∀ a ∈ W, a * a = 1)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hDISJ : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hORB : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hINV : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hCARD : ∀ i, (O i).card = lemma54Sizes i)
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z}) :
    ∑ j ∈ blockOf N O 0, lemma54Sizes j = 21 → 6 < ∑ j ∈ blockOf N O 1, lemma54Sizes j := by
  classical
  intro h21
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hzO0 : z ∈ O 0 := by rw [hO0]; simp
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  have hz₁zO1 : z₁ * z ∈ O 1 := by rw [hO1]; simp
  have hz₁W : z₁ ∈ W := (hOW 1 z₁ hz₁O1).1
  have hS0 : (conjOrbit N z).card = ∑ j ∈ blockOf N O 0, lemma54Sizes j :=
    card_conjOrbit_eq_sum hOW hcover hORB hINV hDISJ hCARD hN hzO0
  have hS1 : (conjOrbit N z₁).card = ∑ j ∈ blockOf N O 1, lemma54Sizes j :=
    card_conjOrbit_eq_sum hOW hcover hORB hINV hDISJ hCARD hN hz₁O1
  by_contra hle
  have hS1le : (conjOrbit N z₁).card ≤ 6 := by
    rw [hS1]
    omega
  obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := N)
  let Q : Subgroup G := (P : Subgroup N).map N.subtype
  have hQ : IsSylowOf 7 Q N := ⟨P, rfl⟩
  have hQle : Q ≤ N := hQ.le
  have hQp : IsPGroup 7 Q := hQ.isPGroup
  have hmono : ∀ x, conjOrbit Q x ⊆ conjOrbit N x := by
    intro x y hy
    obtain ⟨q, hq, rfl⟩ := mem_conjOrbit.mp hy
    exact mem_conjOrbit.mpr ⟨q, hQle hq, rfl⟩
  have hz₁z_mem : z₁ * z ∈ conjOrbit N z₁ := by
    obtain ⟨c, hc, hceq⟩ := hORB 1 z₁ hz₁O1 (z₁ * z) hz₁zO1
    exact mem_conjOrbit.mpr ⟨c, hc.1, hceq⟩
  have hz₁z_orb : conjOrbit N (z₁ * z) = conjOrbit N z₁ :=
    conjOrbit_eq_of_mem hz₁z_mem
  have hcent1 : Q ≤ Subgroup.centralizer ({z₁} : Set G) :=
    le_centralizer_of_orbit_subset hQp (hmono z₁) hS1le
  have hcent2 : Q ≤ Subgroup.centralizer ({z₁ * z} : Set G) :=
    le_centralizer_of_orbit_subset hQp (hz₁z_orb ▸ hmono (z₁ * z)) hS1le
  have hQcent : Q ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [z_eq_z1_mul_z1z (W := W) (z := z) (z₁ := z₁) hW2 hz₁W]
    exact le_centralizer_mul hcent1 hcent2
  have hQC : Q ≤ N ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun q hq => Subgroup.mem_inf.mpr ⟨hQle hq, hQcent hq⟩
  have hrel : (N ⊓ Subgroup.centralizer ({z} : Set G)).relIndex N = 21 := by
    rw [← card_conjOrbit_eq_relIndex N z, hS0]
    exact h21
  exact seven_dvd_of_isSylow_le_inf_centralizer hQ hQC hrel

end

theorem lemma54_orbits [DecidableEq G] {z₁ : G} {W N : Subgroup G} (hN : N ≤ normalizer (W : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (O : Fin 7 → Finset G)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (horb : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hinv : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hcard : ∀ i, (O i).card = lemma54Sizes i)
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO2z : ∀ a ∈ O 2, a * z ∈ O 2) (hO3z : ∀ a ∈ O 3, a * z ∈ O 3)
    (hgen : J z ⊓ W ≤ closure ((O 2 : Set G) ∪ (O 3 : Set G)))
    (hz₁z : ¬ IsConj z₁ z) (hz₁j : ∀ a, a ∈ O 2 ∨ a ∈ O 3 → ¬ IsConj z₁ a)
    (hk : ∃ n ∈ N, n ∉ H z) :
    (∀ a ∈ O 4, ∃ n ∈ N, n * z * n⁻¹ = a) ∧
      (∃ a, (a ∈ O 2 ∨ a ∈ O 3) ∧ ∃ n ∈ N, n * z * n⁻¹ = a) ∧
      (∀ a, (a ∈ O 5 ∨ a ∈ O 6) → ∀ n ∈ N, n * z * n⁻¹ ≠ a) ∧
      (∃ a, (a ∈ O 5 ∨ a ∈ O 6) ∧ ∃ n ∈ N, n * z₁ * n⁻¹ = a) ∧
      (∃ n ∈ N, n * z₁ * n⁻¹ = z₁ ∧ n ∉ H z) := by
  classical
  obtain ⟨hrefl, heq, hk', h01, h12, h13, h11, hdiv, hspan2, hspan3, hJW⟩ :=
    blk_hypotheses hN hWab hW2 hOW hcover hdisj horb hinv hcard hO0 hO1 hJ hnJ hO2z hO3z
      hgen hz₁z hz₁j hk
  have hblk := lemma54_blocks (blockOf N O) hrefl heq hk' h01 h12 h13 h11 hdiv hspan2 hspan3 hJW
  exact ⟨lemma54_conj_four (W := W) horb hO0 hblk.1,
    lemma54_conj_two_or_three (W := W) horb hcard hO0 hblk.2.1,
    lemma54_conj_five_six (W := W) horb hO0 hblk.2.2.1 hblk.2.2.2.1,
    lemma54_conj_one_five_six (W := W) horb hcard hO1 hblk.2.2.2.2.1,
    lemma54_conj_centralizer (W := W) hOW hcover horb hinv hdisj hcard hN hO0 hO1
      hblk.2.2.2.2.2⟩

theorem lemma54_orbits_five_six [DecidableEq G] {z₁ : G} {W N : Subgroup G}
    (hN : N ≤ normalizer (W : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (O : Fin 7 → Finset G)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (horb : ∀ i, ∀ a ∈ O i, ∀ b ∈ O i, ∃ c ∈ N ⊓ H z, c * a * c⁻¹ = b)
    (hinv : ∀ i, ∀ a ∈ O i, ∀ c ∈ N ⊓ H z, c * a * c⁻¹ ∈ O i)
    (hcard : ∀ i, (O i).card = lemma54Sizes i)
    (hO0 : O 0 = {z}) (hO1 : O 1 = {z₁, z₁ * z})
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO2z : ∀ a ∈ O 2, a * z ∈ O 2) (hO3z : ∀ a ∈ O 3, a * z ∈ O 3)
    (hgen : J z ⊓ W ≤ closure ((O 2 : Set G) ∪ (O 3 : Set G)))
    (hz₁z : ¬ IsConj z₁ z) (hz₁j : ∀ a, a ∈ O 2 ∨ a ∈ O 3 → ¬ IsConj z₁ a)
    (hk : ∃ n ∈ N, n ∉ H z) :
    ∀ a ∈ O 5, ∀ b ∈ O 6, ¬ IsConj a b := by
  classical
  obtain ⟨hrefl, heq, hk', h01, h12, h13, h11, hdiv, hspan2, hspan3, hJW⟩ :=
    blk_hypotheses hN hWab hW2 hOW hcover hdisj horb hinv hcard hO0 hO1 hJ hnJ hO2z hO3z
      hgen hz₁z hz₁j hk
  have h7 := blk_seven hN hW2 hOW hcover hdisj horb hinv hcard hO0 hO1
  have hfive_six := lemma54_blocks_five_six (blockOf N O) hrefl heq hk' h01 h12 h13 h11
    hdiv hspan2 hspan3 hJW h7
  have hz₁O1 : z₁ ∈ O 1 := by rw [hO1]; simp
  have hconj_of_block : ∀ {i j : Fin 7} {x y : G}, x ∈ O i → y ∈ O j →
      j ∈ blockOf N O i → IsConj x y := by
    intro i j x y hx hy hmem
    obtain ⟨n, -, hn⟩ := mem_conjOrbit.mp ((mem_blockOf_iff horb hx hy).mp hmem)
    exact isConj_iff.mpr ⟨n, hn⟩
  intro a ha b hb hab
  rcases hfive_six with ⟨h5, h6⟩ | ⟨h6, h5⟩
  · rcases h6 with h6 | h6
    · obtain ⟨c, hc⟩ := nonempty_O hcard 2
      exact hz₁j c (Or.inl hc)
        ((hconj_of_block hz₁O1 ha h5).trans (hab.trans (hconj_of_block hc hb h6).symm))
    · obtain ⟨c, hc⟩ := nonempty_O hcard 3
      exact hz₁j c (Or.inr hc)
        ((hconj_of_block hz₁O1 ha h5).trans (hab.trans (hconj_of_block hc hb h6).symm))
  · rcases h5 with h5 | h5
    · obtain ⟨c, hc⟩ := nonempty_O hcard 2
      exact hz₁j c (Or.inl hc)
        ((hconj_of_block hz₁O1 hb h6).trans (hab.symm.trans
          (hconj_of_block hc ha h5).symm))
    · obtain ⟨c, hc⟩ := nonempty_O hcard 3
      exact hz₁j c (Or.inr hc)
        ((hconj_of_block hz₁O1 hb h6).trans (hab.symm.trans
          (hconj_of_block hc ha h5).symm))

end CFSG.RankThree.GF2n.Parrott
