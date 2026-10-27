module

public import CFSG.Quasithin.EmptyFaithful.S151WB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A]

theorem flip4_exists_flip [Finite A] {L S B : Subgroup A} (hBdef : B = S ⊓ L)
    (D : SurjBorel 4 L B) (hSN : S ≤ Subgroup.normalizer (L : Set A))
    (hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set A), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (hnt : ¬ SActsTrivially L S) :
    ∃ s ∈ S, ∀ K : Subgroup A, B ≤ K → K ≤ L →
      D.cutsOf (conjSub s K) = flipNodes 4 (D.cutsOf K) := by
  classical
  have hSB : ∀ s ∈ S, s ∈ Subgroup.normalizer (B : Set A) := fun s hs => by
    rw [hBdef]
    exact zb_mem_normalizer_inf (Subgroup.le_normalizer hs) (hSN hs)
  have hdich : ∀ s ∈ S,
      (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = D.cutsOf K) ∨
      (∀ K : Subgroup A, B ≤ K → K ≤ L →
        D.cutsOf (conjSub s K) = flipNodes 4 (D.cutsOf K)) :=
    fun s hs => D.cutsOf_conj_dichotomy (by norm_num) s (hSN hs) (hk s hs _)
      (hk s⁻¹ (S.inv_mem hs) _) (zl_conjSub_eq (hSB s hs))
  have hinv : ∀ K : Subgroup A, B ≤ K → K ≤ L → ∀ s ∈ S,
      D.cutsOf (conjSub s K) = D.cutsOf K → s ∈ Subgroup.normalizer (K : Set A) := by
    intro K hBK hKL s hs hcut
    apply zl_mem_normalizer
    exact D.eq_of_cutsOf_eq (zl_le_conj (zl_conjSub_eq (hSB s hs)) hBK)
      (zl_conj_le (hSN hs) hKL) hBK hKL hcut
  by_contra hno
  push Not at hno
  apply hnt
  intro K hBK hKL s hs
  have hBK' : B ≤ K := by
    rw [hBdef]
    exact hBK
  rcases hdich s hs with htr | hfl
  · exact hinv K hBK' hKL s hs (htr K hBK' hKL)
  · exfalso
    obtain ⟨K', hBK'', hK'L, hne⟩ := hno s hs
    exact hne (hfl K' hBK'' hK'L)

theorem flip4_cuts_shape {L S B X : Subgroup A} {s₀ : A} (D : SurjBorel 4 L B) (hs₀ : s₀ ∈ S)
    (hfl : ∀ K : Subgroup A, B ≤ K → K ≤ L →
      D.cutsOf (conjSub s₀ K) = flipNodes 4 (D.cutsOf K))
    (hBX : B ≤ X) (hXL : X ≤ L) (hXS : S ≤ Subgroup.normalizer (X : Set A))
    (hXB : X ≠ B) (hXL' : X ≠ L) : D.cutsOf X = {2} ∨ D.cutsOf X = {1, 3} := by
  have hflip : flipNodes 4 (D.cutsOf X) = D.cutsOf X := by
    have h1 := hfl X hBX hXL
    rw [zl_conjSub_eq (hXS hs₀)] at h1
    exact h1.symm
  have hnode : ∀ i ∈ D.cutsOf X, 1 ≤ i ∧ i < 4 := fun i hi => D.isNode_of_mem_cutsOf hi
  have h13 : (1 ∈ D.cutsOf X) ↔ (3 ∈ D.cutsOf X) := by
    constructor
    · intro h
      rw [← hflip]
      exact ⟨1, h, by norm_num⟩
    · intro h
      rw [← hflip]
      exact ⟨3, h, by norm_num⟩
  have hnode' : ∀ i ∈ D.cutsOf X, i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    have := hnode i hi
    omega
  by_cases h2 : 2 ∈ D.cutsOf X
  · by_cases h1 : 1 ∈ D.cutsOf X
    · exfalso
      apply hXB
      refine D.eq_of_cutsOf_eq hBX hXL le_rfl D.le_L ?_
      rw [D.cutsOf_B]
      ext i
      constructor
      · intro hi
        exact D.isNode_of_mem_cutsOf hi
      · intro hi
        have hi' : 1 ≤ i ∧ i < 4 := hi
        rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact h13.mp h1
    · left
      ext i
      constructor
      · intro hi
        rcases hnode' i hi with rfl | rfl | rfl
        · exact absurd hi h1
        · rfl
        · exact absurd (h13.mpr hi) h1
      · intro hi
        rw [Set.mem_singleton_iff] at hi
        rw [hi]
        exact h2
  · by_cases h1 : 1 ∈ D.cutsOf X
    · right
      ext i
      constructor
      · intro hi
        rcases hnode' i hi with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact absurd hi h2
        · exact Or.inr rfl
      · intro hi
        rcases hi with rfl | rfl
        · exact h1
        · exact h13.mp h1
    · exfalso
      apply hXL'
      refine D.eq_of_cutsOf_eq hBX hXL D.le_L le_rfl ?_
      rw [D.cutsOf_L]
      ext i
      constructor
      · intro hi
        rcases hnode' i hi with rfl | rfl | rfl
        · exact absurd hi h1
        · exact absurd hi h2
        · exact absurd (h13.mpr hi) h1
      · intro hi
        exact absurd hi (Set.notMem_empty i)

theorem flip4_smin_cases {L S B K M' P : Subgroup A} {s₀ : A} (hBdef : B = S ⊓ L)
    (D : SurjBorel 4 L B) (hs₀ : s₀ ∈ S)
    (hfl : ∀ K : Subgroup A, B ≤ K → K ≤ L →
      D.cutsOf (conjSub s₀ K) = flipNodes 4 (D.cutsOf K))
    (hBK : B ≤ K) (hKL : K ≤ L) (hKS : S ≤ Subgroup.normalizer (K : Set A))
    (hKB : K ≠ B) (hKL' : K ≠ L)
    (hBM : B ≤ M') (hML : M' ≤ L) (hMS : S ≤ Subgroup.normalizer (M' : Set A))
    (hMB : M' ≠ B) (hML' : M' ≠ L) (hKM : ¬ K ≤ M') (hP : SMin L S P) :
    P = K ∨ P = M' := by
  have hBP : B ≤ P := by
    rw [hBdef]
    exact hP.sl
  have hPL : P ≤ L := hP.le
  have hPB : P ≠ B := fun h => hP.ne (by rw [← hBdef]; exact h.symm)
  have hPL' : P ≠ L := by
    intro h
    rcases hP.minimal K hKS (by rw [← hBdef]; exact hBK) (h ▸ hKL) with h1 | h1
    · exact hKB (h1.trans hBdef.symm)
    · exact hKL' (h1.trans h)
  have hsh := flip4_cuts_shape D hs₀ hfl hBP hPL hP.sP hPB hPL'
  have hshK := flip4_cuts_shape D hs₀ hfl hBK hKL hKS hKB hKL'
  have hshM := flip4_cuts_shape D hs₀ hfl hBM hML hMS hMB hML'
  have hne : D.cutsOf K ≠ D.cutsOf M' := fun h =>
    hKM (le_of_eq (D.eq_of_cutsOf_eq hBK hKL hBM hML h))
  have hcase : D.cutsOf P = D.cutsOf K ∨ D.cutsOf P = D.cutsOf M' := by
    rcases hsh with h | h <;> rcases hshK with hk | hk <;> rcases hshM with hm | hm <;>
      first
        | exact Or.inl (h.trans hk.symm)
        | exact Or.inr (h.trans hm.symm)
        | exact absurd (hk.trans hm.symm) hne
  rcases hcase with h | h
  · exact Or.inl (D.eq_of_cutsOf_eq hBP hPL hBK hKL h)
  · exact Or.inr (D.eq_of_cutsOf_eq hBP hPL hBM hML h)

end CFSG.Quasithin
