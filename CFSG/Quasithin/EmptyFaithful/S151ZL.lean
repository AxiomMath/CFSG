module

public import CFSG.Quasithin.EmptyFaithful.S151ZK
public import CFSG.Quasithin.EmptyFaithful.S151ZE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc

variable {A : Type} [Group A]

theorem zl_conjSub_eq {K : Subgroup A} {s : A} (hs : s ∈ Subgroup.normalizer (K : Set A)) :
    conjSub s K = K := by
  ext x
  rw [mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hs) x
  simpa using this.symm

theorem zl_mem_normalizer {K : Subgroup A} {s : A} (h : conjSub s K = K) :
    s ∈ Subgroup.normalizer (K : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have : s * x * s⁻¹ ∈ conjSub s K ↔ s⁻¹ * (s * x * s⁻¹) * s ∈ K := mem_conjSub
  rw [h] at this
  simpa [mul_assoc] using this.symm

theorem zl_conj_le {L K : Subgroup A} {s : A} (hs : s ∈ Subgroup.normalizer (L : Set A))
    (hKL : K ≤ L) : conjSub s K ≤ L := by
  intro x hx
  rw [mem_conjSub] at hx
  have h1 := hKL hx
  have := (Subgroup.mem_normalizer_iff.mp hs _).mp h1
  simpa [mul_assoc] using this

theorem zl_le_conj {B K : Subgroup A} {s : A} (hBs : conjSub s B = B) (hBK : B ≤ K) :
    B ≤ conjSub s K := by
  intro x hx
  rw [mem_conjSub]
  have : x ∈ conjSub s B := by rw [hBs]; exact hx
  rw [mem_conjSub] at this
  exact hBK this

theorem zl_theta_mem_pCore {L : Subgroup A} {s : A} (hs : s ∈ Subgroup.normalizer (L : Set A))
    {x : ↥L} (hx : x ∈ CFSG.pCore 2 ↥L) :
    L.normalizerMonoidHom ⟨s, hs⟩ x ∈ CFSG.pCore 2 ↥L := by
  have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (L.normalizerMonoidHom ⟨s, hs⟩)
  rw [← h]
  exact Subgroup.mem_map_of_mem _ hx

theorem flip_diff_pair {n i : ℕ} (hi : IsNode n i) :
    flipNodes n ({j | IsNode n j} \ {i, n - i}) = {j | IsNode n j} \ {i, n - i} := by
  obtain ⟨hi1, hi2⟩ := hi
  ext j
  constructor
  · rintro ⟨i', ⟨⟨hj1, hj2⟩, hne⟩, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
      IsNode]
    omega
  · rintro ⟨⟨hj1, hj2⟩, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    refine ⟨n - j, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    omega

theorem gen_core [Finite A] {L S B : Subgroup A} {n : ℕ} (hBdef : B = S ⊓ L) (hn3 : 3 ≤ n)
    (D : SurjBorel n L B) (hSN : S ≤ Subgroup.normalizer (L : Set A))
    (hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set A), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (Q : Subgroup A) (hQ : ∀ P : Subgroup A, SMin L S P → P ≤ Q) : L ≤ Q := by
  classical
  have hBL : B ≤ L := hBdef ▸ inf_le_right
  have hSB : ∀ s ∈ S, s ∈ Subgroup.normalizer (B : Set A) := fun s hs => by
    rw [hBdef]
    exact zb_mem_normalizer_inf (Subgroup.le_normalizer hs) (hSN hs)
  have hdich : ∀ s ∈ S,
      (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = D.cutsOf K) ∨
      (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = flipNodes n (D.cutsOf K)) :=
    fun s hs => D.cutsOf_conj_dichotomy hn3 s (hSN hs) (hk s hs _) (hk s⁻¹ (S.inv_mem hs) _)
      (zl_conjSub_eq (hSB s hs))
  have hinv : ∀ K : Subgroup A, B ≤ K → K ≤ L → ∀ s ∈ S,
      D.cutsOf (conjSub s K) = D.cutsOf K → s ∈ Subgroup.normalizer (K : Set A) := by
    intro K hBK hKL s hs hcut
    apply zl_mem_normalizer
    exact D.eq_of_cutsOf_eq (zl_le_conj (zl_conjSub_eq (hSB s hs)) hBK)
      (zl_conj_le (hSN hs) hKL) hBK hKL hcut
  have key : ∀ Oset : ℕ → Set ℕ,
      (∀ i, IsNode n i → i ∈ Oset i ∧ ∀ j ∈ Oset i, IsNode n j) →
      (∀ i, IsNode n i → ∀ s ∈ S,
        (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = flipNodes n (D.cutsOf K)) →
          flipNodes n ({j | IsNode n j} \ Oset i) = {j | IsNode n j} \ Oset i) →
      (∀ i, IsNode n i → ∀ K : Subgroup A, B ≤ K → K ≤ L → S ≤ Subgroup.normalizer (K : Set A) →
        {j | IsNode n j} \ Oset i ⊆ D.cutsOf K →
          D.cutsOf K = {j | IsNode n j} \ Oset i ∨ D.cutsOf K = {j | IsNode n j}) →
      L ≤ Q := by
    intro Oset hO1 hO2 hO3
    have hP : ∀ i, IsNode n i → ∃ P : Subgroup A, B ≤ P ∧ P ≤ L ∧
        D.cutsOf P = {j | IsNode n j} \ Oset i :=
      fun i _ => D.exists_cutsOf_eq (fun j hj => hj.1)
    have hSMin : ∀ i, IsNode n i → ∀ P : Subgroup A, B ≤ P → P ≤ L →
        D.cutsOf P = {j | IsNode n j} \ Oset i → SMin L S P := by
      intro i hi P hBP hPL hcut
      have hSP : S ≤ Subgroup.normalizer (P : Set A) := by
        intro s hs
        apply hinv P hBP hPL s hs
        rcases hdich s hs with hid | hfl
        · exact hid P hBP hPL
        · rw [hfl P hBP hPL, hcut]
          exact hO2 i hi s hs hfl
      refine ⟨hPL, hBdef ▸ hBP, ?_, hSP, ?_⟩
      · intro hBeq
        have h1 : D.cutsOf B = D.cutsOf P := congrArg D.cutsOf (hBdef.trans hBeq)
        rw [D.cutsOf_B, hcut] at h1
        have hi' : i ∈ {j | IsNode n j} := hi
        rw [h1] at hi'
        exact hi'.2 (hO1 i hi).1
      · intro K hKS hBK hKP
        rw [← hBdef] at hBK ⊢
        have hKL : K ≤ L := hKP.trans hPL
        have hsub : D.cutsOf P ⊆ D.cutsOf K := (D.cutsOf_le_iff hBK hKL hBP).1 hKP
        rcases hO3 i hi K hBK hKL hKS (by rw [← hcut]; exact hsub) with h | h
        · right
          exact D.eq_of_cutsOf_eq hBK hKL hBP hPL (h.trans hcut.symm)
        · left
          exact D.eq_of_cutsOf_eq hBK hKL le_rfl hBL (by rw [h, D.cutsOf_B])
    have hn1 : IsNode n 1 := ⟨le_rfl, by omega⟩
    obtain ⟨P₁, hBP₁, hP₁L, hc₁⟩ := hP 1 hn1
    have hBQ : B ≤ Q := hBP₁.trans (hQ P₁ (hSMin 1 hn1 P₁ hBP₁ hP₁L hc₁))
    have hBR : B ≤ Q ⊓ L := le_inf hBQ hBL
    have hcutsR : D.cutsOf (Q ⊓ L) = ∅ := by
      ext j
      constructor
      · intro hj
        have hjn := D.isNode_of_mem_cutsOf hj
        obtain ⟨P, hBP, hPL, hc⟩ := hP j hjn
        have hPQ : P ≤ Q := hQ P (hSMin j hjn P hBP hPL hc)
        have hsub := (D.cutsOf_le_iff hBP hPL hBR).1 (le_inf hPQ hPL)
        rw [hc] at hsub
        exact absurd (hO1 j hjn).1 (hsub hj).2
      · intro h
        exact absurd h (Set.notMem_empty j)
    have hRL : Q ⊓ L = L :=
      D.eq_of_cutsOf_eq hBR inf_le_right hBL le_rfl (by rw [hcutsR, D.cutsOf_L])
    rw [← hRL]
    exact inf_le_left
  by_cases hfl : ∃ s ∈ S,
      ∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = flipNodes n (D.cutsOf K)
  ·
    obtain ⟨s₀, hs₀, hfl₀⟩ := hfl
    refine key (fun i => {i, n - i}) ?_ ?_ ?_
    · intro i hi
      refine ⟨Set.mem_insert _ _, ?_⟩
      rintro j (rfl | rfl)
      · exact hi
      · exact isNode_flip hi
    · intro i hi _ _ _
      exact flip_diff_pair hi
    · intro i hi K hBK hKL hKS hsub
      have hKfl : D.cutsOf K = flipNodes n (D.cutsOf K) := by
        rw [← hfl₀ K hBK hKL, zl_conjSub_eq (hKS hs₀)]
      obtain ⟨hi1, hi2⟩ := hi
      by_cases hsubO : D.cutsOf K ⊆ {j | IsNode n j} \ {i, n - i}
      · exact Or.inl (Set.Subset.antisymm hsubO hsub)
      · right
        obtain ⟨j, hjK, hjO⟩ := Set.not_subset.mp hsubO
        have hjn := D.isNode_of_mem_cutsOf hjK
        have hjO' : j = i ∨ j = n - i := by
          by_contra hcon
          push Not at hcon
          exact hjO ⟨hjn, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact hcon⟩
        have hboth : i ∈ D.cutsOf K ∧ n - i ∈ D.cutsOf K := by
          rcases hjO' with rfl | rfl
          · refine ⟨hjK, ?_⟩
            have : n - j ∈ flipNodes n (D.cutsOf K) := ⟨j, hjK, rfl⟩
            rwa [← hKfl] at this
          · refine ⟨?_, hjK⟩
            have : n - (n - i) ∈ flipNodes n (D.cutsOf K) := ⟨n - i, hjK, rfl⟩
            rw [← hKfl] at this
            have e : n - (n - i) = i := by omega
            rwa [e] at this
        ext j'
        constructor
        · exact fun h => D.isNode_of_mem_cutsOf h
        · intro hj'
          by_cases hjO2 : j' = i ∨ j' = n - i
          · rcases hjO2 with rfl | rfl
            · exact hboth.1
            · exact hboth.2
          · apply hsub
            refine ⟨hj', ?_⟩
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            push Not at hjO2
            exact hjO2
  ·
    push Not at hfl
    refine key (fun i => {i}) ?_ ?_ ?_
    · intro i hi
      refine ⟨Set.mem_singleton _, ?_⟩
      rintro j rfl
      exact hi
    · intro i hi s hs hflip
      obtain ⟨K, hBK, hKL, hne⟩ := hfl s hs
      exact absurd (hflip K hBK hKL) hne
    · intro i hi K hBK hKL hKS hsub
      by_cases hiK : i ∈ D.cutsOf K
      · right
        ext j
        constructor
        · exact fun h => D.isNode_of_mem_cutsOf h
        · intro hj
          by_cases hji : j = i
          · rw [hji]
            exact hiK
          · apply hsub
            exact ⟨hj, by simpa using hji⟩
      · left
        apply Set.Subset.antisymm _ hsub
        intro j hj
        refine ⟨D.isNode_of_mem_cutsOf hj, ?_⟩
        intro hji
        rw [Set.mem_singleton_iff] at hji
        rw [hji] at hj
        exact hiK hj

theorem input15122L45Gen_holds : Input15122L45Gen := by
  intro G _ _ L S htype hS2 hSN hsyl Q hQ
  obtain ⟨n, hn, hnp⟩ : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      IsPSL n 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases htype with h | h
    · exact ⟨4, Or.inl rfl, h⟩
    · exact ⟨5, Or.inr rfl, h⟩
  obtain ⟨D, hker⟩ := exists_surjBorel (n := n) (by omega) hnp hsyl
  refine gen_core rfl (by omega) D hSN ?_ Q hQ
  intro s hs hsN x hx
  have hxK : x ∈ CFSG.pCore 2 ↥L := by
    rw [← hker]
    exact hx
  have h := zl_theta_mem_pCore hsN hxK
  rw [← hker] at h
  exact h

end CFSG.Quasithin
