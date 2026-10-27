module

public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice

section Generic

variable {τ : Tag} {K : Type} [Field K]

theorem rootSL2_HSL_eq_rootDiagUnit {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (m : Fin τ.rank → ℤ)
    (hm : ∀ δ, IsRoot τ δ → 2 * iform α δ / iform α α = ∑ i, δ i * m i) (c : Kˣ) :
    rootSL2 τ K α (HSL c) = rootDiagUnit τ (fun i => c ^ m i) := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun δ hδ => ?_)
  · rw [rootSL2_HSL_hVec hα]
    exact (rootDiag_hVec _ j).symm
  · rw [rootSL2_HSL_rootVec hα hδ]
    change _ = rootDiag _ (rootVec τ K δ)
    rw [rootDiag_rootVec _ hδ]
    congr 2
    rw [hm δ hδ, rootChar, ← prod_zpow_eq_zpow_sum]
    exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, mul_comm]

theorem hm_of_check {α : Fin τ.rank → ℤ} {m : Fin τ.rank → ℤ}
    (h : ∀ l ∈ τ.artifactRoots,
      2 * iform α (toVec τ.rank l) / iform α α = ∑ i, toVec τ.rank l i * m i) :
    ∀ δ, IsRoot τ δ → 2 * iform α δ / iform α α = ∑ i, δ i * m i := by
  intro δ hδ
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hδ
  exact h l hl

end Generic

section G2Pair

variable {K : Type} [Field K]

abbrev g2v (a b : ℤ) : Fin Tag.G2.rank → ℤ := ![a, b]

@[expose] def G2SignPair (α β : Fin Tag.G2.rank → ℤ) : Prop :=
  (α = g2v 0 1 ∧ β = g2v 2 3) ∨ (α = g2v 1 0 ∧ β = g2v 1 2) ∨ (α = g2v 1 1 ∧ β = g2v 1 3)

theorem g2_isRoot_check : ∀ v ∈ [g2v 0 1, g2v 2 3, g2v 1 0, g2v 1 2, g2v 1 1, g2v 1 3],
    RootOps.isRootB Tag.G2 v = true := by
  decide +kernel

theorem g2_hm_01 : ∀ δ, IsRoot Tag.G2 δ →
    2 * iform (g2v 0 1) δ / iform (g2v 0 1) (g2v 0 1) = ∑ i, δ i * (g2v (-3) 2) i :=
  hm_of_check (by decide +kernel)

theorem g2_hm_23 : ∀ δ, IsRoot Tag.G2 δ →
    2 * iform (g2v 2 3) δ / iform (g2v 2 3) (g2v 2 3) = ∑ i, δ i * (g2v 1 0) i :=
  hm_of_check (by decide +kernel)

theorem g2_hm_10 : ∀ δ, IsRoot Tag.G2 δ →
    2 * iform (g2v 1 0) δ / iform (g2v 1 0) (g2v 1 0) = ∑ i, δ i * (g2v 2 (-1)) i :=
  hm_of_check (by decide +kernel)

theorem g2_hm_12 : ∀ δ, IsRoot Tag.G2 δ →
    2 * iform (g2v 1 2) δ / iform (g2v 1 2) (g2v 1 2) = ∑ i, δ i * (g2v 0 1) i :=
  hm_of_check (by decide +kernel)

theorem g2_hm_11 : ∀ δ, IsRoot Tag.G2 δ →
    2 * iform (g2v 1 1) δ / iform (g2v 1 1) (g2v 1 1) = ∑ i, δ i * (g2v 3 (-1)) i :=
  hm_of_check (by decide +kernel)

theorem g2_hm_13 : ∀ δ, IsRoot Tag.G2 δ →
    2 * iform (g2v 1 3) δ / iform (g2v 1 3) (g2v 1 3) = ∑ i, δ i * (g2v (-1) 1) i :=
  hm_of_check (by decide +kernel)

theorem g2_pair_isRoot {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) :
    IsRoot Tag.G2 α ∧ IsRoot Tag.G2 β := by
  have h1 := g2_isRoot_check
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h1
  obtain ⟨c01, c23, c10, c12, c11, c13⟩ := h1
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨RootOps.isRootB_iff.1 c01, RootOps.isRootB_iff.1 c23⟩
  · exact ⟨RootOps.isRootB_iff.1 c10, RootOps.isRootB_iff.1 c12⟩
  · exact ⟨RootOps.isRootB_iff.1 c11, RootOps.isRootB_iff.1 c13⟩

theorem g2_pair_orth {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) :
    iform α β = 0 ∧ RootOps.isRootB Tag.G2 (α + β) = false ∧
      RootOps.isRootB Tag.G2 (α - β) = false := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel

theorem g2_pair_commute {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) (A B : SL2 K) :
    Commute (rootSL2 Tag.G2 K α A) (rootSL2 Tag.G2 K β B) := by
  obtain ⟨hα, hβ⟩ := g2_pair_isRoot h
  obtain ⟨h0, hp, hm⟩ := g2_pair_orth h
  have hnot : ∀ {v : Fin Tag.G2.rank → ℤ}, RootOps.isRootB Tag.G2 v = false → ¬ IsRoot Tag.G2 v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  exact rootSL2_commute_of_orth hα hβ h0 (hnot hp) (hnot hm) A B

theorem g2_pair_rootDiagUnit {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β)
    (b : Fin Tag.G2.rank → Kˣ) (lam : Kˣ) (hb : rootChar b α = lam ^ 2) :
    ∃ c₁ c₂ : Kˣ, rootDiagUnit Tag.G2 b =
      rootSL2 Tag.G2 K α (HSL c₁) * rootSL2 Tag.G2 K β (HSL c₂) := by
  obtain ⟨hα, hβ⟩ := g2_pair_isRoot h
  obtain ⟨b0, b1, rfl⟩ : ∃ b0 b1 : Kˣ, b = ![b0, b1] :=
    ⟨b ⟨0, by decide⟩, b ⟨1, by decide⟩, funext fun i => by fin_cases i <;> rfl⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hb' : b1 = lam ^ 2 := by
      have h2 : (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![0, 1] : Fin 2 → ℤ) i) = lam ^ 2 := hb
      rw [Fin.prod_univ_two] at h2
      simpa using h2
    refine ⟨lam, b0 * lam ^ 3, ?_⟩
    rw [rootSL2_HSL_eq_rootDiagUnit hα (g2v (-3) 2) g2_hm_01,
      rootSL2_HSL_eq_rootDiagUnit hβ (g2v 1 0) g2_hm_23, ← rootDiagUnit_mul]
    congr 1
    have key : (![b0, b1] : Fin 2 → Kˣ) = (fun i : Fin 2 => lam ^ (![-3, 2] : Fin 2 → ℤ) i) *
        (fun i : Fin 2 => (b0 * lam ^ 3) ^ (![1, 0] : Fin 2 → ℤ) i) := by
      funext i
      fin_cases i
      · simp [zpow_neg]
      · simp [hb']
    exact key
  · have hb' : b0 = lam ^ 2 := by
      have h2 : (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![1, 0] : Fin 2 → ℤ) i) = lam ^ 2 := hb
      rw [Fin.prod_univ_two] at h2
      simpa using h2
    refine ⟨lam, b1 * lam, ?_⟩
    rw [rootSL2_HSL_eq_rootDiagUnit hα (g2v 2 (-1)) g2_hm_10,
      rootSL2_HSL_eq_rootDiagUnit hβ (g2v 0 1) g2_hm_12, ← rootDiagUnit_mul]
    congr 1
    have key : (![b0, b1] : Fin 2 → Kˣ) = (fun i : Fin 2 => lam ^ (![2, -1] : Fin 2 → ℤ) i) *
        (fun i : Fin 2 => (b1 * lam) ^ (![0, 1] : Fin 2 → ℤ) i) := by
      funext i
      fin_cases i
      · simp [hb']
      · simp [zpow_neg]
    exact key
  · have hb' : b0 * b1 = lam ^ 2 := by
      have h2 : (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![1, 1] : Fin 2 → ℤ) i) = lam ^ 2 := hb
      rw [Fin.prod_univ_two] at h2
      simpa using h2
    have hb0 : b0 = lam ^ 2 * b1⁻¹ := eq_mul_inv_of_mul_eq hb'
    refine ⟨lam, b1 * lam, ?_⟩
    rw [rootSL2_HSL_eq_rootDiagUnit hα (g2v 3 (-1)) g2_hm_11,
      rootSL2_HSL_eq_rootDiagUnit hβ (g2v (-1) 1) g2_hm_13, ← rootDiagUnit_mul]
    congr 1
    have key : (![b0, b1] : Fin 2 → Kˣ) = (fun i : Fin 2 => lam ^ (![3, -1] : Fin 2 → ℤ) i) *
        (fun i : Fin 2 => (b1 * lam) ^ (![-1, 1] : Fin 2 → ℤ) i) := by
      funext i
      fin_cases i
      · simp [zpow_neg, hb0, mul_inv_rev]
        group
      · simp [zpow_neg]
    exact key

theorem g2_pair_rootChar_sq {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β)
    (b : Fin Tag.G2.rank → Kˣ) : ∃ γ : Kˣ, rootChar b α * (rootChar b β)⁻¹ = γ ^ 2 := by
  obtain ⟨b0, b1, rfl⟩ : ∃ b0 b1 : Kˣ, b = ![b0, b1] :=
    ⟨b ⟨0, by decide⟩, b ⟨1, by decide⟩, funext fun i => by fin_cases i <;> rfl⟩
  have h0 : (b0 : K) ≠ 0 := b0.ne_zero
  have h1 : (b1 : K) ≠ 0 := b1.ne_zero
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨(b0 * b1)⁻¹, ?_⟩
    change (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![0, 1] : Fin 2 → ℤ) i) *
      (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![2, 3] : Fin 2 → ℤ) i)⁻¹ = _
    simp only [Fin.prod_univ_two]
    apply Units.ext
    simp
    field_simp
  · refine ⟨b1⁻¹, ?_⟩
    change (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![1, 0] : Fin 2 → ℤ) i) *
      (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![1, 2] : Fin 2 → ℤ) i)⁻¹ = _
    simp only [Fin.prod_univ_two]
    apply Units.ext
    simp
  · refine ⟨b1⁻¹, ?_⟩
    change (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![1, 1] : Fin 2 → ℤ) i) *
      (∏ i : Fin 2, (![b0, b1] : Fin 2 → Kˣ) i ^ (![1, 3] : Fin 2 → ℤ) i)⁻¹ = _
    simp only [Fin.prod_univ_two]
    apply Units.ext
    simp
    field_simp

theorem g2_pair_HSL_neg_one {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) :
    rootSL2 Tag.G2 K α (HSL (-1)) = rootSL2 Tag.G2 K β (HSL (-1)) := by
  obtain ⟨hα, hβ⟩ := g2_pair_isRoot h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [rootSL2_HSL_eq_rootDiagUnit hα (g2v (-3) 2) g2_hm_01,
      rootSL2_HSL_eq_rootDiagUnit hβ (g2v 1 0) g2_hm_23]
    congr 1
    funext i
    fin_cases i
    · change (-1 : Kˣ) ^ (-3 : ℤ) = (-1 : Kˣ) ^ (1 : ℤ)
      rw [Odd.neg_one_zpow (by decide), Odd.neg_one_zpow (by decide)]
    · change (-1 : Kˣ) ^ (2 : ℤ) = (-1 : Kˣ) ^ (0 : ℤ)
      rw [Even.neg_one_zpow (by decide), Even.neg_one_zpow (by decide)]
  · rw [rootSL2_HSL_eq_rootDiagUnit hα (g2v 2 (-1)) g2_hm_10,
      rootSL2_HSL_eq_rootDiagUnit hβ (g2v 0 1) g2_hm_12]
    congr 1
    funext i
    fin_cases i
    · change (-1 : Kˣ) ^ (2 : ℤ) = (-1 : Kˣ) ^ (0 : ℤ)
      rw [Even.neg_one_zpow (by decide), Even.neg_one_zpow (by decide)]
    · change (-1 : Kˣ) ^ (-1 : ℤ) = (-1 : Kˣ) ^ (1 : ℤ)
      rw [Odd.neg_one_zpow (by decide), Odd.neg_one_zpow (by decide)]
  · rw [rootSL2_HSL_eq_rootDiagUnit hα (g2v 3 (-1)) g2_hm_11,
      rootSL2_HSL_eq_rootDiagUnit hβ (g2v (-1) 1) g2_hm_13]
    congr 1
    funext i
    fin_cases i
    · change (-1 : Kˣ) ^ (3 : ℤ) = (-1 : Kˣ) ^ (-1 : ℤ)
      rw [Odd.neg_one_zpow (by decide), Odd.neg_one_zpow (by decide)]
    · change (-1 : Kˣ) ^ (-1 : ℤ) = (-1 : Kˣ) ^ (1 : ℤ)
      rw [Odd.neg_one_zpow (by decide), Odd.neg_one_zpow (by decide)]

end G2Pair

end CFSG.RankThree.PartOne
