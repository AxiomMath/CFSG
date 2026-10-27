module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBasic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

private def six (b b₁ b₂ : G) : Fin 6 → G := ![b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹]

private def validIdx : Finset (Fin 6 × Fin 6 × Fin 6) :=
  Finset.univ.filter fun t => t.1.val / 2 ≠ t.2.1.val / 2 ∧ t.1.val / 2 ≠ t.2.2.val / 2 ∧
    t.2.1.val / 2 ≠ t.2.2.val / 2

private theorem validIdx_card : validIdx.card = 48 := by decide

private theorem six_cls {i j : Fin 6} (hij : i.val / 2 = j.val / 2) :
    six b b₁ b₂ i = six b b₁ b₂ j ∨ six b b₁ b₂ i = (six b b₁ b₂ j)⁻¹ := by
  fin_cases i <;> fin_cases j <;> simp [six] at hij ⊢

private theorem exists_idx {y : G} (hy : y ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) :
    ∃ i : Fin 6, six b b₁ b₂ i = y := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

private theorem class_ne {x y n : G} (hxy : y ∉ Subgroup.zpowers x) {i j : Fin 6}
    (hi : six b b₁ b₂ i = n * x * n⁻¹) (hj : six b b₁ b₂ j = n * y * n⁻¹) :
    i.val / 2 ≠ j.val / 2 := by
  intro hc
  apply hxy
  rcases six_cls (b := b) (b₁ := b₁) (b₂ := b₂) hc with e | e
  · have : x = y := by
      have := hi.symm.trans (e.trans hj)
      simpa using this
    rw [← this]; exact Subgroup.mem_zpowers x
  · have : x = y⁻¹ := by
      have h1 : n * x * n⁻¹ = (n * y * n⁻¹)⁻¹ := by rw [← hi, ← hj]; exact e
      have h2 : (n * y * n⁻¹)⁻¹ = n * y⁻¹ * n⁻¹ := by group
      rw [h2] at h1
      simpa using h1
    have : y = x⁻¹ := by rw [this]; simp
    rw [this]; exact inv_mem (Subgroup.mem_zpowers x)

theorem card_Nor_B_le {G : Type} [Group G] [Finite G] {b : G} {L B K : Subgroup G} {b₁ b₂ : G}
    (h : FF84Sec4 b L B K b₁ b₂) (hC : CenS B = B) : Nat.card (Nor B) ≤ 1296 := by
  classical
  have hBN : B ≤ Nor B := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]; intro y
    refine ⟨fun hy => mul_mem (mul_mem hx hy) (inv_mem hx), fun hy => ?_⟩
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    simpa [e] using mul_mem (mul_mem (inv_mem hx) hy) hx
  let H : Subgroup (Nor B) := B.subgroupOf (Nor B)
  have hcardH : Nat.card H = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv]
    simpa using card_B h
  let φ : Nor B → G × G × G := fun n =>
    ((n : G) * b * (n : G)⁻¹, (n : G) * b₁ * (n : G)⁻¹, (n : G) * b₂ * (n : G)⁻¹)
  have hcomm : ∀ c ∈ B, ∀ x ∈ B, c * x * c⁻¹ = x := fun c hc x hx => by
    have := (comm_of_mem h hc hx).eq
    rw [this]; group
  have hφ : ∀ m n : Nor B, (m⁻¹ * n) ∈ H → φ m = φ n := by
    intro m n hmn
    have hc : (m : G)⁻¹ * (n : G) ∈ B := hmn
    have key : ∀ x ∈ B, (n : G) * x * (n : G)⁻¹ = (m : G) * x * (m : G)⁻¹ := by
      intro x hx
      have := hcomm _ hc x hx
      calc (n : G) * x * (n : G)⁻¹
          = (m : G) * ((m : G)⁻¹ * (n : G) * x * ((m : G)⁻¹ * (n : G))⁻¹) * (m : G)⁻¹ := by
            group
        _ = (m : G) * x * (m : G)⁻¹ := by rw [this]
    simp only [φ, key b (mem_b h), key b₁ (mem_b₁ h), key b₂ (mem_b₂ h)]
  have hφ' : ∀ m n : Nor B, φ m = φ n → (m⁻¹ * n) ∈ H := by
    intro m n hmn
    simp only [φ, Prod.mk.injEq] at hmn
    obtain ⟨e0, e1, e2⟩ := hmn
    have cm : ∀ x : G, (m : G) * x * (m : G)⁻¹ = (n : G) * x * (n : G)⁻¹ →
        ((m : G)⁻¹ * (n : G)) * x = x * ((m : G)⁻¹ * (n : G)) := by
      intro x hx
      have : x * (m : G)⁻¹ * (n : G) = (m : G)⁻¹ * (n : G) * x := by
        have h1 : (m : G) * x * (m : G)⁻¹ * (n : G) = (n : G) * x := by
          rw [hx]; group
        calc x * (m : G)⁻¹ * (n : G) = (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹ * (n : G)) := by
              group
          _ = (m : G)⁻¹ * ((n : G) * x) := by rw [h1]
          _ = _ := by group
      simpa [mul_assoc] using this.symm
    have hmem : B ≤ Subgroup.centralizer ({(m : G)⁻¹ * (n : G)} : Set G) := by
      refine B_le_of_mem' h ?_ ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]; intro z hz
        rw [Set.mem_singleton_iff] at hz; subst hz; exact cm b e0
      · rw [Subgroup.mem_centralizer_iff]; intro z hz
        rw [Set.mem_singleton_iff] at hz; subst hz; exact cm b₁ e1
      · rw [Subgroup.mem_centralizer_iff]; intro z hz
        rw [Set.mem_singleton_iff] at hz; subst hz; exact cm b₂ e2
    have hcen : (m : G)⁻¹ * (n : G) ∈ CenS B := by
      rw [Subgroup.mem_centralizer_iff]; intro z hz
      have := Subgroup.mem_centralizer_iff.1 (hmem hz) _ (Set.mem_singleton _)
      exact this.symm
    rw [hC] at hcen
    exact hcen
  let T : Finset (G × G × G) :=
    validIdx.image fun t => (six b b₁ b₂ t.1, six b b₁ b₂ t.2.1, six b b₁ b₂ t.2.2)
  have hT : T.card ≤ 48 := by
    refine (Finset.card_image_le).trans ?_
    exact validIdx_card.le
  have hφT : ∀ n : Nor B, φ n ∈ T := by
    intro n
    have hn := h.mono.2.2.1 n n.2
    obtain ⟨i, hi⟩ := exists_idx (hn b (by simp))
    obtain ⟨j, hj⟩ := exists_idx (hn b₁ (by simp))
    obtain ⟨k, hk⟩ := exists_idx (hn b₂ (by simp))
    refine Finset.mem_image.2 ⟨(i, j, k), ?_, ?_⟩
    · simp only [validIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨class_ne (b := b) (b₁ := b₁) (b₂ := b₂) (b₁_notin_zpowers_b h) hi hj,
        class_ne (b := b) (b₁ := b₁) (b₂ := b₂) (b₂_notin_zpowers_b h) hi hk,
        class_ne (b := b) (b₁ := b₁) (b₂ := b₂) (b₂_notin_zpowers_b₁ h) hj hk⟩
    · simp only [φ, hi, hj, hk]
  let F : Nor B ⧸ H → G × G × G :=
    Quotient.lift φ (fun m n hmn => hφ m n (by
      have := (QuotientGroup.leftRel_apply (s := H)).1 hmn
      exact this))
  have hFinj : Function.Injective F := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | _ m =>
    induction q using Quotient.inductionOn with
    | _ n =>
    exact Quotient.sound ((QuotientGroup.leftRel_apply (s := H)).2 (hφ' m n hpq))
  have hrange : Set.range F ⊆ (T : Set (G × G × G)) := by
    rintro _ ⟨p, rfl⟩
    induction p using Quotient.inductionOn with
    | _ m => exact hφT m
  have key : Nat.card (Nor B ⧸ H) ≤ 48 := by
    rw [← Nat.card_range_of_injective hFinj, Nat.card_coe_set_eq]
    calc (Set.range F).ncard ≤ (T : Set (G × G × G)).ncard :=
          Set.ncard_le_ncard hrange (Finset.finite_toSet T)
      _ = T.card := Set.ncard_coe_finset T
      _ ≤ 48 := hT
  have hmul := Subgroup.card_mul_index H
  have hidx : H.index = Nat.card (Nor B ⧸ H) := rfl
  rw [hcardH, hidx] at hmul
  omega

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
