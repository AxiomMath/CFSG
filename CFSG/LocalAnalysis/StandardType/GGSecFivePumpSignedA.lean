module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSignedAPath

public section

namespace CFSG.StandardType

private theorem share {k : ℕ} {γ δ : Fin k → ℤ} (h : ggDDot γ δ ≠ 0) :
    ∃ y, γ y ≠ 0 ∧ δ y ≠ 0 := by
  by_contra hno
  refine h (Finset.sum_eq_zero fun y _ => ?_)
  by_cases hy : γ y = 0
  · rw [hy, zero_mul]
  · rw [show δ y = 0 from by_contra fun hδ => hno ⟨y, hy, hδ⟩, mul_zero]

private theorem same_supp {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) {y z : Fin k} (hyz : y ≠ z) (hγy : γ y ≠ 0) (hγz : γ z ≠ 0)
    (hδy : δ y ≠ 0) (hδz : δ z ≠ 0) (h0 : ggDDot γ δ ≠ 0) : δ = γ ∨ δ = -γ := by
  rw [ggDRootSet_dot_eq hγ hyz hγy hγz] at h0
  rw [ggDRootSet_eq_single_add_single hγ hyz hγy hγz,
    ggDRootSet_eq_single_add_single hδ hyz hδy hδz]
  rcases ggDRootSet_sign hγ hγy with h1 | h1 <;> rcases ggDRootSet_sign hγ hγz with h2 | h2 <;>
    rcases ggDRootSet_sign hδ hδy with h3 | h3 <;> rcases ggDRootSet_sign hδ hδz with h4 | h4 <;>
    rw [h1, h2, h3, h4] <;> rw [h1, h2, h3, h4] at h0 <;>
    first
    | (left; rfl)
    | (right; simp only [Pi.single_neg, neg_add, neg_neg]; done)
    | (norm_num at h0)

private theorem orth_disj {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ)
    (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    {γ δ : Fin k → ℤ} (hγ : γ ∈ Φ) (hδ : δ ∈ Φ) (h0 : ggDDot γ δ = 0) (x : Fin k) :
    γ x = 0 ∨ δ x = 0 := by
  rcases ggDRootSet_orth (hΦ.1 hγ) (hΦ.1 hδ) h0 with ⟨a, b, s, hab, hs, hγ', hδ'⟩ |
    ⟨a, b, c, d, s, s', u, u', -, -, hac, had, hbc, hbd, -, -, -, -, rfl, rfl⟩
  · exfalso
    have h1 : Pi.single a 1 + Pi.single b s ∈ Φ := by
      rcases hγ' with rfl | rfl
      · exact hγ
      · simpa using hΦ.neg_mem hγ
    have h2 : Pi.single a 1 - Pi.single b s ∈ Φ := by
      rcases hδ' with rfl | rfl
      · exact hδ
      · simpa using hΦ.neg_mem hδ
    rcases hs with rfl | rfl
    · exact hss a b hab ⟨h1, h2⟩
    · rw [Pi.single_neg, ← sub_eq_add_neg] at h1
      rw [Pi.single_neg, sub_neg_eq_add] at h2
      exact hss a b hab ⟨h2, h1⟩
  · by_cases hxa : x = a
    · exact Or.inr (hxa ▸ ggDPair_apply_of_ne hac had u u')
    by_cases hxb : x = b
    · exact Or.inr (hxb ▸ ggDPair_apply_of_ne hbc hbd u u')
    exact Or.inl (ggDPair_apply_of_ne hxa hxb s s')

private theorem no_branch {k ℓ m : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ)
    (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    {N : CoxeterMatrix (Fin ℓ)} {N₀ : CoxeterMatrix (Fin m)} {e : Fin m ≃ Fin ℓ}
    (hl : ∀ i j, N.M (e i) (e j) = N₀.M i j) (η : Fin ℓ → Fin k → ℤ) (hηΦ : ∀ i, η i ∈ Φ)
    (hdot2 : ∀ i j, i ≠ j → N.M i j = 2 → ggDDot (η i) (η j) = 0)
    (hdot3 : ∀ i j, N.M i j = 3 → ggDDot (η i) (η j) ≠ 0) {u v₁ v₂ v₃ : Fin m}
    (h : N₀.M u v₁ = 3 ∧ N₀.M u v₂ = 3 ∧ N₀.M u v₃ = 3 ∧ N₀.M v₁ v₂ = 2 ∧ N₀.M v₁ v₃ = 2 ∧
      N₀.M v₂ v₃ = 2) : False := by
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := h
  have hd : ∀ {i j : Fin m} {y : Fin k}, N₀.M i j = 2 → η (e i) y ≠ 0 → η (e j) y = 0 :=
    fun {i j y} h hy => by
      have hij : e i ≠ e j := fun he => by
        rw [e.injective he, N₀.diagonal] at h
        exact absurd h (by decide)
      exact (orth_disj hΦ hss (hηΦ _) (hηΦ _) (hdot2 _ _ hij (by rw [hl, h])) y).resolve_left hy
  obtain ⟨y₁, hu₁, h₁⟩ := share (hdot3 (e u) (e v₁) (by rw [hl, h1]))
  obtain ⟨y₂, hu₂, h₂⟩ := share (hdot3 (e u) (e v₂) (by rw [hl, h2]))
  obtain ⟨y₃, hu₃, h₃⟩ := share (hdot3 (e u) (e v₃) (by rw [hl, h3]))
  have d12 : y₁ ≠ y₂ := fun h => h₂ (h ▸ hd h12 h₁)
  have d13 : y₃ ≠ y₁ := fun h => h₃ (h ▸ hd h13 h₁)
  have d23 : y₃ ≠ y₂ := fun h => h₃ (h ▸ hd h23 h₂)
  exact hu₃ (ggDRootSet_eq_zero (hΦ.1 (hηΦ _)) d12 hu₁ hu₂ d13 d23)

theorem ggDk_signedA_of_weyl {k ℓ : ℕ} {Φ : Set (Fin k → ℤ)}
    (hΦ : GGDSubsys k Φ) (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    {N : CoxeterMatrix (Fin ℓ)} (hN : GGIsWeylMatrix N) (h3 : ∀ i j, i ≠ j → N.M i j ≤ 3)
    (η : Fin ℓ → Fin k → ℤ) (hηΦ : ∀ i, η i ∈ Φ)
    (hne : ∀ i j, i ≠ j → η j ≠ η i ∧ η j ≠ -η i)
    (hdot2 : ∀ i j, i ≠ j → N.M i j = 2 → ggDDot (η i) (η j) = 0)
    (hdot3 : ∀ i j, N.M i j = 3 → ggDDot (η i) (η j) ≠ 0) (hkℓ : k ≤ ℓ + 1) :
    ℓ + 1 = k ∧ ∃ ε : Fin k → ℤ, (∀ a, ε a = 1 ∨ ε a = -1) ∧ (∀ i, ggDDot ε (η i) = 0) ∧
      ∀ a b : Fin k, a ≠ b → Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ := by
  have hl : ∀ {m : ℕ} {N₀ : CoxeterMatrix (Fin m)} {e : Fin m ≃ Fin ℓ}, N = N₀.reindex e →
      ∀ i j, N.M (e i) (e j) = N₀.M i j := fun h i j => by
    rw [h, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases hN with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ |
    ⟨e, hE⟩
  ·
    have hnℓ : n = ℓ := by simpa using Fintype.card_congr e
    have hlab : ∀ i j : Fin n, i ≠ j → N.M (e i) (e j) =
        if j.val + 1 = i.val ∨ i.val + 1 = j.val then 3 else 2 := fun i j hij => by
      rw [hl hA]
      exact if_neg hij
    let θ : ℕ → Fin k → ℤ := fun j => if h : j < n then η (e ⟨j, h⟩) else 0
    have hθ : ∀ j (h : j < n), θ j = η (e ⟨j, h⟩) := fun j h => dif_pos h
    obtain ⟨T, ε, hT, hε, hd, hP⟩ := ggDk_signedA_of_path hΦ (θ := θ)
      (fun j hj => by rw [hθ j hj]; exact hηΦ _)
      (fun j hj => by
        have hij : (⟨j, by omega⟩ : Fin n) ≠ ⟨j + 1, hj⟩ := by simp
        have h0 := hdot3 _ _ ((hlab _ _ hij).trans (if_pos (Or.inr rfl)))
        rw [hθ j (by omega), hθ (j + 1) hj]
        obtain ⟨y, hy1, hy2⟩ := share h0
        obtain ⟨z, hzy, hz⟩ := ggDRootSet_exists_ne (hΦ.1 (hηΦ _)) hy2
        refine ⟨y, z, hy1, hy2, hz, Classical.byContradiction fun hγz => ?_⟩
        rcases same_supp (hΦ.1 (hηΦ _)) (hΦ.1 (hηΦ _)) hzy.symm hy1 hγz hy2 hz h0 with h | h
        · exact (hne _ _ (e.injective.ne hij)).1 h
        · exact (hne _ _ (e.injective.ne hij)).2 h)
      (fun i j hj hij c => by
        have hij' : (⟨i, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := by
          simp only [ne_eq, Fin.mk.injEq]
          omega
        rw [hθ i (by omega), hθ j hj]
        exact orth_disj hΦ hss (hηΦ _) (hηΦ _) (hdot2 _ _ (e.injective.ne hij')
          ((hlab _ _ hij').trans (if_neg (by dsimp only; omega)))) c)
      (by omega)
    have hTk := T.card_le_univ
    rw [hT, Fintype.card_fin] at hTk
    have hTu : T = Finset.univ := T.eq_univ_of_card (by rw [hT, Fintype.card_fin]; omega)
    refine ⟨by omega, ε, hε, fun i => ?_, fun a b hab => hP a (by simp [hTu]) b (by simp [hTu]) hab⟩
    have h := hd _ (e.symm i).isLt
    rwa [hθ _ (e.symm i).isLt, Fin.eta, Equiv.apply_symm_apply] at h
  ·
    have h := h3 (e ⟨n - 1, by omega⟩) (e ⟨n - 2, by omega⟩)
      (e.injective.ne (by simp only [ne_eq, Fin.mk.injEq]; omega))
    rw [hl hB] at h
    exfalso
    simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff, and_self, true_or, ↓reduceIte] at h
    split_ifs at h <;> omega
  ·
    refine (no_branch hΦ hss (hl hD) η hηΦ hdot2 hdot3 (u := ⟨n - 3, by omega⟩)
      (v₁ := ⟨n - 4, by omega⟩) (v₂ := ⟨n - 2, by omega⟩) (v₃ := ⟨n - 1, by omega⟩) ?_).elim
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [ggCoxeterMatrixD_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> first | omega | contradiction
  all_goals first
    | exact (no_branch hΦ hss (hl hE) η hηΦ hdot2 hdot3 (u := 3) (v₁ := 1) (v₂ := 2) (v₃ := 4)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩).elim
    | exact absurd (h3 (e 1) (e 2) (e.injective.ne (by decide))) (by rw [hl hE]; decide)
    | exact absurd (h3 (e 0) (e 1) (e.injective.ne (by decide))) (by rw [hl hE]; decide)

end CFSG.StandardType

end
