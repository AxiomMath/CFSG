module

public import CFSG.Sporadic.Recognition.LyonsLocalNormalizerE

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def NN {G : Type*} [Group G] (a b : G) : Subgroup G :=
  normalizer (zpowers a : Set G) ⊓ normalizer (zpowers b : Set G)

section Generic

variable {G : Type*} [Group G]

theorem QE_le_NN (a b : G) : QE a b ≤ NN a b := by
  intro q hq
  obtain ⟨h1, h2⟩ := mem_QE.1 hq
  have hz : ∀ c : G, c * q = q * c → q ∈ normalizer (zpowers c : Set G) := by
    intro c hc
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute c q from hc) k)).eq
  exact ⟨hz a h1, hz b h2⟩

theorem conj_eq_or_inv_of_mem_normalizer_zpowers {a n : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hn : n ∈ normalizer (zpowers a : Set G)) : n * a * n⁻¹ = a ∨ n * a * n⁻¹ = a⁻¹ := by
  have hmem : n * a * n⁻¹ ∈ zpowers a := (mem_normalizer_iff.1 hn a).1 (mem_zpowers a)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  rcases zpow_cases ha3 k with h | h | h
  · exfalso
    apply ha1
    have h1 : n * a * n⁻¹ = 1 := by rw [← hk, h]
    have h2 : a = n⁻¹ * (n * a * n⁻¹) * n := by group
    rw [h2, h1]
    group
  · left
    rw [← hk, h]
  · right
    rw [← hk, h]
    have : a ^ 2 * a = 1 := by rw [← pow_succ]; exact ha3
    exact eq_inv_of_mul_eq_one_left this

theorem mem_NN_of_conj {a b w : G} [Finite G]
    (ha : w * a * w⁻¹ = a ∨ w * a * w⁻¹ = a⁻¹) (hb : w * b * w⁻¹ = b ∨ w * b * w⁻¹ = b⁻¹) :
    w ∈ NN a b := by
  have hz : ∀ c : G, (w * c * w⁻¹ = c ∨ w * c * w⁻¹ = c⁻¹) →
      w ∈ normalizer (zpowers c : Set G) := by
    intro c hc
    rw [Subgroup.zpowers_eq_closure]
    refine McLAS.mem_normalizer_closure fun s hs => ?_
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rcases hc with hc | hc
    · rw [hc]; exact Subgroup.subset_closure rfl
    · rw [hc]; exact Subgroup.inv_mem _ (Subgroup.subset_closure rfl)
  exact ⟨hz a ha, hz b hb⟩

theorem NN_le_normalizer_EE [Finite G] (a b : G) : NN a b ≤ normalizer (EE a b : Set G) := by
  rintro n ⟨hna, hnb⟩
  refine McLAS.mem_normalizer_closure fun s hs => ?_
  have hs' : s = a ∨ s = b := by simpa using hs
  rcases hs' with rfl | rfl
  · have : n * s * n⁻¹ ∈ zpowers s := (mem_normalizer_iff.1 hna s).1 (mem_zpowers s)
    exact zpowers_le.2 (Subgroup.subset_closure (by simp)) this
  · have : n * s * n⁻¹ ∈ zpowers s := (mem_normalizer_iff.1 hnb s).1 (mem_zpowers s)
    exact zpowers_le.2 (Subgroup.subset_closure (by simp)) this

end Generic

section Edge

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem card_NN (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(NN (x₁ : G) (x₂ : G)) = 4 * Nat.card ↥(QE (x₁ : G) (x₂ : G)) := by
  classical
  let a : Fin 2 → G := ![(x₁ : G), (x₂ : G)]
  have hrange : Set.range a = {(x₁ : G), (x₂ : G)} := by
    ext g
    simp [a, or_comm]
  let ι : Fin 4 → Fin 8 := fun k => Fin.castLE (by norm_num) k
  have hι : Function.Injective ι := Fin.castLE_injective _
  let gT : Fin 4 → (Fin 2 → G) := fun k =>
    ![(e4H x₁ x₂ (iE (ι k)).1 : G), (e4H x₁ x₂ (iE (ι k)).2 : G)]
  have hgT : Function.Injective gT := by
    intro k k' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [gT, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    apply hι
    apply iE_injective
    exact Prod.ext (e4H_injective S (Subtype.val_injective h0))
      (e4H_injective S (Subtype.val_injective h1))
  let T : Finset (Fin 2 → G) := Finset.univ.image gT
  have hTcard : T.card = 4 := by
    rw [Finset.card_image_of_injective _ hgT]; simp
  have hx₁3 : (x₁ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₁
  have hx₂3 : (x₂ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₂
  have hx₁1 : (x₁ : G) ≠ 1 := by
    intro h
    have := orderOf_x₁ S
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hx₂1 : (x₂ : G) ≠ 1 := by
    intro h
    have := orderOf_x₂ S
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  choose w hwN hw using fun m => D.exists_lift_pE_normalizer S m
  have hax : ∀ k : Fin 4, ((iE (ι k)).1 = 0 ∨ (iE (ι k)).1 = 1) ∧
      ((iE (ι k)).2 = 2 ∨ (iE (ι k)).2 = 3) := by decide
  have hwNN : ∀ k : Fin 4, (w (ι k) : G) ∈ NN (x₁ : G) (x₂ : G) := by
    intro k
    obtain ⟨hk1, hk2⟩ := hax k
    refine mem_NN_of_conj ?_ ?_
    · rw [(hw (ι k)).1]
      rcases hk1 with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr (by simp [e4H])
    · rw [(hw (ι k)).2]
      rcases hk2 with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr (by simp [e4H])
  have hconj : ∀ k, (fun i => (w (ι k) : G) * a i * (w (ι k) : G)⁻¹) = gT k := by
    intro k
    funext i
    fin_cases i
    · exact (hw (ι k)).1
    · exact (hw (ι k)).2
  have hT : ∀ n ∈ NN (x₁ : G) (x₂ : G), (fun i => n * a i * n⁻¹) ∈ T := by
    intro n hn
    obtain ⟨m, hm1, hm2⟩ := D.exists_pE_of_mem_normalizer S (NN_le_normalizer_EE _ _ hn)
    have hn1 := conj_eq_or_inv_of_mem_normalizer_zpowers hx₁3 hx₁1 hn.1
    have hi : (iE m).1 = 0 ∨ (iE m).1 = 1 := by
      rcases hn1 with h | h
      · left
        apply e4H_injective S
        apply Subtype.val_injective
        rw [← hm1, h]
        rfl
      · right
        apply e4H_injective S
        apply Subtype.val_injective
        rw [← hm1, h]
        simp [e4H]
    have hfin : ∀ m : Fin 8, ((iE m).1 = 0 ∨ (iE m).1 = 1) → m.val < 4 := by decide
    have hm4 : m.val < 4 := hfin m hi
    refine Finset.mem_image.2 ⟨⟨m.val, hm4⟩, Finset.mem_univ _, ?_⟩
    funext k
    have hιm : ι ⟨m.val, hm4⟩ = m := Fin.ext rfl
    fin_cases k
    · simp only [gT, hιm]
      exact hm1.symm
    · simp only [gT, hιm]
      exact hm2.symm
  have hmain := card_eq_mul_card_of_conj_tuples (NN (x₁ : G) (x₂ : G)) a T hT hTcard
    (fun k => (w (ι k) : G)) hwNN
    (by
      intro k k' h
      apply hgT
      rw [← hconj k, ← hconj k']
      exact h)
  have hinf : NN (x₁ : G) (x₂ : G) ⊓ centralizer ({(x₁ : G), (x₂ : G)} : Set G) =
      QE (x₁ : G) (x₂ : G) := inf_eq_right.2 (QE_le_NN _ _)
  rw [hmain, hrange, hinf]

theorem card_normalizer_EE_eq_two_mul_NN (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(normalizer (EE (x₁ : G) (x₂ : G) : Set G)) =
      2 * Nat.card ↥(NN (x₁ : G) (x₂ : G)) := by
  rw [D.card_normalizer_EE S, D.card_NN S]
  ring

theorem relIndex_NN_normalizer_EE (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    (NN (x₁ : G) (x₂ : G)).relIndex (normalizer (EE (x₁ : G) (x₂ : G) : Set G)) = 2 := by
  have hle := NN_le_normalizer_EE (x₁ : G) (x₂ : G)
  have h1 := Subgroup.card_mul_index
    ((NN (x₁ : G) (x₂ : G)).subgroupOf (normalizer (EE (x₁ : G) (x₂ : G) : Set G)))
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    D.card_normalizer_EE_eq_two_mul_NN S] at h1
  have hpos : 0 < Nat.card ↥(NN (x₁ : G) (x₂ : G)) := Nat.card_pos
  have h2 : Nat.card ↥(NN (x₁ : G) (x₂ : G)) *
      ((NN (x₁ : G) (x₂ : G)).subgroupOf (normalizer (EE (x₁ : G) (x₂ : G) : Set G))).index =
      Nat.card ↥(NN (x₁ : G) (x₂ : G)) * 2 := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem conj_mem_NN_of_mem_normalizer_EE (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {n g : G}
    (hn : n ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G)) (hg : g ∈ NN (x₁ : G) (x₂ : G)) :
    n * g * n⁻¹ ∈ NN (x₁ : G) (x₂ : G) := by
  have hnormal : ((NN (x₁ : G) (x₂ : G)).subgroupOf
      (normalizer (EE (x₁ : G) (x₂ : G) : Set G))).Normal :=
    Subgroup.normal_of_index_eq_two (D.relIndex_NN_normalizer_EE S)
  have hgN : g ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G) := NN_le_normalizer_EE _ _ hg
  have := hnormal.conj_mem ⟨g, hgN⟩ hg ⟨n, hn⟩
  exact this

end LyData

end Edge

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem card_NN' (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(NN (x₁ : G) (x₂ : G)) = 349920 := by
  rw [D.card_NN S, D.card_QE S]

end LyData

end Cert

end CFSG.Sporadic.Recognition.LyonsSims
