module

public import CFSG.Sporadic.Recognition.LyonsAS44Classes
public import CFSG.Sporadic.Recognition.LyonsAS44ClosureCard
public import CFSG.Sporadic.Recognition.LyonsAS44Geom
public import CFSG.Sporadic.Recognition.LyonsAS44R

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS
open CFSG.Semidihedral.GL2Recognition.SharpFourM11

section Classes2

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

namespace LyData

variable (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)

include D S F

theorem card_closure_triple_SG {u v w : G}
    (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hv : v ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) v)
    (hw : w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w)
    (huv : v ≠ u ∧ v ≠ u⁻¹) (huw : w ≠ u ∧ w ≠ u⁻¹) (hvw : w ≠ v ∧ w ≠ v⁻¹) :
    Nat.card ↥(closure ({u, v, w} : Set G)) = 27 := by
  obtain ⟨k, hk1, hk2, hk3⟩ := D.exists_conj_triple S F hu hv hw huv huw hvw
  rw [← card_closure_conj_image ({u, v, w} : Set G) (k : G)]
  have hset : (fun y => (k : G) * y * (k : G)⁻¹) '' ({u, v, w} : Set G) =
      {(k : G) * u * (k : G)⁻¹, (k : G) * v * (k : G)⁻¹, (k : G) * w * (k : G)⁻¹} := by
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [hset]
  have hcl : closure ({(k : G) * u * (k : G)⁻¹, (k : G) * v * (k : G)⁻¹,
      (k : G) * w * (k : G)⁻¹} : Set G) = closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) := by
    apply closure_eq_closure_of_mem_or_inv
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨x₁, by simp, hk1⟩
      · exact ⟨x₂, by simp, hk2⟩
      · exact ⟨x₃, by simp, hk3⟩
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · refine ⟨(k : G) * u * (k : G)⁻¹, by simp, ?_⟩
        rcases hk1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, inv_inv])
      · refine ⟨(k : G) * v * (k : G)⁻¹, by simp, ?_⟩
        rcases hk2 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, inv_inv])
      · refine ⟨(k : G) * w * (k : G)⁻¹, by simp, ?_⟩
        rcases hk3 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, inv_inv])
  rw [hcl]
  exact D.card_closure_three S

theorem card_closure_four_SG {u v w x : G}
    (hu : u ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) u)
    (hv : v ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) v)
    (hw : w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w)
    (hx : x ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) x)
    (huv : v ≠ u ∧ v ≠ u⁻¹) (huw : w ≠ u ∧ w ≠ u⁻¹) (hvw : w ≠ v ∧ w ≠ v⁻¹)
    (hux : x ≠ u ∧ x ≠ u⁻¹) (hvx : x ≠ v ∧ x ≠ v⁻¹) (hwx : x ≠ w ∧ x ≠ w⁻¹) :
    Nat.card ↥(closure ({u, v, w, x} : Set G)) = 81 := by
  obtain ⟨w₄, hw₄, h41, h42, h43⟩ := D.exists_fourth S F
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
    D.exists_conj_quad S F hu hv hw hx hw₄ huv huw hvw hux hvx hwx h41 h42 h43
  rw [← card_closure_conj_image ({u, v, w, x} : Set G) (k : G)]
  have hset : (fun y => (k : G) * y * (k : G)⁻¹) '' ({u, v, w, x} : Set G) =
      {(k : G) * u * (k : G)⁻¹, (k : G) * v * (k : G)⁻¹, (k : G) * w * (k : G)⁻¹,
        (k : G) * x * (k : G)⁻¹} := by
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [hset]
  have hcl : closure ({(k : G) * u * (k : G)⁻¹, (k : G) * v * (k : G)⁻¹,
      (k : G) * w * (k : G)⁻¹, (k : G) * x * (k : G)⁻¹} : Set G) =
      closure ({(x₁ : G), (x₂ : G), (x₃ : G), w₄} : Set G) := by
    apply closure_eq_closure_of_mem_or_inv
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨x₁, by simp, hk1⟩
      · exact ⟨x₂, by simp, hk2⟩
      · exact ⟨x₃, by simp, hk3⟩
      · exact ⟨w₄, by simp, hk4⟩
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · refine ⟨(k : G) * u * (k : G)⁻¹, by simp, ?_⟩
        rcases hk1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, inv_inv])
      · refine ⟨(k : G) * v * (k : G)⁻¹, by simp, ?_⟩
        rcases hk2 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, inv_inv])
      · refine ⟨(k : G) * w * (k : G)⁻¹, by simp, ?_⟩
        rcases hk3 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, inv_inv])
      · refine ⟨(k : G) * x * (k : G)⁻¹, by simp, ?_⟩
        rcases hk4 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, inv_inv])
  rw [hcl]
  have hA3 : closure ({(x₁ : G), (x₂ : G), (x₃ : G), w₄} : Set G) =
      closure (((closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) : Subgroup G) : Set G) ∪
        {w₄}) := by
    apply le_antisymm
    · apply (closure_le _).2
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact subset_closure (Or.inl (subset_closure (by simp)))
      · exact subset_closure (Or.inl (subset_closure (by simp)))
      · exact subset_closure (Or.inl (subset_closure (by simp)))
      · exact subset_closure (Or.inr rfl)
    · apply (closure_le _).2
      rintro g (hg | rfl)
      · exact (closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
          Set.mem_singleton_iff] at hy ⊢; tauto) : closure ({(x₁ : G), (x₂ : G), (x₃ : G)} :
            Set G) ≤ closure ({(x₁ : G), (x₂ : G), (x₃ : G), w₄} : Set G)) hg
      · exact subset_closure (by simp)
  rw [hA3]
  have hw₄3 : w₄ ^ 3 = 1 := pow_three_of_isConj_x₁ S hw₄.2
  have hA3le : closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) ≤ preimQ (x₁ : G) A :=
    D.A3_le_AG S F
  have hw₄B : w₄ ∉ closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) := by
    intro hmem
    rcases D.eq_of_isConj_mem_closure_three S hmem hw₄.2 with h | h | h | h | h | h
    · exact h41.1 h
    · exact h41.2 h
    · exact h42.1 h
    · exact h42.2 h
    · exact h43.1 h
    · exact h43.2 h
  have hcomm : ∀ b ∈ closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G), b * w₄ = w₄ * b :=
    fun b hb => D.AG_comm S F b (hA3le hb) w₄ hw₄.1
  rw [card_closure_union_singleton_eq_three_mul hw₄3 hw₄B hcomm, D.card_closure_three S]


theorem isConj_of_mem_AG {z : G} (hz : z ∈ preimQ (x₁ : G) A) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    IsConj z (x₁ : G) ∨ IsConj z ((x₁ : G) * (x₂ : G)) := by
  by_cases hS : IsConj (x₁ : G) z
  · exact Or.inl hS.symm
  · right
    have hS1 : (1 : G) ∉ {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} :=
      fun h => ne_one_of_mem_SG S h rfl
    have hSinv : ∀ u ∈ {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w},
        u⁻¹ ∈ {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} := fun u hu =>
      ⟨Subgroup.inv_mem _ hu.1, isConj_inv_of_isConj hu.2 (D.isConj_x₁_inv S F)⟩
    obtain ⟨u, hu, v, hv, h1, h2, rfl⟩ := exists_mul_of_not_mem_of_independent
      (A := preimQ (x₁ : G) A) (S := {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w})
      (D.AG_comm S F) (D.AG_pow_three S F) (D.card_AG S F) (fun w hw => hw.1) hS1 hSinv
      (D.ncard_SG S F)
      (fun u hu v hv w hw h1 h2 h3 h4 h5 h6 =>
        D.card_closure_triple_SG S F hu hv hw ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨h5, h6⟩)
      (fun u hu v hv w hw x hx h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
        D.card_closure_four_SG S F hu hv hw hx ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨h5, h6⟩ ⟨h7, h8⟩ ⟨h9, h10⟩
          ⟨h11, h12⟩) z hz hz1 (fun h => hS h.2)
    exact D.isConj_x₁_mul_x₂_of_mul S F hu hv h1 h2

omit [Finite G] in
theorem exists_conj_mem_AG_of_mem_RG {w : G} (hw : w ∈ preimQ (x₁ : G) R) (hw3 : w ^ 3 = 1) :
    ∃ w' ∈ preimQ (x₁ : G) A, IsConj w w' := by
  obtain ⟨hwM, hwq⟩ := mem_preimQ.1 hw
  by_cases h1 : projQ (x₁ : G) ⟨w, hwM⟩ = 1
  · have hker : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈ (projQ (x₁ : G)).ker := h1
    rw [ker_projQ] at hker
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hker
    have hwj : w = (x₁ : G) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    refine ⟨w, ?_, IsConj.refl _⟩
    rw [hwj]
    exact Subgroup.zpow_mem _ (x_mem_preimQ A) j
  · have hq3 : projQ (x₁ : G) ⟨w, hwM⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hw3)
      rw [this, map_one]
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord : orderOf (projQ (x₁ : G) ⟨w, hwM⟩) = 3 := orderOf_eq_prime hq3 h1
    have hx₁k : ∀ k : ℤ, (x₁ : G) ^ k ∈ preimQ (x₁ : G) A := fun k =>
      Subgroup.zpow_mem _ (x_mem_preimQ A) k
    rcases F.classes _ hord with hy | hy
    · obtain ⟨m, k, hmk⟩ := exists_lift_conj (u := ⟨w, hwM⟩) (v := D.x₂M S) (by
        exact hy.symm)
      refine ⟨(x₂ : G) * (x₁ : G) ^ k, Subgroup.mul_mem _ (D.x₂_mem_AG S F) (hx₁k k), ?_⟩
      refine isConj_iff.2 ⟨(m : G)⁻¹, ?_⟩
      have hmk' : w = (m : G) * ((x₂ : G) * (x₁ : G) ^ k) * (m : G)⁻¹ := hmk
      rw [hmk']
      group
    · let v : ↥(centralizer ({(x₁ : G)} : Set G)) := D.x₂M S * D.x₃M S
      have hpv : projQ (x₁ : G) v = D.x₂Q S * D.x₃Q S := by
        rw [map_mul]; rfl
      obtain ⟨m, k, hmk⟩ := exists_lift_conj (u := ⟨w, hwM⟩) (v := v) (by
        rw [hpv]; exact hy.symm)
      refine ⟨(x₂ : G) * (x₃ : G) * (x₁ : G) ^ k,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (D.x₂_mem_AG S F) (D.x₃_mem_AG S F)) (hx₁k k), ?_⟩
      refine isConj_iff.2 ⟨(m : G)⁻¹, ?_⟩
      have hmk' : w = (m : G) * ((x₂ : G) * (x₃ : G) * (x₁ : G) ^ k) * (m : G)⁻¹ := hmk
      rw [hmk']
      group

omit [Finite G] D S F in
theorem isConj_pow_three {a b : G} (h : IsConj a b) (ha : a ^ 3 = 1) : b ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [conj_pow, ha]
  group

omit [Finite G] D S F in
theorem isConj_ne_one {a b : G} (h : IsConj a b) (ha : a ≠ 1) : b ≠ 1 := by
  intro hb
  rw [hb] at h
  exact ha (isConj_one_right.1 h.symm)

theorem two_classes :
    (∀ g : G, orderOf g = 3 → IsConj g (x₁ : G) ∨ IsConj g ((x₁ : G) * (x₂ : G))) ∧
      ¬ IsConj (x₁ : G) ((x₁ : G) * (x₂ : G)) := by
  refine ⟨?_, (D.lemma42 S.pow₁ S.pow₂ S.pow₃ S.rho₁ S.rho₂ S.rho₃).1⟩
  intro g hg
  have hg3 : g ^ 3 = 1 := by simpa [hg] using pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hv : IsPGroup 3 ↥(zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow (preimQ (x₁ : G) T) (D.card_TG_eq S F) hv
  have hcw : IsConj g (c⁻¹ * g * c) := isConj_iff.2 ⟨c⁻¹, by simp⟩
  have hw3 : (c⁻¹ * g * c) ^ 3 = 1 := isConj_pow_three hcw hg3
  have hw1 : c⁻¹ * g * c ≠ 1 := isConj_ne_one hcw hg1
  have hword : orderOf (c⁻¹ * g * c) = 3 := orderOf_eq_prime hw3 hw1
  rcases D.mem_RG_or_AG_of_orderOf_three S F hc hword with h | h
  · obtain ⟨w', hw', hww'⟩ := D.exists_conj_mem_AG_of_mem_RG S F h hw3
    have hw'3 : w' ^ 3 = 1 := isConj_pow_three hww' hw3
    have hw'1 : w' ≠ 1 := isConj_ne_one hww' hw1
    rcases D.isConj_of_mem_AG S F hw' hw'3 hw'1 with h' | h'
    · exact Or.inl (hcw.trans (hww'.trans h'))
    · exact Or.inr (hcw.trans (hww'.trans h'))
  · rcases D.isConj_of_mem_AG S F h hw3 hw1 with h' | h'
    · exact Or.inl (hcw.trans h')
    · exact Or.inr (hcw.trans h')

end LyData

end Classes2

end CFSG.Sporadic.Recognition.LyonsSims
