module

public import CFSG.Quasithin.Recognition.F4Local

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

universe u v

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]

section Lie

variable [Finite Mb] {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z : Mb}

structure F431LieK (T M1 M2 : Subgroup Mb) (I : Finset Mb) (z : Mb) : Prop where
  sylow : IsSylowTwoOf T ⊤
  T_le₁ : T ≤ M1
  T_le₂ : T ≤ M2
  mem_T : ∀ i ∈ I, i ∈ T
  order_two : ∀ i ∈ I, orderOf i = 2
  z_mem : z ∈ I
  two_le : 2 ≤ I.card
  rep : ∀ x : Mb, orderOf x = 2 → ∃! i, i ∈ I ∧ IsConj i x
  cent : ∀ i ∈ I, Subgroup.centralizer ({i} : Set Mb) ≤ M1 ∨
    Subgroup.centralizer ({i} : Set Mb) ≤ M2
  cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1 ∨ Subgroup.centralizer ({z} : Set Mb) ≤ M2
  center_T : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ M1 ⊓ M2, m * z * m⁻¹ = w
  ag : ∀ D : Subgroup Mb, IsAGMember T D →
    Subgroup.normalizer (D : Set Mb) ≤ M1 ∨ Subgroup.normalizer (D : Set Mb) ≤ M2

variable {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431LieK.fusion_forward (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2) {i j : Mb}
    (hi : i ∈ T) (hj : j ∈ T) (hij : IsConj i j) :
    IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hij
  have hg : c * i * c⁻¹ ∈ T := by rw [hc]; exact hj
  have hg' : (c⁻¹)⁻¹ * i * c⁻¹ ∈ T := by simpa using hg
  obtain ⟨k, -, hk⟩ := fusion_transfer D.sylow D.T_le₁ D.T_le₂ D.ag (amalgamMap b1 b2)
    (b1.range ⊔ b2.range)
    (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb)
    (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb)
    (fun a ha => by
      rw [amalgamMap_of_mem₁ b1 b2 ha]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩)
    (fun a ha => by
      rw [amalgamMap_of_mem₂ b1 b2 C.agree ha]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩) hi hg'
  refine isConj_iff.mpr ⟨k⁻¹, ?_⟩
  have : (c⁻¹)⁻¹ * i * c⁻¹ = j := by simpa using hc
  rw [this] at hk
  simpa using hk

theorem F431LieK.lemma_F435 (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnf : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    {i j : Mb} (hi : i ∈ T) (hj : j ∈ T) (hio : orderOf i = 2) (hjo : orderOf j = 2) :
    IsConj i j ↔ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  refine ⟨D.fusion_forward C hi hj, fun h => ?_⟩
  obtain ⟨i₀, ⟨hi₀I, hi₀c⟩, -⟩ := D.rep i hio
  obtain ⟨j₀, ⟨hj₀I, hj₀c⟩, -⟩ := D.rep j hjo
  have h1 := D.fusion_forward C (D.mem_T i₀ hi₀I) hi hi₀c
  have h2 := D.fusion_forward C (D.mem_T j₀ hj₀I) hj hj₀c
  have h3 : IsConj (amalgamMap b1 b2 i₀) (amalgamMap b1 b2 j₀) := (h1.trans h).trans h2.symm
  have hij : i₀ = j₀ := by
    by_contra hne
    exact hnf i₀ hi₀I j₀ hj₀I hne h3
  rw [hij] at hi₀c
  exact hi₀c.symm.trans hj₀c

end Lie

end CFSG.Quasithin.H13.F431
