module

public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Std
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)

section Root

variable {F : Type} [Field F]

theorem cube_root_cases {ω lam : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : lam ^ 3 = 1) :
    lam = 1 ∨ lam = ω ∨ lam = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h : (lam - 1) * (lam - ω) * (lam - ω ^ 2) = 0 := by
    linear_combination h3 + (lam - lam ^ 2) * hω + (lam - 1) * hω3
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

variable [CharP F 2] {G : Type} [Group G] {g : F → G}

theorem rootFam_zero (hmul : ∀ s t, g (s + t) = g s * g t) : g 0 = 1 := by
  have h : g 0 * g 0 = g 0 * 1 := by rw [mul_one, ← hmul, add_zero]
  exact mul_left_cancel h

theorem rootFam_self (hmul : ∀ s t, g (s + t) = g s * g t) (t : F) : g t * g t = 1 := by
  rw [← hmul, CharTwo.add_self_eq_zero, rootFam_zero hmul]

theorem rootFam_comm (hmul : ∀ s t, g (s + t) = g s * g t) (s t : F) :
    g s * g t = g t * g s := by
  rw [← hmul, ← hmul, add_comm]

variable (g)

@[expose] def rootFourOf (ω : F) : Subgroup G :=
  Subgroup.closure {g 1, g ω}

variable {g}

theorem rootFourOf_spec (hmul : ∀ s t, g (s + t) = g s * g t)
    (hinj : ∀ s t, g s = g t → s = t) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    IsElemAbelian 2 (rootFourOf g ω) ∧ Nat.card (rootFourOf g ω) = 4 := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have h1 : g 1 ≠ 1 := fun e => one_ne_zero (hinj _ _ (e.trans (rootFam_zero hmul).symm))
  have h2 : g ω ≠ 1 := fun e => hω0 (hinj _ _ (e.trans (rootFam_zero hmul).symm))
  have h3 : g 1 ≠ g ω := fun e => hω1 (hinj _ _ e).symm
  exact ⟨isElemAbelian_closure_pair (rootFam_self hmul 1) (rootFam_self hmul ω)
      (rootFam_comm hmul 1 ω),
    card_closure_pair (rootFam_self hmul 1) (rootFam_self hmul ω) (rootFam_comm hmul 1 ω)
      h1 h2 h3⟩

theorem mem_rootFourOf_one (ω : F) : g 1 ∈ rootFourOf g ω :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem mem_rootFourOf_omega (ω : F) : g ω ∈ rootFourOf g ω :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem rootFourOf_normalized (hmul : ∀ s t, g (s + t) = g s * g t) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) {z : G} {l : F} (hl : l ^ 3 = 1)
    (hz : ∀ t, z * g t * z⁻¹ = g (l * t)) :
    ∀ w ∈ rootFourOf g ω, z * w * z⁻¹ ∈ rootFourOf g ω := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hsq : ω ^ 2 = 1 + ω := by
    have : ω ^ 2 = -(ω + 1) := by linear_combination hω
    rw [this, CharTwo.neg_eq, add_comm]
  have hW1 : g 1 ∈ rootFourOf g ω := mem_rootFourOf_one ω
  have hWω : g ω ∈ rootFourOf g ω := mem_rootFourOf_omega ω
  have hW1ω : g (1 + ω) ∈ rootFourOf g ω := by
    rw [hmul]; exact Subgroup.mul_mem _ hW1 hWω
  have hle : (rootFourOf g ω).map (MulAut.conj z).toMonoidHom ≤ rootFourOf g ω := by
    rw [rootFourOf, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · rw [hx]
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      rw [hz, mul_one]
      rcases cube_root_cases hω hl with e | e | e
      · rw [e]; exact hW1
      · rw [e]; exact hWω
      · rw [e, hsq]; exact hW1ω
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      rw [hz]
      rcases cube_root_cases hω hl with e | e | e
      · rw [e, one_mul]; exact hWω
      · rw [e]
        have : ω * ω = 1 + ω := by rw [← sq]; exact hsq
        rw [this]; exact hW1ω
      · rw [e]
        have : ω ^ 2 * ω = 1 := by rw [← pow_succ]; exact hω3
        rw [this]; exact hW1
  intro w hw
  exact hle ⟨w, hw, by simp [MulAut.conj_apply]⟩

theorem rootFourOf_moved (hinj : ∀ s t, g s = g t → s = t) {z : G} {l : F} (hl1 : l ≠ 1)
    (hz : ∀ t, z * g t * z⁻¹ = g (l * t)) : z * g 1 * z⁻¹ ≠ g 1 := by
  intro h
  rw [hz, mul_one] at h
  exact hl1 (hinj _ _ h)

theorem exists_four_of_root (hmul : ∀ s t, g (s + t) = g s * g t)
    (hinj : ∀ s t, g s = g t → s = t) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) {z : G}
    {l : F} (hl : l ^ 3 = 1) (hl1 : l ≠ 1) (hz : ∀ t, z * g t * z⁻¹ = g (l * t)) :
    ∃ W : Subgroup G, IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ (∀ w ∈ W, z * w * z⁻¹ ∈ W) ∧
      ∃ w ∈ W, z * w * z⁻¹ ≠ w :=
  ⟨rootFourOf g ω, (rootFourOf_spec hmul hinj hω hω1).1, (rootFourOf_spec hmul hinj hω hω1).2,
    rootFourOf_normalized hmul hω hl hz, g 1, mem_rootFourOf_one ω,
    rootFourOf_moved hinj hl1 hz⟩

end Root

end CFSG.RankThree.PartTwo.Sec21.Hering214
