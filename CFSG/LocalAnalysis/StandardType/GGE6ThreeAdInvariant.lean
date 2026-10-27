module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

@[expose] def ggE6CartanCol (i : Fin Tag.E6.rank) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ((Tag.E6.cartan i j : ℤ) : ZMod 3)

private theorem am_smul_mem {S : AddSubgroup (Fin Tag.E6.rank → ZMod 3)} (a : ZMod 3)
    {v : Fin Tag.E6.rank → ZMod 3} (hv : v ∈ S) : a • v ∈ S := by
  have h : a • v = a.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) a.val v, ZMod.natCast_zmod_val]
  rw [h]
  exact S.nsmul_mem hv _

private theorem am_col_mem {S : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (hS : ∀ (i : Fin Tag.E6.rank) x, x ∈ S → adRefl .E6 3 i x ∈ S)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ S) {i : Fin Tag.E6.rank} (hi : x i ≠ 0) :
    ggE6CartanCol i ∈ S := by
  have h1 : x i • ggE6CartanCol i ∈ S := by
    have h := S.sub_mem hx (hS i x hx)
    have e : x - adRefl .E6 3 i x = x i • ggE6CartanCol i := by
      simp only [adRefl, sub_sub_cancel]
      rfl
    rwa [e] at h
  rcases (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2) (x i) hi with h | h
  · simpa [h] using h1
  · rw [h] at h1
    have h3 := S.neg_mem h1
    convert h3 using 1
    funext j
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact (by decide : ∀ a : ZMod 3, a = -(2 * a)) _

private theorem am_step {S : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (hS : ∀ (i : Fin Tag.E6.rank) x, x ∈ S → adRefl .E6 3 i x ∈ S) {i j : Fin Tag.E6.rank}
    (hij : Tag.E6.cartan i j = -1) (hi : ggE6CartanCol i ∈ S) : ggE6CartanCol j ∈ S := by
  have h := S.sub_mem hi (hS j _ hi)
  have e : ggE6CartanCol i - adRefl .E6 3 j (ggE6CartanCol i) =
      -ggE6CartanCol j := by
    funext k
    simp only [adRefl, ggE6CartanCol, sub_sub_cancel, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rw [hij]
    simp
  rw [e] at h
  simpa using S.neg_mem h

private theorem am_all_cols {S : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (hS : ∀ (i : Fin Tag.E6.rank) x, x ∈ S → adRefl .E6 3 i x ∈ S) {i : Fin Tag.E6.rank}
    (hi : ggE6CartanCol i ∈ S) : ∀ j, ggE6CartanCol j ∈ S := by
  have s02 : ggE6CartanCol 0 ∈ S → ggE6CartanCol 2 ∈ S := am_step hS (by decide)
  have s20 : ggE6CartanCol 2 ∈ S → ggE6CartanCol 0 ∈ S := am_step hS (by decide)
  have s13 : ggE6CartanCol 1 ∈ S → ggE6CartanCol 3 ∈ S := am_step hS (by decide)
  have s31 : ggE6CartanCol 3 ∈ S → ggE6CartanCol 1 ∈ S := am_step hS (by decide)
  have s23 : ggE6CartanCol 2 ∈ S → ggE6CartanCol 3 ∈ S := am_step hS (by decide)
  have s32 : ggE6CartanCol 3 ∈ S → ggE6CartanCol 2 ∈ S := am_step hS (by decide)
  have s34 : ggE6CartanCol 3 ∈ S → ggE6CartanCol 4 ∈ S := am_step hS (by decide)
  have s43 : ggE6CartanCol 4 ∈ S → ggE6CartanCol 3 ∈ S := am_step hS (by decide)
  have s45 : ggE6CartanCol 4 ∈ S → ggE6CartanCol 5 ∈ S := am_step hS (by decide)
  have s54 : ggE6CartanCol 5 ∈ S → ggE6CartanCol 4 ∈ S := am_step hS (by decide)
  have h3 : ggE6CartanCol 3 ∈ S := by
    fin_cases i
    · exact s23 (s02 hi)
    · exact s13 hi
    · exact s23 hi
    · exact hi
    · exact s43 hi
    · exact s43 (s54 hi)
  have h2 := s32 h3
  have h4 := s34 h3
  have h1 := s31 h3
  have h0 := s20 h2
  have h5 := s45 h4
  intro j
  fin_cases j <;> assumption

private def am_coef (y : Fin Tag.E6.rank → ZMod 3) : Fin 6 → ZMod 3 :=
  ![2 * (y 4 - y 3 - (2 * y 1 + 2 * y 5 - 2 * y 4)) - (y 5 - y 4) - y 2,
    2 * y 1 + 2 * y 5 - 2 * y 4, y 4 - y 3 - (2 * y 1 + 2 * y 5 - 2 * y 4), y 5 - y 4, -y 5, 0]

private theorem am_decomp : ∀ y : Fin Tag.E6.rank → ZMod 3, NoOffRest.kDotP 3 y = 0 →
    y = am_coef y 0 • ggE6CartanCol 0 + am_coef y 1 • ggE6CartanCol 1 +
      am_coef y 2 • ggE6CartanCol 2 + am_coef y 3 • ggE6CartanCol 3 +
      am_coef y 4 • ggE6CartanCol 4 + am_coef y 5 • ggE6CartanCol 5 := by
  decide +kernel

theorem ggAdRefl_invariant_hypE6_le {S : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (hS : ∀ (i : Fin Tag.E6.rank) x, x ∈ S → adRefl .E6 3 i x ∈ S)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ S) (hx0 : x ≠ 0) : NoOffRest.hypE6 ≤ S := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    exact hx0 (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  have hall := am_all_cols hS (am_col_mem hS hx hi)
  intro y hy
  rw [am_decomp y (NoOffRest.mem_hypE6.mp hy)]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (am_smul_mem _ (hall 0))
    (am_smul_mem _ (hall 1))) (am_smul_mem _ (hall 2))) (am_smul_mem _ (hall 3)))
    (am_smul_mem _ (hall 4))) (am_smul_mem _ (hall 5))

section Fixed

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

private theorem am_weylAut_of_mem (h : GGE6ThreeData Z A Φ T w) {x : MulAut ↥A}
    (hx : x ∈ Subgroup.closure (Set.range h.conjAut)) : ∃ u : WeylGroup .E6, h.weylAut u = x := by
  refine Subgroup.closure_induction (p := fun x _ => ∃ u : WeylGroup .E6, h.weylAut u = x)
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, rfl⟩
    exact ⟨simple .E6 i, h.weylAut_simple i⟩
  · exact ⟨1, h.weylAut_one⟩
  · rintro x y _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, h.weylAut_mul u v⟩
  · rintro x _ ⟨u, rfl⟩
    exact ⟨u⁻¹, h.weylAut_inv u⟩

theorem GGE6ThreeData.eq_one_of_fixed_normal
    (h : GGE6ThreeData Z A Φ T w) {N' : Subgroup (MulAut ↥A)}
    (hle : N' ≤ Subgroup.closure (Set.range h.conjAut))
    (hnorm : ∀ g ∈ Subgroup.closure (Set.range h.conjAut), ∀ n ∈ N', g * n * g⁻¹ ∈ N')
    (hne : N' ≠ ⊥) {a : ↥A} (hfix : ∀ n ∈ N', n a = a) : a = 1 := by
  classical
  by_contra ha
  let Sg : AddSubgroup (Fin 6 → ZMod 3) :=
    { carrier := {v | ∃ b : ↥A, Φ b = Multiplicative.ofAdd v ∧ ∀ n ∈ N', n b = b}
      zero_mem' := ⟨1, by simp, fun n _ => map_one n⟩
      add_mem' := by
        rintro v₁ v₂ ⟨b₁, hb₁, hf₁⟩ ⟨b₂, hb₂, hf₂⟩
        exact ⟨b₁ * b₂, by rw [map_mul, hb₁, hb₂, ofAdd_add],
          fun n hn => by rw [map_mul, hf₁ n hn, hf₂ n hn]⟩
      neg_mem' := by
        rintro v ⟨b, hb, hf⟩
        exact ⟨b⁻¹, by rw [map_inv, hb]; rfl, fun n hn => by rw [map_inv, hf n hn]⟩ }
  have hinv : ∀ (i : Fin Tag.E6.rank) x, x ∈ Sg → adRefl .E6 3 i x ∈ Sg := by
    rintro i x ⟨b, hb, hf⟩
    refine ⟨h.conjAut i b, ?_, fun n hn => ?_⟩
    · apply Multiplicative.toAdd.injective
      exact (h.conjAut_apply_toAdd i b).trans
        (congrArg (adRefl .E6 3 i) (congrArg Multiplicative.toAdd hb))
    · have hρ : h.conjAut i ∈ Subgroup.closure (Set.range h.conjAut) :=
        Subgroup.subset_closure ⟨i, rfl⟩
      have hn' := hnorm (h.conjAut i)⁻¹ (Subgroup.inv_mem _ hρ) n hn
      have h2 := hf _ hn'
      simp only [inv_inv, MulAut.mul_apply, MulAut.inv_apply] at h2
      have h3 : n (h.conjAut i b) = h.conjAut i b := by
        have := congrArg (h.conjAut i) h2
        simpa using this
      exact h3
  have hav : Multiplicative.toAdd (Φ a) ∈ Sg := ⟨a, by simp, hfix⟩
  have hav0 : Multiplicative.toAdd (Φ a) ≠ 0 := by
    intro h0
    apply ha
    apply h.injective
    apply Multiplicative.toAdd.injective
    rw [h0, map_one]
    rfl
  have hhyp := ggAdRefl_invariant_hypE6_le hinv hav hav0
  apply hne
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨u, hu⟩ := am_weylAut_of_mem h (hle hn)
  have hu1 : u = 1 := by
    apply TableBExc.E6Three.eq_one_of_adAct_eq_on_hypE6
    intro x hx
    obtain ⟨b, hb, hf⟩ := hhyp hx
    have h1 := h.weylAut_act u b
    rw [hu, hf n hn, hb] at h1
    exact h1.symm
  rw [Subgroup.mem_bot, ← hu, hu1]
  exact h.weylAut_one

end Fixed

end CFSG.StandardType

end
