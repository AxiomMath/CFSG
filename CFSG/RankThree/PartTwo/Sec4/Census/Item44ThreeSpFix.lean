module

public import CFSG.RankThree.SubgroupLists.SymplecticReducible

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open scoped Matrix

theorem finrank_ker_comp_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g : V →ₗ[K] V) :
    Module.finrank K (LinearMap.ker (f ∘ₗ g)) ≤
      Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.ker g) := by
  let r : LinearMap.ker (f ∘ₗ g) →ₗ[K] LinearMap.ker f :=
    g.restrict fun x hx => by simpa using hx
  have h1 := LinearMap.finrank_range_add_finrank_ker r
  have h2 : Module.finrank K (LinearMap.range r) ≤ Module.finrank K (LinearMap.ker f) :=
    Submodule.finrank_le _
  have h3 : Module.finrank K (LinearMap.ker r) ≤ Module.finrank K (LinearMap.ker g) := by
    let i : LinearMap.ker r →ₗ[K] LinearMap.ker g :=
      LinearMap.codRestrict (LinearMap.ker g)
        ((LinearMap.ker (f ∘ₗ g)).subtype ∘ₗ (LinearMap.ker r).subtype) fun x => by
          rw [LinearMap.mem_ker]
          exact congrArg Subtype.val (LinearMap.map_coe_ker r x)
    refine LinearMap.finrank_le_finrank_of_injective (f := i) fun a b hab => ?_
    have := congrArg Subtype.val hab
    simp only [i, LinearMap.codRestrict_apply, LinearMap.comp_apply,
      Submodule.coe_subtype] at this
    exact Subtype.ext (Subtype.ext this)
  omega

theorem exists_mem_linearIndependent_pair {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {P : Submodule K V} (hP : 2 ≤ Module.finrank K P) {x : V}
    (hx : x ≠ 0) : ∃ y ∈ P, LinearIndependent K ![y, x] := by
  have hle : ¬ P ≤ K ∙ x := fun h => by
    have := Submodule.finrank_mono h
    rw [finrank_span_singleton hx] at this
    omega
  obtain ⟨y, hyP, hy⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  refine ⟨y, hyP, linearIndependent_fin2.mpr ⟨by simpa using hx, fun a ha => hy ?_⟩⟩
  exact Submodule.mem_span_singleton.mpr ⟨a, by simpa using ha⟩

theorem spForm_sub_one_mulVec_eq_zero {n : ℕ} {K : Type} [Field K] {g : GL (Fin n ⊕ Fin n) K}
    (hg : g ∈ StatedSp n K) {w : Fin n ⊕ Fin n → K}
    (hw : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w = w) (x : Fin n ⊕ Fin n → K) :
    spForm n K w (((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ x) = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, sub_eq_zero]
  conv_lhs => rw [← hw]
  exact spForm_mulVec hg w x

theorem exists_fixed_isotropic_pair {g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)}
    (hg : g ∈ StatedSp 2 (ZMod 3)) (h3 : g ^ 3 = 1) :
    ∃ u v : Fin 2 ⊕ Fin 2 → ZMod 3, LinearIndependent (ZMod 3) ![u, v] ∧
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) *ᵥ u = u ∧
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) *ᵥ v = v ∧
      spForm 2 (ZMod 3) u v = 0 := by
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))
  have hN3 : (M - 1) ^ 3 = 0 := by
    have h := congrArg Units.val h3
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [sub_pow_char_of_commute 3 (Commute.one_right M), h, one_pow, sub_self]
  have hN : ∀ v, (M - 1) *ᵥ v = M *ᵥ v - v := fun v => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  by_cases hall : ∀ x, M *ᵥ x = x
  ·
    have he : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → ZMod 3) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl 0)
      simp at this
    obtain ⟨y, hy, hli⟩ := exists_mem_linearIndependent_pair
      (P := orth ((ZMod 3) ∙ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → ZMod 3)))
      (by rw [finrank_orth, finrank_span_singleton he]; norm_num) he
    exact ⟨y, Pi.single (Sum.inl 0) 1, hli, hall y, hall _,
      spForm_isRefl _ _ (mem_orth.mp hy _ (Submodule.mem_span_singleton_self _))⟩
  ·
    push Not at hall
    obtain ⟨x, hx⟩ := hall
    obtain ⟨z, hz0, hz1⟩ : ∃ z, (M - 1) *ᵥ z ≠ 0 ∧ (M - 1) *ᵥ ((M - 1) *ᵥ z) = 0 := by
      by_cases hxx : (M - 1) *ᵥ ((M - 1) *ᵥ x) = 0
      · exact ⟨x, by rw [hN, sub_ne_zero]; exact hx, hxx⟩
      · refine ⟨(M - 1) *ᵥ x, hxx, ?_⟩
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', hN3, Matrix.zero_mulVec]
    set T : Module.End (ZMod 3) (Fin 2 ⊕ Fin 2 → ZMod 3) := Matrix.toLin' (M - 1) with hT
    have hT3 : LinearMap.ker (T ∘ₗ (T ∘ₗ T)) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply, hT, Matrix.toLin'_apply,
        Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← pow_three', hN3, Matrix.zero_mulVec]
    have hW2 : 2 ≤ Module.finrank (ZMod 3) (LinearMap.ker T) := by
      have h1 := finrank_ker_comp_le T (T ∘ₗ T)
      have h2 := finrank_ker_comp_le T T
      rw [hT3, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
      simp only [Fintype.card_sum, Fintype.card_fin] at h1
      omega
    obtain ⟨y, hy, hli⟩ := exists_mem_linearIndependent_pair hW2 hz0
    have hy' : M *ᵥ y = y := by
      rw [LinearMap.mem_ker, hT, Matrix.toLin'_apply, hN, sub_eq_zero] at hy
      exact hy
    refine ⟨y, (M - 1) *ᵥ z, hli, hy', ?_, spForm_sub_one_mulVec_eq_zero hg hy' z⟩
    rw [← sub_eq_zero, ← hN]
    exact hz1

end CFSG.RankThree.PartTwo.Sec4.Census
