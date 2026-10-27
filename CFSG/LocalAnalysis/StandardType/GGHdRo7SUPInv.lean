module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULinDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7SUPInvAux_coord_equiv {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (σ : Equiv.Perm (Fin m)) (w : V) (j : Fin m) :
    b.coord j ((b.equiv b σ) w) = b.coord (σ.symm j) w := by
  have h : (b.coord j).comp ((b.equiv b σ).toLinearMap) = b.coord (σ.symm j) := by
    refine b.ext (fun i => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    by_cases hij : σ i = j
    · have hji : i = σ.symm j := by rw [← hij, Equiv.symm_apply_apply]
      simp [hij, hji]
    · have hji : i ≠ σ.symm j := by
        intro h'
        exact hij (by rw [h', Equiv.apply_symm_apply])
      simp [hij, hji]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    congrArg (fun φ : V →ₗ[ZMod p] (ZMod p) => φ w) h

private theorem hdRo7SUPInvAux_repr_equiv {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (σ : Equiv.Perm (Fin m)) (w : V) (j : Fin m) :
    (b.repr ((b.equiv b σ) w)) j = (b.repr w) (σ.symm j) := by
  rw [← Module.Basis.coord_apply, hdRo7SUPInvAux_coord_equiv, Module.Basis.coord_apply]

private theorem hdRo7SUPInvAux_coord_ones {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (k : Fin m) :
    b.coord k (SUOnes p b) = 1 := by
  unfold SUOnes
  rw [map_sum]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  simp

private theorem hdRo7SUPInvAux_sub_swap {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (v : V) {i j : Fin m} (hij : i ≠ j) :
    v - (b.equiv b (Equiv.swap i j)) v =
      (b.repr v i - b.repr v j) • (b i - b j) := by
  apply b.repr.injective
  ext k
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply]
  rw [hdRo7SUPInvAux_repr_equiv b (Equiv.swap i j) v k]
  rw [show (Equiv.swap i j).symm = Equiv.swap i j from Equiv.swap_inv i j]
  simp only [Module.Basis.repr_self_apply]
  rcases eq_or_ne k i with rfl | hki
  · rw [Equiv.swap_apply_left, if_neg (Ne.symm hij)]
    simp
  rcases eq_or_ne k j with rfl | hkj
  · rw [Equiv.swap_apply_right, if_neg hij]
    simp
  · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, if_neg (Ne.symm hki), if_neg (Ne.symm hkj)]
    ring

private theorem hdRo7SUPInvAux_exists_coord_ne {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (i0 : Fin m) {v : V}
    (hv : v ∉ Submodule.span (ZMod p) {SUOnes p b}) :
    ∃ i j : Fin m, b.repr v i ≠ b.repr v j := by
  by_contra hcon
  have hcon' : ∀ i j : Fin m, b.repr v i = b.repr v j := by
    intro i j
    by_contra hne
    exact hcon ⟨i, j, hne⟩
  apply hv
  rw [Submodule.mem_span_singleton]
  refine ⟨b.repr v i0, ?_⟩
  have hsum : ∑ k, b.repr v k • b k = (b.repr v i0) • SUOnes p b := by
    rw [SUOnes, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcon' k i0]
  exact hsum.symm.trans (b.sum_repr v)

private theorem hdRo7SUPInvAux_aug_eq_span {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (i0 : Fin m) :
    SUAug p b = Submodule.span (ZMod p) (Set.range (fun i : Fin m => b i - b i0)) := by
  apply le_antisymm
  · intro v hv
    rw [SUAug, LinearMap.mem_ker] at hv
    have hvsum : ∑ k, b.repr v k = 0 := by
      simpa only [LinearMap.sum_apply, Module.Basis.coord_apply] using hv
    have hmem : ∀ k : Fin m, b.repr v k • (b k - b i0) ∈
        Submodule.span (ZMod p) (Set.range (fun i : Fin m => b i - b i0)) :=
      fun k => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hsum : (∑ k : Fin m, b.repr v k • (b k - b i0)) ∈
        Submodule.span (ZMod p) (Set.range (fun i : Fin m => b i - b i0)) :=
      Submodule.sum_mem _ (fun k _ => hmem k)
    have hsym : (∑ k : Fin m, b.repr v k • (b k - b i0)) = v := by
      calc ∑ k, b.repr v k • (b k - b i0)
          = ∑ k, (b.repr v k • b k - b.repr v k • b i0) := by simp only [smul_sub]
        _ = ∑ k, b.repr v k • b k - ∑ k, b.repr v k • b i0 := by rw [Finset.sum_sub_distrib]
        _ = v - (∑ k, b.repr v k) • b i0 := by rw [b.sum_repr v, Finset.sum_smul]
        _ = v := by rw [hvsum, zero_smul, sub_zero]
    rwa [hsym] at hsum
  · rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    change b i - b i0 ∈ SUAug p b
    rw [SUAug, LinearMap.mem_ker, map_sub, LinearMap.sum_apply, LinearMap.sum_apply]
    have h1 : (∑ k, b.coord k (b i)) = 1 := by
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      simp
    have h2 : (∑ k, b.coord k (b i0)) = 1 := by
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      simp
    rw [h1, h2, sub_self]

private theorem hdRo7SUPInvAux_le_span_singleton {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (x : M) (W : Submodule F M) (h : W ≤ Submodule.span F {x}) :
    W = ⊥ ∨ W = Submodule.span F {x} := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    apply le_antisymm h
    have hnz : ∃ w ∈ W, w ≠ 0 := by
      by_contra hc
      apply hbot
      rw [Submodule.eq_bot_iff]
      intro z hz
      by_contra hz0
      exact hc ⟨z, hz, hz0⟩
    obtain ⟨w, hwW, hw0⟩ := hnz
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp (h hwW)
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hw0 hc.symm
    rw [Submodule.span_le]
    rintro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    have hmem : c⁻¹ • w ∈ W := W.smul_mem _ hwW
    rwa [← hc, inv_smul_smul₀ hc0] at hmem

private theorem hdRo7SUPInvAux_sup_span_eq_top {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (φ : M →ₗ[F] F) (x : M) (hx : φ x ≠ 0) :
    LinearMap.ker φ ⊔ Submodule.span F {x} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y
  rw [Submodule.mem_sup]
  refine ⟨y - (φ y / φ x) • x, ?_, (φ y / φ x) • x, ?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx, sub_self]
  · exact Submodule.smul_mem _ (φ y / φ x) (Submodule.subset_span (Set.mem_singleton x))
  · rw [sub_add_cancel]

private theorem hdRo7SUPInvAux_eq_or_top_of_le_sup {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (U : Submodule F M) (x : M) (W : Submodule F M) (hU : U ≤ W)
    (hsup : U ⊔ Submodule.span F {x} = ⊤) : W = U ∨ W = ⊤ := by
  by_cases hWU : W = U
  · exact Or.inl hWU
  · right
    have hnle : ∃ w, w ∈ W ∧ w ∉ U := by
      by_contra h'
      apply hWU
      apply le_antisymm _ hU
      intro z hzW
      by_contra hzU
      exact h' ⟨z, hzW, hzU⟩
    obtain ⟨w, hwW, hwU⟩ := hnle
    have hwtop : w ∈ U ⊔ Submodule.span F {x} := by
      rw [hsup]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hwtop
    obtain ⟨u, huU, s, hs, hus⟩ := hwtop
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hs
    have hc0 : c ≠ 0 := by
      intro hc0'
      apply hwU
      have : w = u := by rw [← hus, ← hc, hc0', zero_smul, add_zero]
      rwa [this]
    have hxW : x ∈ W := by
      have hwu : w - u = s := by rw [← hus, add_sub_cancel_left]
      have hmem : c⁻¹ • (w - u) ∈ W := W.smul_mem _ (W.sub_mem hwW (hU huU))
      rwa [hwu, ← hc, inv_smul_smul₀ hc0] at hmem
    have hspan : Submodule.span F {x} ≤ W := by
      rw [Submodule.span_singleton_le_iff_mem]; exact hxW
    have htop : (⊤ : Submodule F M) ≤ W := by
      rw [← hsup]; exact sup_le hU hspan
    exact le_antisymm le_top htop

private theorem hdRo7SUPInvAux_diff_mem {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW : ∀ a, SUPerm p b a → ∀ w ∈ W, a w ∈ W) {i j : Fin m} (hij : i ≠ j)
    (hdiff : b i - b j ∈ W) : ∀ k : Fin m, b i - b k ∈ W := by
  intro k
  by_cases hki : k = i
  · subst hki; rw [sub_self]; exact W.zero_mem
  by_cases hkj : k = j
  · subst hkj; exact hdiff
  · have hki' : i ≠ k := fun h => hki h.symm
    have hkj' : j ≠ k := fun h => hkj h.symm
    let τ : Equiv.Perm (Fin m) := Equiv.swap j k
    have hSU : SUPerm p b (b.equiv b τ) := ⟨τ, fun l => by rw [Module.Basis.equiv_apply]⟩
    have hmem := hW _ hSU _ hdiff
    have hτi : τ i = i := by
      show Equiv.swap j k i = i
      exact Equiv.swap_apply_of_ne_of_ne hij hki'
    have hτj : τ j = k := by
      show Equiv.swap j k j = k
      exact Equiv.swap_apply_left j k
    have heq : (b.equiv b τ) (b i - b j) = b i - b k := by
      rw [map_sub, Module.Basis.equiv_apply, Module.Basis.equiv_apply, hτi, hτj]
    rwa [heq] at hmem

theorem su_pInv_holds : SUPInvLeaf := by
  intro p _ hp m hm h3 V _ _ b W hW
  subst p
  by_cases hle : W ≤ Submodule.span (ZMod 3) {SUOnes 3 b}
  · rcases hdRo7SUPInvAux_le_span_singleton (SUOnes 3 b) W hle with hbot | hspan
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hspan)
  · right; right
    have hle' : ∃ v, v ∈ W ∧ v ∉ Submodule.span (ZMod 3) {SUOnes 3 b} := by
      by_contra h'
      apply hle
      intro z hzW
      by_contra hznot
      exact h' ⟨z, hzW, hznot⟩
    obtain ⟨v, hvW, hvnot⟩ := hle'
    let i0 : Fin m := ⟨0, by omega⟩
    obtain ⟨i, j, hij⟩ := hdRo7SUPInvAux_exists_coord_ne b i0 hvnot
    have hij_ne : i ≠ j := fun h => hij (by rw [h])
    have hsub := hdRo7SUPInvAux_sub_swap b v hij_ne
    have htv : (b.equiv b (Equiv.swap i j)) v ∈ W :=
      hW _ ⟨Equiv.swap i j, fun k => by rw [Module.Basis.equiv_apply]⟩ v hvW
    have hdiff : b i - b j ∈ W := by
      have hmem : (b.repr v i - b.repr v j) • (b i - b j) ∈ W := by
        rw [← hsub]; exact W.sub_mem hvW htv
      have hc0 : b.repr v i - b.repr v j ≠ 0 := sub_ne_zero.mpr hij
      have hsm := W.smul_mem (b.repr v i - b.repr v j)⁻¹ hmem
      rwa [inv_smul_smul₀ hc0] at hsm
    have hik : ∀ k : Fin m, b i - b k ∈ W :=
      hdRo7SUPInvAux_diff_mem b W hW hij_ne hdiff
    have hspread : ∀ k : Fin m, b k - b i0 ∈ W := by
      intro k
      have h1 : b i - b i0 ∈ W := hik i0
      have h2 : b i - b k ∈ W := hik k
      have hmem : (b i - b i0) - (b i - b k) ∈ W := W.sub_mem h1 h2
      convert hmem using 1
      abel
    have hUle : SUAug 3 b ≤ W := by
      rw [hdRo7SUPInvAux_aug_eq_span b i0, Submodule.span_le]
      rintro y ⟨k, rfl⟩
      exact hspread k
    have hxnotU : SUOnes 3 b ∉ SUAug 3 b := by
      rw [SUAug, LinearMap.mem_ker, LinearMap.sum_apply]
      simp only [hdRo7SUPInvAux_coord_ones]
      have hsum1 : (∑ _k : Fin m, (1 : ZMod 3)) = (m : ZMod 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
      rw [hsum1]
      intro hzero
      exact h3 ((ZMod.natCast_eq_zero_iff m 3).mp hzero)
    have hφx : (∑ k, b.coord k) (SUOnes 3 b) ≠ 0 := by
      simpa only [SUAug, LinearMap.mem_ker] using hxnotU
    have hsup : SUAug 3 b ⊔ Submodule.span (ZMod 3) {SUOnes 3 b} = ⊤ :=
      hdRo7SUPInvAux_sup_span_eq_top (∑ k, b.coord k) (SUOnes 3 b) hφx
    rcases hdRo7SUPInvAux_eq_or_top_of_le_sup (SUAug 3 b) (SUOnes 3 b) W hUle hsup with
      hWU | htop
    · exact Or.inl hWU
    · exact Or.inr htop

end CFSG.StandardType.HdRo7SU

