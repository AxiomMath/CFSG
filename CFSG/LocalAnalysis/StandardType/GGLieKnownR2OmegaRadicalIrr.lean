module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCore

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin

private theorem irr_exists_two_ne {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    ∃ k l : Fin n, k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l := by
  classical
  have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
    simpa using Finset.card_insert_le i ({j} : Finset (Fin n))
  have hs : 1 < (({i, j} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp hs
  rw [Finset.mem_compl] at hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
  exact ⟨k, l, fun h => hk (Or.inl h), fun h => hk (Or.inr h),
    fun h => hl (Or.inl h), fun h => hl (Or.inr h), hkl⟩

private theorem irr_polarNondegOn_siegelW {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P')
    (hQ : (polarBilin Q).Nondegenerate) :
    PolarNondegOn Q (siegelW Q P.e P'.e P.f P'.f) := by
  have he : P'.e ∈ P.perp := HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩
  have hf : P'.f ∈ P.perp := HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩
  have hnd : PolarNondegOn Q (P.perp ⊓ P'.perp) :=
    PolarNondegOn.inf_perp (HypPair.polarNondegOn_perp hQ P) P' he hf
  have heq : siegelW Q P.e P'.e P.f P'.f = P.perp ⊓ P'.perp := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_inf, HypPair.mem_perp, HypPair.mem_perp]
      rw [siegelW, mem_orth_iff] at hx
      exact ⟨⟨hx P.e (Submodule.subset_span (by simp)),
          hx P.f (Submodule.subset_span (by simp))⟩,
        ⟨hx P'.e (Submodule.subset_span (by simp)),
          hx P'.f (Submodule.subset_span (by simp))⟩⟩
    · intro x hx
      rw [Submodule.mem_inf, HypPair.mem_perp, HypPair.mem_perp] at hx
      rw [siegelW, mem_orth_iff]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact hx.1.1
        · exact hx.2.1
        · exact hx.1.2
        · exact hx.2.2
      | zero => exact polar_zero_left Q x
      | add y z _ _ ihy ihz => rw [polar_add_left, ihy, ihz, add_zero]
      | smul c y _ ihy => rw [polar_smul_left_eq, ihy, mul_zero]
  rw [heq]
  exact hnd

private theorem irr_irreducible_of_W {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V}
    (hWnd : PolarNondegOn Q W)
    {P₁ P₂ : HypPair Q} (hP : P₁.Orth P₂)
    (he₁ : P₁.e ∈ W) (hf₁ : P₁.f ∈ W) (he₂ : P₂.e ∈ W) (hf₂ : P₂.f ∈ W) :
    ∀ X : Submodule K V, X ≤ W →
      (∀ g ∈ elementaryGroup Q,
        (∀ z, (∀ w ∈ W, polar Q z w = 0) → g z = z) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = W := by
  intro X hXW hXinv
  classical
  let X' : Submodule K W := X.comap W.subtype
  let Pfun : Fin 2 → HypPair (Q.restrict W) :=
    fun m => if m = 0 then P₁.restrict he₁ hf₁ else P₂.restrict he₂ hf₂
  have hP' : ∃ P : Fin 2 → HypPair (Q.restrict W), ∀ i j, i ≠ j → (P i).Orth (P j) := by
    refine ⟨Pfun, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [Pfun] using hP.restrict he₁ hf₁ he₂ hf₂
    · simpa [Pfun] using (hP.symm).restrict he₂ hf₂ he₁ hf₁
    · exact absurd rfl hij
  have hX'inv : ∀ g' ∈ elementaryGroup (Q.restrict W), ∀ x ∈ X', g' x ∈ X' := by
    intro g' hg' x hx
    obtain ⟨g, hg, hgW, hgz⟩ := exists_extend_of_mem_elementaryGroup_restrict hg'
    have hxX : (x : V) ∈ X := hx
    have hthis : g (x : V) ∈ X := hXinv g hg hgz (x : V) hxX
    change ((g' x : W) : V) ∈ X
    rw [← hgW x]
    exact hthis
  have hmain := submodule_eq_bot_or_top_of_elementaryGroup_invariant
    (V := W) (Q := Q.restrict W) (nondegenerate_polarBilin_restrict hWnd) hP' X' hX'inv
  rcases hmain with hbot | htop
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have hxW : x ∈ W := hXW hx
    have hmem : (⟨x, hxW⟩ : W) ∈ X' := hx
    rw [hbot] at hmem
    have h0 : (⟨x, hxW⟩ : W) = 0 := by simpa using hmem
    simpa using congrArg Subtype.val h0
  · right
    apply le_antisymm hXW
    intro x hxW
    have hmem : (⟨x, hxW⟩ : W) ∈ X' := by rw [htop]; exact Submodule.mem_top
    exact hmem

private theorem irr_irreducible_frame {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N)
    {i j : Fin N} (hij : i ≠ j) (s t : Bool)
    {k l : Fin N} (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l)
    (hQ : (polarBilin Q).Nondegenerate) :
    ∀ X : Submodule K V,
      X ≤ siegelW Q (F.vec j t) (F.vec i s) (F.vec j (!t)) (F.vec i (!s)) →
      (∀ g ∈ elementaryGroup Q,
        (∀ v ∈ Submodule.span K {F.vec j t, F.vec i s, F.vec j (!t), F.vec i (!s)}, g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW Q (F.vec j t) (F.vec i s) (F.vec j (!t)) (F.vec i (!s)) := by
  intro X hXW hXinv
  set a₁ : V := F.vec j t with ha₁
  set a₂ : V := F.vec i s with ha₂
  set b₁ : V := F.vec j (!t) with hb₁
  set b₂ : V := F.vec i (!s) with hb₂
  let P : HypPair Q := ⟨a₁, b₁, F.map_vec j t, F.map_vec j (!t), F.polar_vec_not j t⟩
  let P' : HypPair Q := ⟨a₂, b₂, F.map_vec i s, F.map_vec i (!s), F.polar_vec_not i s⟩
  have hPorth : P.Orth P' :=
    ⟨F.polar_vec_of_ne hij.symm t s, F.polar_vec_of_ne hij.symm t (!s),
      F.polar_vec_of_ne hij.symm (!t) s, F.polar_vec_of_ne hij.symm (!t) (!s)⟩
  set W : Submodule K V := siegelW Q a₁ a₂ b₁ b₂ with hW_def
  have hWnd : PolarNondegOn Q W := by
    change PolarNondegOn Q (siegelW Q P.e P'.e P.f P'.f)
    exact irr_polarNondegOn_siegelW hPorth hQ
  have hmem_key : ∀ (m : Fin N), m ≠ i → m ≠ j → ∀ u : Bool, F.vec m u ∈ W := by
    intro m hmi hmj u
    rw [hW_def, siegelW, mem_orth_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact F.polar_vec_of_ne hmj.symm t u
      · exact F.polar_vec_of_ne hmi.symm s u
      · exact F.polar_vec_of_ne hmj.symm (!t) u
      · exact F.polar_vec_of_ne hmi.symm (!s) u
    | zero => exact polar_zero_left Q _
    | add y z _ _ ihy ihz => rw [polar_add_left, ihy, ihz, add_zero]
    | smul c y _ ihy => rw [polar_smul_left_eq, ihy, mul_zero]
  let P₁ : HypPair Q :=
    ⟨F.vec k true, F.vec k false, F.map_vec k true, F.map_vec k false, F.polar_vec_not k true⟩
  let P₂ : HypPair Q :=
    ⟨F.vec l true, F.vec l false, F.map_vec l true, F.map_vec l false, F.polar_vec_not l true⟩
  have hP₁orth : P₁.Orth P₂ :=
    ⟨F.polar_vec_of_ne hkl true true, F.polar_vec_of_ne hkl true false,
      F.polar_vec_of_ne hkl false true, F.polar_vec_of_ne hkl false false⟩
  have he₁ : P₁.e ∈ W := hmem_key k hki hkj true
  have hf₁ : P₁.f ∈ W := hmem_key k hki hkj false
  have he₂ : P₂.e ∈ W := hmem_key l hli hlj true
  have hf₂ : P₂.f ∈ W := hmem_key l hli hlj false
  have hXinv' : ∀ g ∈ elementaryGroup Q,
      (∀ z, (∀ w ∈ W, polar Q z w = 0) → g z = z) → ∀ x ∈ X, g x ∈ X := by
    intro g hg hfix x hx
    apply hXinv g hg _ x hx
    intro v hv
    apply hfix v
    intro w hw
    rw [hW_def, siegelW, mem_orth_iff] at hw
    exact hw v hv
  have hfin := irr_irreducible_of_W hWnd hP₁orth he₁ hf₁ he₂ hf₂ X hXW hXinv'
  rwa [hW_def] at hfin

theorem siegelW_irreducible_quadPlus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F]
    {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    ∀ X : Submodule F (Fin n ⊕ Fin n → F),
      X ≤ siegelW (Spin.quadPlus n F) ((Spin.plusFrame n F (by omega)).vec j t)
        ((Spin.plusFrame n F (by omega)).vec i s) ((Spin.plusFrame n F (by omega)).vec j (!t))
        ((Spin.plusFrame n F (by omega)).vec i (!s)) →
      (∀ g ∈ elementaryGroup (Spin.quadPlus n F),
        (∀ v ∈ Submodule.span F {((Spin.plusFrame n F (by omega)).vec j t),
          ((Spin.plusFrame n F (by omega)).vec i s), ((Spin.plusFrame n F (by omega)).vec j (!t)),
          ((Spin.plusFrame n F (by omega)).vec i (!s))}, g v = v) → ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW (Spin.quadPlus n F) ((Spin.plusFrame n F (by omega)).vec j t)
        ((Spin.plusFrame n F (by omega)).vec i s) ((Spin.plusFrame n F (by omega)).vec j (!t))
        ((Spin.plusFrame n F (by omega)).vec i (!s)) := by
  obtain ⟨k, l, hki, hkj, hli, hlj, hkl⟩ := irr_exists_two_ne hn i j
  exact irr_irreducible_frame (Spin.plusFrame n F (by omega)) hij s t hki hkj hli hlj hkl
    (Spin.nondegenerate_polarBilin_quadPlus n F)

theorem siegelW_irreducible_quadMinus_ge_five {n : ℕ} (hn : 5 ≤ n) {F : Type} [Field F]
    [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) :
    ∀ X : Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      X ≤ siegelW (Spin.quadMinus n F b c)
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec j t)
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec i s)
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec j (!t))
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec i (!s)) →
      (∀ g ∈ elementaryGroup (Spin.quadMinus n F b c),
        (∀ v ∈ Submodule.span F {((Spin.Twisted.minusFrame n b c).toHypFrame.vec j t),
          ((Spin.Twisted.minusFrame n b c).toHypFrame.vec i s),
          ((Spin.Twisted.minusFrame n b c).toHypFrame.vec j (!t)),
          ((Spin.Twisted.minusFrame n b c).toHypFrame.vec i (!s))}, g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW (Spin.quadMinus n F b c)
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec j t)
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec i s)
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec j (!t))
        ((Spin.Twisted.minusFrame n b c).toHypFrame.vec i (!s)) := by
  obtain ⟨k, l, hki, hkj, hli, hlj, hkl⟩ := irr_exists_two_ne (n := n - 1) (by omega) i j
  exact irr_irreducible_frame (Spin.Twisted.minusFrame n b c).toHypFrame hij s t
    hki hkj hli hlj hkl (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr)

end CFSG.StandardType.LieKnownR2.POmega.Radical
