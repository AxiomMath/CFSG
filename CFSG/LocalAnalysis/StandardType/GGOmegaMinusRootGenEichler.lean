module

public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenDefs
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitStabilizer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.SeitzReduction
open CFSG.SeitzReduction.F4Pilot
open CFSG.SeitzReduction.OmegaPilot
open CFSG.SeitzReduction.SymplecticPilot
open Matrix QuadraticMap
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {b c : K}

section Split

variable {ι ι' : Type} {F : Type} [Field F] {Q : QuadraticForm F (ι → F)}
  {Q' : QuadraticForm F (ι' → F)} {e : ι' → ι}

private theorem apply_eq_of_isCoordSplit (hs : IsCoordSplit ⇑Q ⇑Q' e) {u : ι → F}
    (hu : ∀ a, a ∉ Set.range e → u a = 0) : Q u = Q' (u ∘ e) := by
  obtain ⟨R, hQ, hR⟩ := hs
  have hR0 : R 0 = 0 := by
    have h := hQ 0
    simpa using h.symm
  rw [hQ u, hR u 0 (fun a ha => by rw [hu a ha]; rfl), hR0, add_zero]

private theorem polar_eq_of_isCoordSplit (hs : IsCoordSplit ⇑Q ⇑Q' e) {u : ι → F}
    (hu : ∀ a, a ∉ Set.range e → u a = 0) (v : ι → F) :
    polar Q v u = polar Q' (v ∘ e) (u ∘ e) := by
  have hu' : Q u = Q' (u ∘ e) := apply_eq_of_isCoordSplit hs hu
  obtain ⟨R, hQ, hR⟩ := hs
  have hRvu : R (v + u) = R v := by
    refine hR (v + u) v (fun a ha => ?_)
    rw [Pi.add_apply, hu a ha, add_zero]
  have hvu : Q (v + u) = Q' (v ∘ e + u ∘ e) + R v := by
    rw [hQ, hRvu]
    rfl
  rw [show polar Q v u = Q (v + u) - Q v - Q u from rfl,
    show polar Q' (v ∘ e) (u ∘ e) =
      Q' (v ∘ e + u ∘ e) - Q' (v ∘ e) - Q' (u ∘ e) from rfl,
    hvu, hQ v, hu']
  ring

theorem eichler_extend_of_isCoordSplit (he : Function.Injective e)
    (hs : IsCoordSplit ⇑Q ⇑Q' e) {u w : ι → F}
    (hu : ∀ a, a ∉ Set.range e → u a = 0) (hw : ∀ a, a ∉ Set.range e → w a = 0)
    (x : ι' → F) :
    eichler Q u w (Function.extend e x 0) =
      Function.extend e (eichler Q' (u ∘ e) (w ∘ e) x) 0 := by
  have hu' : Q u = Q' (u ∘ e) := apply_eq_of_isCoordSplit hs hu
  have hw' : Q w = Q' (w ∘ e) := apply_eq_of_isCoordSplit hs hw
  have hpol : ∀ v : ι → F, polar Q v u = polar Q' (v ∘ e) (u ∘ e) :=
    fun v => polar_eq_of_isCoordSplit hs hu v
  have hpolw : ∀ v : ι → F, polar Q v w = polar Q' (v ∘ e) (w ∘ e) :=
    fun v => polar_eq_of_isCoordSplit hs hw v
  have hcond : (Q u = 0 ∧ polar Q u w = 0) ↔
      (Q' (u ∘ e) = 0 ∧ polar Q' (u ∘ e) (w ∘ e) = 0) := by
    rw [hu', hpolw u]
  have hcomp : (Function.extend e x 0) ∘ e = x := Function.extend_comp he x 0
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h' : Q' (u ∘ e) = 0 ∧ polar Q' (u ∘ e) (w ∘ e) = 0 := hcond.1 h
    rw [eichler_apply h.1 h.2, eichler_apply h'.1 h'.2]
    funext a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Function.Injective.extend_apply he, hpol, hpolw, hcomp, hw', Function.comp_apply]
    · have hxa : Function.extend e x 0 a = 0 :=
        Function.extend_apply' _ _ _ (by simpa using ha)
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hxa, hu a ha, hw a ha]
      simp only [mul_zero, sub_zero, add_zero]
      rw [Function.extend_apply' (g := _) (e' := (0 : ι → F)) (b := a)
        (by simpa using ha)]
      rfl
  · have h' : ¬(Q' (u ∘ e) = 0 ∧ polar Q' (u ∘ e) (w ∘ e) = 0) :=
      fun h'' => h (hcond.2 h'')
    rw [eichler_of_not h, eichler_of_not h']
    rfl

private theorem eichler_apply_of_not_mem (hs : IsCoordSplit ⇑Q ⇑Q' e) {u w : ι → F}
    (hu : ∀ a, a ∉ Set.range e → u a = 0) (hw : ∀ a, a ∉ Set.range e → w a = 0)
    {a : ι} (ha : a ∉ Set.range e) (v : ι → F) : eichler Q u w v a = v a := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply h.1 h.2]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hu a ha, hw a ha, smul_zero,
      sub_zero, add_zero]
  · rw [eichler_of_not h]
    rfl

private theorem eichler_apply_of_comp_eq_zero (hs : IsCoordSplit ⇑Q ⇑Q' e) {u w : ι → F}
    (hu : ∀ a, a ∉ Set.range e → u a = 0) (hw : ∀ a, a ∉ Set.range e → w a = 0)
    {v : ι → F} (hv : v ∘ e = 0) : eichler Q u w v = v := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply h.1 h.2, polar_eq_of_isCoordSplit hs hu v,
      polar_eq_of_isCoordSplit hs hw v, hv]
    simp
  · rw [eichler_of_not h]
    rfl

end Split

section Short

private theorem toMatrix'_toLinEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (A : GL ι K) :
    LinearMap.toMatrix' (LinearEquiv.toLinearMap (toLinEquiv ι K A)) =
      (A : Matrix ι ι K) := by
  ext i j
  change (toLinEquiv ι K A) (Pi.single j 1) i = (A : Matrix ι ι K) i j
  rw [toLinEquiv_apply, Matrix.mulVec_single_one, Matrix.col_apply]

private theorem mat_elt_difference {m : ℕ} {K : Type} [Field K] {i j : Fin m}
    (hij : i ≠ j) (t : K) :
    (((elt (.difference i j hij) t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      fromBlocks (1 + t • Matrix.single i j 1) 0 0 (1 - t • Matrix.single j i 1) := by
  ext a b
  rw [← mat_apply]
  rw [mat_elt]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [E, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
      Matrix.single_apply, sub_eq_add_neg]

private theorem eichler_quadPlus_eq_elt {m : ℕ} {K : Type} [Field K] [CharP K 2]
    {i j : Fin m} (hij : i ≠ j) (t : K) :
    toLinEquiv (Fin m ⊕ Fin m) K
        (((elt (.difference i j hij) (-t) : StatedSp m K) : GL (Fin m ⊕ Fin m) K)) =
      eichler (quadPlus m K) (Pi.single (Sum.inl i) 1) (t • Pi.single (Sum.inr j) 1) := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  have hmat := CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.toMatrix'_eichler_inl_inr
    (r := m) (K := K) hij (-t)
  simp only [neg_neg] at hmat
  rw [hmat, toMatrix'_toLinEquiv, mat_elt_difference]

theorem eichler_root_mem_omMinusShortBlock {i j : Fin m} (hij : i ≠ j) (t : K) :
    (toLinEquiv _ K).symm (eichler (quadMinus (m + 1) K b c)
      (Pi.single (Sum.inl i) 1) (t • Pi.single (Sum.inr (Sum.inl j)) 1)) ∈
      omMinusShortBlock K i j := by
  classical
  let ι := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2
  let e : Fin m ⊕ Fin m → ι := kOmMEmb m
  let Q : QuadraticForm K (ι → K) := quadMinus (m + 1) K b c
  let Q' : QuadraticForm K (Fin m ⊕ Fin m → K) := quadPlus m K
  let u : ι → K := Pi.single (Sum.inl i) 1
  let w : ι → K := t • Pi.single (Sum.inr (Sum.inl j)) 1
  let A : GL ι K := (toLinEquiv ι K).symm (eichler Q u w)
  let g : GL (Fin m ⊕ Fin m) K :=
    ((elt (.difference i j hij) (-t) : StatedSp m K) : GL (Fin m ⊕ Fin m) K)
  change (toLinEquiv ι K).symm (eichler Q u w) ∈ omMinusShortBlock K i j
  have he : Function.Injective e := kOmMEmb_injective
  have hs : IsCoordSplit ⇑Q ⇑Q' e := by
    dsimp only [Q, Q', e]
    rw [coe_quadMinus, coe_quadPlus]
    exact kOmM_isCoordSplit_hyp (r := m) b c
  have hu : ∀ a, a ∉ Set.range e → u a = 0 := by
    intro a ha
    rcases a with a | a | a
    · exact absurd ⟨Sum.inl a, rfl⟩ ha
    · exact absurd ⟨Sum.inr a, rfl⟩ ha
    · fin_cases a <;> simp [u, Pi.single_apply]
  have hw : ∀ a, a ∉ Set.range e → w a = 0 := by
    intro a ha
    rcases a with a | a | a
    · exact absurd ⟨Sum.inl a, rfl⟩ ha
    · exact absurd ⟨Sum.inr a, rfl⟩ ha
    · fin_cases a <;> simp [w, Pi.single_apply]
  have hsplit := eichler_extend_of_isCoordSplit he hs hu hw
  have hu_comp : u ∘ e = (Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K) := by
    funext a
    rcases a with a | a
    · simp [u, e, Pi.single_apply, Sum.inl_injective.eq_iff]
    · simp [u, e, Pi.single_apply]
  have hw_comp : w ∘ e = (t • Pi.single (Sum.inr j) 1 : Fin m ⊕ Fin m → K) := by
    funext a
    rcases a with a | a
    · simp [w, e, Pi.single_apply]
    · simp [w, e, Pi.single_apply, Sum.inr_injective.eq_iff, Sum.inl_injective.eq_iff]
  have hsingle : ∀ y : Fin m ⊕ Fin m,
      (Pi.single (e y) (1 : K) : ι → K) = Function.extend e (Pi.single y 1) 0 := by
    intro y
    funext a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨z, rfl⟩ := ha
      rw [Function.Injective.extend_apply he, Pi.single_apply, Pi.single_apply]
      by_cases hzy : z = y
      · rw [hzy]
        simp
      · have hne : e z ≠ e y := fun h => hzy (he h)
        simp [hzy, hne]
    · rw [Function.extend_apply' _ _ _ (by simpa using ha),
        Pi.single_eq_of_ne (i := e y) (i' := a) (fun h => ha ⟨y, h.symm⟩)]
      simp
  have hA_apply : toLinEquiv ι K A = eichler Q u w := by
    dsimp only [A]
    rw [MulEquiv.apply_symm_apply]
  have hrow : ∀ {a : ι}, a ∉ Set.range e → ∀ v : ι → K,
      eichler Q u w v a = v a :=
    fun ha v => eichler_apply_of_not_mem hs hu hw ha v
  have hzero : ∀ v : ι → K, v ∘ e = 0 → eichler Q u w v = v :=
    fun v hv => eichler_apply_of_comp_eq_zero hs hu hw hv
  have hsupp : IsSuppMat (Set.range e) (A : Matrix ι ι K) := by
    intro a b hab
    have hcol : (A : Matrix ι ι K) a b = eichler Q u w (Pi.single b 1) a := by
      have h : (A : Matrix ι ι K) *ᵥ Pi.single b 1 = eichler Q u w (Pi.single b 1) := by
        rw [← toLinEquiv_apply (A := A), hA_apply]
      rw [Matrix.mulVec_single_one] at h
      simpa [Matrix.col_apply] using congrFun h a
    by_cases hb : b ∈ Set.range e
    · have ha : a ∉ Set.range e := fun ha => hab ⟨ha, hb⟩
      rw [hcol, hrow ha (Pi.single b 1), Matrix.one_apply]
      have hne : a ≠ b := fun h => ha (h ▸ hb)
      simp [Pi.single_eq_of_ne hne, hne]
    · rw [hcol, hzero (Pi.single b 1) (by
        funext d
        rw [Function.comp_apply,
          Pi.single_eq_of_ne (i := b) (i' := e d) (fun h => hb ⟨d, h⟩)]
        simp),
        Matrix.one_apply]
      by_cases hab' : a = b
      · subst hab'
        simp
      · simp [Pi.single_eq_of_ne hab', hab']
  have hentry : ∀ x y : Fin m ⊕ Fin m,
      (A : Matrix ι ι K) (e x) (e y) = (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y := by
    intro x y
    have h1 : (A : Matrix ι ι K) (e x) (e y) =
        eichler Q u w (Pi.single (e y) 1) (e x) := by
      have h : (A : Matrix ι ι K) *ᵥ Pi.single (e y) 1 =
          eichler Q u w (Pi.single (e y) 1) := by
        rw [← toLinEquiv_apply (A := A), hA_apply]
      rw [Matrix.mulVec_single_one] at h
      simpa [Matrix.col_apply] using congrFun h (e x)
    rw [h1, hsingle y, hsplit (Pi.single y 1), Function.Injective.extend_apply he,
      hu_comp, hw_comp, ← eichler_quadPlus_eq_elt hij t]
    change (toLinEquiv (Fin m ⊕ Fin m) K g) (Pi.single y 1) x =
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y
    rw [toLinEquiv_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  have hcoord : coordEmbedGL e he g = A := by
    apply Units.ext
    apply Matrix.ext
    intro a b
    by_cases hab : a ∈ Set.range e ∧ b ∈ Set.range e
    · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab
      rw [coe_coordEmbedGL, coordEmbedMat_apply_image he]
      exact (hentry x y).symm
    · rw [coe_coordEmbedGL, coordEmbedMat_apply_of_not_mem _ hab]
      exact (hsupp a b hab).symm
  rw [omMinusShortBlock]
  refine Subgroup.mem_map.mpr ⟨g, ?_, hcoord⟩
  refine Subgroup.mem_map.mpr ⟨elt (.difference i j hij) (-t), ?_, rfl⟩
  exact elt_difference_mem_siegelBlock hij (by simp) (by simp) (-t)

end Short

section Long

theorem eichler_plane_mem_omMinusLongBlock (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k₀ : Fin m) {u w : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hu : ∀ k : Fin m, k ≠ k₀ → u (Sum.inl k) = 0 ∧ u (Sum.inr (Sum.inl k)) = 0)
    (hw : ∀ k : Fin m, k ≠ k₀ → w (Sum.inl k) = 0 ∧ w (Sum.inr (Sum.inl k)) = 0) :
    (toLinEquiv _ K).symm (eichler (quadMinus (m + 1) K b c) u w) ∈
      omMinusLongBlock K b c k₀ := by
  classical
  let ι := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2
  let ι' := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2
  let e : ι' → ι := kOmMLongEmb m k₀
  let Q : QuadraticForm K (ι → K) := quadMinus (m + 1) K b c
  let Q' : QuadraticForm K (ι' → K) := quadMinus 2 K b c
  let A : GL ι K := (toLinEquiv ι K).symm (eichler Q u w)
  change (toLinEquiv ι K).symm (eichler Q u w) ∈ omMinusLongBlock K b c k₀
  have he : Function.Injective e := kOmMLongEmb_injective k₀
  have hs : IsCoordSplit ⇑Q ⇑Q' e := by
    dsimp only [Q, Q', e]
    rw [coe_quadMinus, coe_quadMinus]
    exact kOmM_isCoordSplit_long b c k₀
  have hu_supp : ∀ a, a ∉ Set.range e → u a = 0 := by
    intro a ha
    obtain ⟨k, hk, rfl | rfl⟩ := kOmM_exists_of_not_mem_range_longEmb ha
    · exact (hu k hk).1
    · exact (hu k hk).2
  have hw_supp : ∀ a, a ∉ Set.range e → w a = 0 := by
    intro a ha
    obtain ⟨k, hk, rfl | rfl⟩ := kOmM_exists_of_not_mem_range_longEmb ha
    · exact (hw k hk).1
    · exact (hw k hk).2
  have hsplit := eichler_extend_of_isCoordSplit he hs hu_supp hw_supp
  have hA_apply : toLinEquiv ι K A = eichler Q u w := by
    dsimp only [A]
    rw [MulEquiv.apply_symm_apply]
  have hrow : ∀ {a : ι}, a ∉ Set.range e → ∀ v : ι → K,
      eichler Q u w v a = v a :=
    fun ha v => eichler_apply_of_not_mem hs hu_supp hw_supp ha v
  have hzero : ∀ v : ι → K, v ∘ e = 0 → eichler Q u w v = v :=
    fun v hv => eichler_apply_of_comp_eq_zero hs hu_supp hw_supp hv
  have hsingle : ∀ y : ι',
      (Pi.single (e y) (1 : K) : ι → K) = Function.extend e (Pi.single y 1) 0 := by
    intro y
    funext a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨z, rfl⟩ := ha
      rw [Function.Injective.extend_apply he, Pi.single_apply, Pi.single_apply]
      by_cases hzy : z = y
      · rw [hzy]
        simp
      · have hne : e z ≠ e y := fun h => hzy (he h)
        simp [hzy, hne]
    · rw [Function.extend_apply' _ _ _ (by simpa using ha),
        Pi.single_eq_of_ne (i := e y) (i' := a) (fun h => ha ⟨y, h.symm⟩)]
      simp
  have hsupp : IsSuppMat (Set.range e) (A : Matrix ι ι K) := by
    intro a b hab
    have hcol : (A : Matrix ι ι K) a b = eichler Q u w (Pi.single b 1) a := by
      have h : (A : Matrix ι ι K) *ᵥ Pi.single b 1 = eichler Q u w (Pi.single b 1) := by
        rw [← toLinEquiv_apply (A := A), hA_apply]
      rw [Matrix.mulVec_single_one] at h
      simpa [Matrix.col_apply] using congrFun h a
    by_cases hb : b ∈ Set.range e
    · have ha : a ∉ Set.range e := fun ha => hab ⟨ha, hb⟩
      rw [hcol, hrow ha (Pi.single b 1), Matrix.one_apply]
      have hne : a ≠ b := fun h => ha (h ▸ hb)
      simp [Pi.single_eq_of_ne hne, hne]
    · rw [hcol, hzero (Pi.single b 1) (by
        funext d
        rw [Function.comp_apply,
          Pi.single_eq_of_ne (i := b) (i' := e d) (fun h => hb ⟨d, h⟩)]
        simp),
        Matrix.one_apply]
      by_cases hab' : a = b
      · subst hab'
        simp
      · simp [Pi.single_eq_of_ne hab', hab']
  obtain ⟨g, hg⟩ := exists_coordEmbedGL_eq_of_mem_suppGL he (mem_suppGL.mpr hsupp)
  have hg_entry : ∀ x y : ι', (g : Matrix ι' ι' K) x y =
      eichler Q' (u ∘ e) (w ∘ e) (Pi.single y 1) x := by
    intro x y
    have h1 : (A : Matrix ι ι K) (e x) (e y) =
        eichler Q u w (Pi.single (e y) 1) (e x) := by
      have h : (A : Matrix ι ι K) *ᵥ Pi.single (e y) 1 =
          eichler Q u w (Pi.single (e y) 1) := by
        rw [← toLinEquiv_apply (A := A), hA_apply]
      rw [Matrix.mulVec_single_one] at h
      simpa [Matrix.col_apply] using congrFun h (e x)
    have h2 : (g : Matrix ι' ι' K) x y = (A : Matrix ι ι K) (e x) (e y) := by
      rw [← hg, coe_coordEmbedGL, coordEmbedMat_apply_image he]
    rw [h2, h1, hsingle y, hsplit (Pi.single y 1), Function.Injective.extend_apply he]
  have hg_eq : toLinEquiv ι' K g = eichler Q' (u ∘ e) (w ∘ e) := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.toMatrix'.injective
    rw [toMatrix'_toLinEquiv]
    ext x y
    rw [LinearMap.toMatrix'_apply]
    exact hg_entry x y
  have hg_stated : g ∈ StatedOmega (StatedQuadMinus 2 K b c) := by
    rw [mem_statedOmega_iff_mem_elementaryGroup (Q := quadMinus 2 K b c)
      (Q₀ := StatedQuadMinus 2 K b c) (coe_quadMinus 2 K b c)
      (commutator_orthogonalGroup_quadMinus_small (n := 2) (Or.inl rfl) hirr)]
    rw [hg_eq]
    exact eichler_mem_elementaryGroup (quadMinus 2 K b c) (u ∘ e) (w ∘ e)
  rw [omMinusLongBlock]
  exact Subgroup.mem_map.mpr ⟨g, hg_stated, hg⟩

end Long

end CFSG.StandardType

end
