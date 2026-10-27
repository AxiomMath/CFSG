module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Coord
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Action
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Normal
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Model

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

private lemma twE6ShiftMap_zero {k : Type} [AddCommMonoid k] (j : Fin 12) :
    twE6ShiftMap j (0 : Fin 8 → k) = 0 := by
  ext i
  simp [twE6ShiftMap]

private lemma twE6ShiftMap_add {k : Type} [AddCommMonoid k] (j : Fin 12) (a b : Fin 8 → k) :
    twE6ShiftMap j (a + b) = twE6ShiftMap j a + twE6ShiftMap j b := by
  ext i
  simp only [twE6ShiftMap, Pi.add_apply, Finset.sum_add_distrib]

private lemma twE6ShiftMap_none {k : Type} [AddCommMonoid k] (j : Fin 12) (i : Fin 8)
    (h : twE6Shift j i = none) (c : k) :
    twE6ShiftMap j (Pi.single i c) = 0 := by
  ext i''
  change twE6ShiftMap j (Pi.single i c) i'' = 0
  rw [twE6ShiftMap]
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hbi : b = i
  · subst hbi
    exact absurd (Finset.mem_filter.mp hb).2 (by rw [h]; simp)
  · rw [Pi.single_eq_of_ne hbi]

private lemma twE6ShiftMap_single {k : Type} [AddCommMonoid k] (j : Fin 12) (i i' : Fin 8)
    (h : twE6Shift j i = some i') (c : k) :
    twE6ShiftMap j (Pi.single i c) = Pi.single i' c := by
  ext i''
  rw [twE6ShiftMap]
  by_cases hii : i'' = i'
  · rw [hii]
    have hmem : i ∈ Finset.univ.filter (fun b => twE6Shift j b = some i') :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hvanish : ∀ b ∈ Finset.univ.filter (fun b => twE6Shift j b = some i'), b ≠ i →
        (Pi.single i c : Fin 8 → k) b = 0 := by
      intro b _ hb
      rw [Pi.single_eq_of_ne hb]
    rw [Finset.sum_eq_single_of_mem i hmem hvanish]
    simp
  · rw [Pi.single_eq_of_ne hii]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hbi : b = i
    · subst hbi
      exact absurd (Option.some.inj ((Finset.mem_filter.mp hb).2.symm.trans h)) hii
    · rw [Pi.single_eq_of_ne hbi]

private noncomputable def twE6ShiftActHom {k : Type} [AddCommMonoid k] (j : Fin 12) :
    (Fin 8 → k) →+ (Fin 8 → k) where
  toFun := fun m => m + twE6ShiftMap j m
  map_zero' := by
    ext i
    simp [twE6ShiftMap]
  map_add' := by
    intro a b
    rw [twE6ShiftMap_add]
    abel

private lemma teCoordAct_torusMap_single {k : Type} [Field k] (θ : k →+* k) (s : k) (i : Fin 8)
    (c : k) :
    twE6TorusMap θ s (Pi.single i c) = Pi.single i (twE6TorusMul θ s i * c) := by
  ext i'
  by_cases h : i' = i
  · subst h
    simp [twE6TorusMap, twE6TorusMul]
  · simp [twE6TorusMap, Pi.single_eq_of_ne h]

private noncomputable def twE6TorusHom {k : Type} [Field k] (θ : k →+* k) (s : k) :
    (Fin 8 → k) →+ (Fin 8 → k) where
  toFun := twE6TorusMap θ s
  map_zero' := by
    ext i
    simp [twE6TorusMap]
  map_add' := by
    intro a b
    ext i
    simp [twE6TorusMap, mul_add]

private lemma twE6Perm_involutive : Function.Involutive twE6Perm := by
  intro i
  fin_cases i <;> rfl

private lemma teCoordAct_permMap_single {k : Type} [Zero k] (i : Fin 8) (c : k) :
    twE6PermMap (Pi.single i c) = Pi.single (twE6Perm i) c := by
  ext i'
  rw [twE6PermMap]
  by_cases h : i' = twE6Perm i
  · subst h
    rw [twE6Perm_involutive, Pi.single_eq_same, Pi.single_eq_same]
  · have hne : twE6Perm i' ≠ i := by
      intro hc
      apply h
      rw [← twE6Perm_involutive i', hc]
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h]

private noncomputable def twE6PermHom (k : Type*) [AddCommMonoid k] :
    (Fin 8 → k) →+ (Fin 8 → k) where
  toFun := fun (m : Fin 8 → k) => fun i => m (twE6Perm i)
  map_zero' := by
    ext i
    simp
  map_add' := by
    intro a b
    ext i
    simp

private lemma twE6_coord_one
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Φ : fixedGroup k θ → (Fin 8 → k)} (hΦ : IsTwE6Coord θ hθ Φ) :
    Φ (1 : fixedGroup k θ) = 0 := by
  have h : Φ (1 : fixedGroup k θ) = Φ 1 + Φ 1 := by
    simpa using hΦ.1 1 (twE6Rad θ).one_mem 1 (twE6Rad θ).one_mem
  have h2 : (0 : Fin 8 → k) = Φ 1 := by
    have h3 : Φ 1 + 0 = Φ 1 + Φ 1 := by rw [add_zero]; exact h
    exact add_left_cancel h3
  exact h2.symm

private lemma twE6_coord_list_prod
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Φ : fixedGroup k θ → (Fin 8 → k)} (hΦ : IsTwE6Coord θ hθ Φ)
    (l : List (fixedGroup k θ)) (hl : ∀ x ∈ l, x ∈ twE6Rad θ) :
    l.prod ∈ twE6Rad θ ∧ Φ l.prod = (l.map Φ).sum := by
  induction l with
  | nil =>
      refine ⟨(twE6Rad θ).one_mem, ?_⟩
      change Φ (1 : fixedGroup k θ) = 0
      exact twE6_coord_one θ hθ hΦ
  | cons a l ih =>
      obtain ⟨hmem, hphi⟩ := ih fun x hx => hl x (List.mem_cons_of_mem a hx)
      refine ⟨?_, ?_⟩
      · rw [List.prod_cons]
        exact (twE6Rad θ).mul_mem (hl a (List.mem_cons_self)) hmem
      · rw [List.prod_cons, List.map_cons, List.sum_cons]
        rw [hΦ.1 a (hl a (List.mem_cons_self)) l.prod hmem, hphi]

private lemma teCoordAct_cen_le_rad
    {k : Type} [Field k] (θ : k →+* k) :
    twE6Cen θ ≤ twE6Rad θ := by
  simp only [twE6Cen, twE6Rad, ggSub]
  refine iSup_le fun γ => iSup_le fun hγ => ?_
  exact le_iSup_of_le γ (le_iSup_of_le ⟨hγ.1, le_trans (by norm_num : (1 : ℤ) ≤ 2) hγ.2⟩
    le_rfl)

private lemma twE6_coord_conj
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Φ : fixedGroup k θ → (Fin 8 → k)} (hΦ : IsTwE6Coord θ hθ Φ)
    (u : fixedGroup k θ)
    (huQ : ∀ x ∈ twE6Rad θ, u * x * u⁻¹ ∈ twE6Rad θ)
    (huC : ∀ x ∈ twE6Cen θ, u * x * u⁻¹ ∈ twE6Cen θ)
    (T : (Fin 8 → k) →+ (Fin 8 → k))
    (hgen : ∀ (i : Fin 8) (c : k), Φ (u * twE6X θ hθ i c * u⁻¹) = T (Pi.single i c))
    {g : fixedGroup k θ} (hg : g ∈ twE6Rad θ) :
    u * g * u⁻¹ ∈ twE6Rad θ ∧ Φ (u * g * u⁻¹) = T (Φ g) := by
  classical
  let f : Fin 8 → fixedGroup k θ := fun i => twE6X θ hθ i (Φ g i)
  have hf : ∀ x ∈ List.ofFn f, x ∈ twE6Rad θ := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact twE6X_mem_rad θ hθ i (Φ g i)
  have hsingle : (∑ i : Fin 8, Pi.single i (Φ g i)) = Φ g := by
    ext i
    simpa using Fintype.sum_pi_single i (Φ g)
  obtain ⟨hfm, hfp⟩ := twE6_coord_list_prod θ hθ hΦ (List.ofFn f) hf
  let g' : fixedGroup k θ := (List.ofFn f).prod
  have hg'mem : g' ∈ twE6Rad θ := hfm
  have hg'phi : Φ g' = Φ g := by
    change Φ (List.ofFn f).prod = Φ g
    rw [hfp, List.map_ofFn, Fin.sum_ofFn]
    have hsum : (∑ i : Fin 8, (Φ ∘ f) i) = ∑ i : Fin 8, Pi.single i (Φ g i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply, f]
      exact hΦ.2.2 i (Φ g i)
    rw [hsum, hsingle]
  have hzQ : g * g'⁻¹ ∈ twE6Rad θ :=
    (twE6Rad θ).mul_mem hg ((twE6Rad θ).inv_mem hg'mem)
  have hinv : Φ g'⁻¹ = -Φ g' := by
    have h := hΦ.1 (g'⁻¹) ((twE6Rad θ).inv_mem hg'mem) g' hg'mem
    have h0 : Φ g'⁻¹ + Φ g' = 0 := by
      rw [h.symm, inv_mul_cancel, twE6_coord_one θ hθ hΦ]
    exact eq_neg_of_add_eq_zero_left h0
  have hzphi : Φ (g * g'⁻¹) = 0 := by
    rw [hΦ.1 g hg (g'⁻¹) ((twE6Rad θ).inv_mem hg'mem), hinv, hg'phi]
    abel
  have hzC : g * g'⁻¹ ∈ twE6Cen θ := (hΦ.2.1 (g * g'⁻¹) hzQ).1 hzphi
  have hconj : u * g * u⁻¹ = (u * (g * g'⁻¹) * u⁻¹) * (u * g' * u⁻¹) := by group
  have hzQ' : u * (g * g'⁻¹) * u⁻¹ ∈ twE6Rad θ := huQ _ hzQ
  have hzC' : u * (g * g'⁻¹) * u⁻¹ ∈ twE6Cen θ := huC _ hzC
  have hg'Q' : u * g' * u⁻¹ ∈ twE6Rad θ := huQ _ hg'mem
  have hz0 : Φ (u * (g * g'⁻¹) * u⁻¹) = 0 := (hΦ.2.1 _ hzQ').2 hzC'
  have hprod' : Φ (u * g' * u⁻¹) = T (Φ g) := by
    let f' : Fin 8 → fixedGroup k θ := fun i => u * f i * u⁻¹
    have hf' : ∀ x ∈ List.ofFn f', x ∈ twE6Rad θ := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact huQ (f i) (hf (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩))
    obtain ⟨_, hf'p⟩ := twE6_coord_list_prod θ hθ hΦ (List.ofFn f') hf'
    have hconjprod : u * g' * u⁻¹ = (List.ofFn f').prod := by
      have h1 : u * g' * u⁻¹ = ((List.ofFn f).map (MulAut.conj u)).prod := by
        change u * (List.ofFn f).prod * u⁻¹ = ((List.ofFn f).map (MulAut.conj u)).prod
        rw [← map_list_prod (MulAut.conj u) (List.ofFn f)]
        rfl
      rw [h1, List.map_ofFn]
      rfl
    rw [hconjprod, hf'p, List.map_ofFn, Fin.sum_ofFn]
    have hsum' : (∑ i : Fin 8, (Φ ∘ f') i) = ∑ i : Fin 8, T (Pi.single i (Φ g i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply, f']
      exact hgen i (Φ g i)
    rw [hsum', ← map_sum T (fun i : Fin 8 => Pi.single i (Φ g i)) Finset.univ, hsingle]
  refine ⟨?_, ?_⟩
  · rw [hconj]
    exact (twE6Rad θ).mul_mem hzQ' hg'Q'
  · rw [hconj, hΦ.1 (u * (g * g'⁻¹) * u⁻¹) hzQ' (u * g' * u⁻¹) hg'Q', hz0, zero_add, hprod']

theorem twE6_coord_shift
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Φ : fixedGroup k θ → (Fin 8 → k)} (hΦ : IsTwE6Coord θ hθ Φ) (j : Fin 12)
    {g : fixedGroup k θ} (hg : g ∈ twE6Rad θ) :
    twE6Y θ j * g * (twE6Y θ j)⁻¹ ∈ twE6Rad θ ∧
      Φ (twE6Y θ j * g * (twE6Y θ j)⁻¹) = Φ g + twE6ShiftMap j (Φ g) := by
  have huQ : ∀ x ∈ twE6Rad θ, twE6Y θ j * x * (twE6Y θ j)⁻¹ ∈ twE6Rad θ :=
    fun x hx => (Subgroup.mem_set_normalizer_iff.mp (twE6Y_mem_normalizer_rad_cen θ j).1 x).1 hx
  have huC : ∀ x ∈ twE6Cen θ, twE6Y θ j * x * (twE6Y θ j)⁻¹ ∈ twE6Cen θ :=
    fun x hx => (Subgroup.mem_set_normalizer_iff.mp (twE6Y_mem_normalizer_rad_cen θ j).2 x).1 hx
  have hgen : ∀ (i : Fin 8) (c : k),
      Φ (twE6Y θ j * twE6X θ hθ i c * (twE6Y θ j)⁻¹) =
        twE6ShiftActHom j (Pi.single i c) := by
    intro i c
    cases h : twE6Shift j i with
    | none =>
        have hcomm := twE6_comm_shift_none θ hθ j i h c
        have hconj : twE6Y θ j * twE6X θ hθ i c * (twE6Y θ j)⁻¹ = twE6X θ hθ i c := by
          have h1 : twE6Y θ j * twE6X θ hθ i c * (twE6Y θ j)⁻¹ =
              ⁅twE6Y θ j, twE6X θ hθ i c⁆ * twE6X θ hθ i c := by
            rw [commutatorElement_def]
            group
          rw [h1, hcomm, one_mul]
        rw [hconj, hΦ.2.2 i c]
        change Pi.single i c = Pi.single i c + twE6ShiftMap j (Pi.single i c)
        rw [twE6ShiftMap_none j i h c, add_zero]
    | some i' =>
        obtain ⟨z, hzC, hcomm⟩ := twE6_comm_shift_some θ hθ j i i' h c
        have hconj : twE6Y θ j * twE6X θ hθ i c * (twE6Y θ j)⁻¹ =
            (twE6X θ hθ i' c * z) * twE6X θ hθ i c := by
          have h1 : twE6Y θ j * twE6X θ hθ i c * (twE6Y θ j)⁻¹ =
              ⁅twE6Y θ j, twE6X θ hθ i c⁆ * twE6X θ hθ i c := by
            rw [commutatorElement_def]
            group
          rw [h1, hcomm]
        rw [hconj]
        rw [hΦ.1 (twE6X θ hθ i' c * z)
              (mul_mem (twE6X_mem_rad θ hθ i' c) (teCoordAct_cen_le_rad θ hzC))
              (twE6X θ hθ i c) (twE6X_mem_rad θ hθ i c)]
        rw [hΦ.1 (twE6X θ hθ i' c) (twE6X_mem_rad θ hθ i' c) z (teCoordAct_cen_le_rad θ hzC)]
        rw [(hΦ.2.1 z (teCoordAct_cen_le_rad θ hzC)).2 hzC]
        rw [hΦ.2.2 i' c, hΦ.2.2 i c]
        rw [show twE6ShiftActHom j (Pi.single i c) =
          Pi.single i c + twE6ShiftMap j (Pi.single i c) from rfl]
        rw [twE6ShiftMap_single j i i' h c]
        abel
  exact twE6_coord_conj θ hθ hΦ (twE6Y θ j) huQ huC (twE6ShiftActHom j) hgen hg

theorem twE6_coord_torus
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Φ : fixedGroup k θ → (Fin 8 → k)} (hΦ : IsTwE6Coord θ hθ Φ) (t : kˣ) :
    ∃ h ∈ hHat k θ twE6ShortNode, ∀ g ∈ twE6Rad θ,
      h * g * h⁻¹ ∈ twE6Rad θ ∧ Φ (h * g * h⁻¹) = twE6TorusMap θ (t : k) (Φ g) := by
  obtain ⟨h, hh, hconj⟩ := twE6_torus_conj θ hθ t
  refine ⟨h, hh, ?_⟩
  have hnorm := hHat_le_normalizer_rad_cen θ twE6ShortNode hh
  have huQ : ∀ x ∈ twE6Rad θ, h * x * h⁻¹ ∈ twE6Rad θ :=
    fun x hx => (Subgroup.mem_set_normalizer_iff.mp hnorm.1 x).1 hx
  have huC : ∀ x ∈ twE6Cen θ, h * x * h⁻¹ ∈ twE6Cen θ :=
    fun x hx => (Subgroup.mem_set_normalizer_iff.mp hnorm.2 x).1 hx
  have hgen : ∀ (i : Fin 8) (c : k),
      Φ (h * twE6X θ hθ i c * h⁻¹) = twE6TorusHom θ (t : k) (Pi.single i c) := by
    intro i c
    rw [hconj i c, hΦ.2.2 i (twE6TorusMul θ (t : k) i * c)]
    change Pi.single i (twE6TorusMul θ (t : k) i * c) =
      twE6TorusMap θ (t : k) (Pi.single i c)
    rw [teCoordAct_torusMap_single]
  exact fun g hg => twE6_coord_conj θ hθ hΦ h huQ huC (twE6TorusHom θ (t : k)) hgen hg

theorem twE6_coord_perm
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {Φ : fixedGroup k θ → (Fin 8 → k)} (hΦ : IsTwE6Coord θ hθ Φ)
    {g : fixedGroup k θ} (hg : g ∈ twE6Rad θ) :
    nHat θ twE6ShortNode * g * (nHat θ twE6ShortNode)⁻¹ ∈ twE6Rad θ ∧
      Φ (nHat θ twE6ShortNode * g * (nHat θ twE6ShortNode)⁻¹) = twE6PermMap (Φ g) := by
  have hnorm := nHat_mem_normalizer_rad_cen θ
  have huQ : ∀ x ∈ twE6Rad θ, nHat θ twE6ShortNode * x * (nHat θ twE6ShortNode)⁻¹ ∈
      twE6Rad θ :=
    fun x hx => (Subgroup.mem_set_normalizer_iff.mp hnorm.1 x).1 hx
  have huC : ∀ x ∈ twE6Cen θ, nHat θ twE6ShortNode * x * (nHat θ twE6ShortNode)⁻¹ ∈
      twE6Cen θ :=
    fun x hx => (Subgroup.mem_set_normalizer_iff.mp hnorm.2 x).1 hx
  have hgen : ∀ (i : Fin 8) (c : k),
      Φ (nHat θ twE6ShortNode * twE6X θ hθ i c * (nHat θ twE6ShortNode)⁻¹) =
        twE6PermHom k (Pi.single i c) := by
    intro i c
    rw [twE6_nHat_conj θ hθ i c, hΦ.2.2 (twE6Perm i) c]
    rw [show twE6PermHom k (Pi.single i c) = twE6PermMap (Pi.single i c) from rfl]
    rw [teCoordAct_permMap_single]
  exact twE6_coord_conj θ hθ hΦ (nHat θ twE6ShortNode) huQ huC (twE6PermHom k) hgen hg

end CFSG.StandardType.LieKnownR2.Short
