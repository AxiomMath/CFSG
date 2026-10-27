module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.StandardType.E6QTwo

open Module
open CFSG.Blueprint.Chevalley

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}

theorem exists_functional_ker_eq {H : Submodule (ZMod 3) V}
    (hH : Nat.card H = 3 ^ 5) (hV : Nat.card V = 3 ^ 6) :
    ∃ f : Dual (ZMod 3) V, f ≠ 0 ∧ LinearMap.ker f = H := by
  have hHlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hcard : Nat.card H = Nat.card V := by
      rw [htop]
      exact Nat.card_congr (Submodule.topEquiv (R := ZMod 3) (M := V)).toEquiv
    rw [← hcard, hH] at hV
    norm_num at hV
  haveI : Module.Free (ZMod 3) (V ⧸ H) := inferInstance
  obtain ⟨f, hfne, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hHlt
    (inferInstance : Projective (ZMod 3) (V ⧸ H))
  have hle : H ≤ LinearMap.ker f := by
    intro x hx
    have : f x ∈ H.map f := Submodule.mem_map_of_mem hx
    rw [hfmap] at this
    simpa using this
  have hfinH : finrank (ZMod 3) H = 5 := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := H)
    rw [Nat.card_zmod, hH] at hcard
    exact (Nat.pow_right_injective (by norm_num) hcard).symm
  have hfink : finrank (ZMod 3) (LinearMap.ker f) = 5 := by
    have hkerlt : LinearMap.ker f < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      have hfzero : f = 0 := by
        ext v
        have hv : v ∈ LinearMap.ker f := by rw [htop]; exact Submodule.mem_top
        simpa using hv
      exact hfne hfzero
    have hV6 : finrank (ZMod 3) V = 6 := finrank_eq_six hV
    have hge : 5 ≤ finrank (ZMod 3) (LinearMap.ker f) := by
      have := Submodule.finrank_mono hle
      omega
    have hle6 : finrank (ZMod 3) (LinearMap.ker f) ≤ 5 := by
      have hlt : finrank (ZMod 3) (LinearMap.ker f) < finrank (ZMod 3) V := by
        have := Submodule.finrank_lt hkerlt.ne
        simpa [hV6] using this
      omega
    omega
  exact ⟨f, hfne, (Submodule.eq_of_le_of_finrank_eq hle (hfinH.trans hfink.symm)).symm⟩

theorem exists_bilinForm_of_span_top (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) :
    ∃ B : LinearMap.BilinForm (ZMod 3) V, ∀ i v, B (h i) v = α i v := by
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod 3) h) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  obtain ⟨S, hS⟩ :=
    LinearMap.exists_rightInverse_of_surjective (Fintype.linearCombination (ZMod 3) h)
      (LinearMap.range_eq_top.mpr hsurj)
  have hFn : Fintype.linearCombination (ZMod 3) α cartanE6KernelVec = 0 := by
    refine LinearMap.ext_on_range (v := h) hspan fun k => ?_
    rw [Fintype.linearCombination_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, hP]
    exact cartanE6KernelVec_mulVec_transpose k
  have hES : ∀ w, Fintype.linearCombination (ZMod 3) h (S w) = w := by
    intro w
    simpa using LinearMap.congr_fun hS w
  have hsingle : ∀ i, Fintype.linearCombination (ZMod 3) h (Pi.single i 1) = h i := by
    intro i
    rw [Fintype.linearCombination_apply_single]
    simp
  have hFker : ∀ c : Fin 6 → ZMod 3,
      Fintype.linearCombination (ZMod 3) h c = 0 →
      Fintype.linearCombination (ZMod 3) α c = 0 := by
    intro c hc
    have hcC : cartanE6ModThree *ᵥ c = 0 := by
      ext i
      have h' := congrArg (α i) hc
      simp only [map_zero] at h'
      rwa [apply_linearCombination_eq_cartanE6ModThree hP i c] at h'
    have hcn : c = c 0 • cartanE6KernelVec := eq_smul_cartanE6KernelVec c hcC
    conv_lhs => rw [hcn]
    rw [map_smul, hFn, smul_zero]
  have hFS : ∀ i, Fintype.linearCombination (ZMod 3) α (S (h i)) = α i := by
    intro i
    have hker : Fintype.linearCombination (ZMod 3) h (S (h i) - Pi.single i 1) = 0 := by
      rw [map_sub, hES, hsingle, sub_self]
    have h0 : Fintype.linearCombination (ZMod 3) α (S (h i)) -
        Fintype.linearCombination (ZMod 3) α (Pi.single i 1) = 0 := by
      rw [← map_sub]
      exact hFker _ hker
    have h1 : Fintype.linearCombination (ZMod 3) α (Pi.single i 1) = α i := by
      rw [Fintype.linearCombination_apply_single]
      simp
    exact sub_eq_zero.mp (by rwa [h1] at h0)
  refine ⟨(Fintype.linearCombination (ZMod 3) α).comp S, fun i v => ?_⟩
  rw [LinearMap.comp_apply, hFS]

variable {B : LinearMap.BilinForm (ZMod 3) V}

theorem bilinForm_symm_of_span_top
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hB : ∀ i v, B (h i) v = α i v) (u v : V) : B u v = B v u := by
  have hflip : B = B.flip := by
    refine LinearMap.ext_on_range (v := h) hspan fun i => ?_
    refine LinearMap.ext_on_range (v := h) hspan fun j => ?_
    rw [LinearMap.BilinForm.flip_apply, hB i (h j), hB j (h i), hP i j, hP j i]
    exact congrArg (fun x : ℤ => (x : ZMod 3))
      (Matrix.IsSymm.apply (CartanMatrix.E_isSymm 6) i j).symm
  have h := LinearMap.congr_fun (LinearMap.congr_fun hflip u) v
  rwa [LinearMap.BilinForm.flip_apply] at h

theorem bilinForm_reflection_of_span_top
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (i : Fin 6) (u v : V) : B (reflection (hα i) u) (reflection (hα i) v) = B u v := by
  have hsymm := bilinForm_symm_of_span_top hP hspan hB
  have hux : B u (h i) = α i u := by
    rw [hsymm u (h i)]
    exact hB i u
  have hvx : B v (h i) = α i v := by
    rw [hsymm v (h i)]
    exact hB i v
  have hxx : B (h i) (h i) = 2 := by rw [hB, hα]
  rw [reflection_apply, reflection_apply]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hB, hux, hvx, hxx, hα]
  ring

theorem span_ne_top_of_card_six
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hV : Nat.card V = 3 ^ 6)
    (hW : Nat.card (e6Weyl hα) = 51840) {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hA : A ≤ e6Weyl hα) (hcardA : 720 ≤ Nat.card A) {x : V} (hx : x ≠ 0)
    (hAx : ∀ g ∈ A, g x = x)
    {H : Submodule (ZMod 3) V} (hH : Nat.card H = 3 ^ 5) (hxH : x ∈ H)
    (hAH : ∀ g ∈ A, ∀ v, g v - v ∈ H)
    (hfix : ∀ v, (∀ g ∈ A, g v - v ∈ (ZMod 3) ∙ x) → v ∈ (ZMod 3) ∙ x) :
    Submodule.span (ZMod 3) (Set.range h) ≠ ⊤ := by
  intro hspan
  obtain ⟨B, hB⟩ := exists_bilinForm_of_span_top hP hspan
  have hsymm : ∀ u v, B u v = B v u := bilinForm_symm_of_span_top hP hspan hB
  have hmem_ker : ∀ v, v ∈ LinearMap.ker B ↔ ∀ i, α i v = 0 := by
    intro v
    rw [LinearMap.mem_ker]
    constructor
    · intro hv i
      have h1 := congrArg (fun φ : V →ₗ[ZMod 3] ZMod 3 => φ (h i)) hv
      simp only [LinearMap.zero_apply] at h1
      rwa [hsymm v (h i), hB i v] at h1
    · intro hv
      refine LinearMap.ext_on_range (v := h) hspan ?_
      intro i
      rw [hsymm v (h i), hB i v, hv i]
      simp
  have hfix_alpha : ∀ v, (∀ i, α i v = 0) → ∀ g ∈ e6Weyl hα, g v = v := by
    intro v hv g hg
    refine Subgroup.closure_induction (k := Set.range fun i => reflection (hα i))
      (p := fun g _ => g v = v) ?_ ?_ ?_ ?_ hg
    · rintro s ⟨i, rfl⟩
      rw [reflection_apply, hv i, zero_smul, sub_zero]
    · simp
    · intro a b _ _ ha hb
      rw [LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha
      have h := congrArg (fun w => a⁻¹ w) ha
      simpa using h.symm
  let r : V := Fintype.linearCombination (ZMod 3) h cartanE6KernelVec
  have hr_alpha : ∀ i, α i r = 0 := by
    intro i
    change α i (Fintype.linearCombination (ZMod 3) h cartanE6KernelVec) = 0
    rw [apply_linearCombination_eq_cartanE6ModThree hP i cartanE6KernelVec]
    have h := congrFun cartanE6ModThree_mulVec_cartanE6KernelVec i
    simpa using h
  have hr_ne : r ≠ 0 := by
    have hli : LinearIndependent (ZMod 3) h :=
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := h)
        (spans := by rw [hspan])
        (card_eq := by simp [finrank_eq_six hV])
    have hinj := hli.fintypeLinearCombination_injective
    intro h0
    have h1 : cartanE6KernelVec = 0 := by
      apply hinj
      simpa using h0
    exact cartanE6KernelVec_ne_zero h1
  have hr_rad : r ∈ LinearMap.ker B := (hmem_ker r).mpr hr_alpha
  have hr_line : r ∈ (ZMod 3) ∙ x := by
    apply hfix r
    intro g hg
    rw [hfix_alpha r hr_alpha g (hA hg), sub_self]
    exact Submodule.zero_mem _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr_line
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hr_ne hc.symm
  have hx_rad : x ∈ LinearMap.ker B := by
    have hx_eq : x = c⁻¹ • r := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hx_eq]
    exact Submodule.smul_mem _ _ hr_rad
  have hker_le : LinearMap.ker B ≤ (ZMod 3) ∙ x := by
    intro v hv
    apply hfix v
    intro g hg
    rw [hfix_alpha v ((hmem_ker v).mp hv) g (hA hg), sub_self]
    exact Submodule.zero_mem _
  have hrad_eq : LinearMap.ker B = (ZMod 3) ∙ x :=
    le_antisymm hker_le
      ((Submodule.span_singleton_le_iff_mem x (LinearMap.ker B)).mpr hx_rad)
  obtain ⟨f, hfne, hkerf⟩ := exists_functional_ker_eq hH hV
  have hf_x : f x = 0 := by
    have hxm : x ∈ LinearMap.ker f := by rwa [hkerf]
    exact LinearMap.mem_ker.mp hxm
  have hf_ann : f ∈ (LinearMap.ker B).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    rw [hrad_eq] at hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    rw [← ha, map_smul, smul_eq_mul, hf_x, mul_zero]
  have hflip : B.flip = B := by
    ext u v
    rw [LinearMap.BilinForm.flip_apply]
    exact (hsymm u v).symm
  have hrange : (LinearMap.ker B).dualAnnihilator = LinearMap.range B := by
    have h := LinearMap.dualCoannihilator_range_eq_ker_flip (B := B)
    have hker : LinearMap.ker (LinearMap.flip B) = LinearMap.ker B :=
      congrArg LinearMap.ker hflip
    rw [hker] at h
    rw [← h]
    exact Subspace.dualCoannihilator_dualAnnihilator_eq
  have hf_range : f ∈ LinearMap.range B := by
    rw [← hrange]
    exact hf_ann
  obtain ⟨w, hw⟩ := hf_range
  have hw_not_rad : w ∉ LinearMap.ker B := by
    intro hwmem
    have hzero : B w = 0 := hwmem
    exact hfne (hw.symm.trans hzero)
  have hiso : ∀ g ∈ e6Weyl hα, ∀ u v, B (g u) (g v) = B u v := by
    intro g hg
    refine Subgroup.closure_induction (k := Set.range fun i => reflection (hα i))
      (p := fun g _ => ∀ u v : V, B (g u) (g v) = B u v) ?_ ?_ ?_ ?_ hg
    · rintro s ⟨i, rfl⟩ u v
      exact bilinForm_reflection_of_span_top hP hspan hB hα i u v
    · intro u v
      simp
    · intro a b _ _ ha hb u v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
    · intro a _ ha u v
      have h := ha (a⁻¹ u) (a⁻¹ v)
      simpa using h.symm
  have hgw : ∀ g ∈ A, g w - w ∈ LinearMap.ker B := by
    intro g hg
    rw [LinearMap.mem_ker]
    refine LinearMap.ext_on_range (v := h) hspan ?_
    intro i
    have hginv : g⁻¹ ∈ A := (Subgroup.inv_mem_iff A).mpr hg
    have h1 : B (g w) (h i) = B w (g⁻¹ (h i)) := by
      have h := hiso g (hA hg) w (g⁻¹ (h i))
      simpa using h
    have h2 : B w (g⁻¹ (h i)) = f (g⁻¹ (h i)) := by
      rw [hw]
    have h3 : f (g⁻¹ (h i)) = f (h i) := by
      have hmem : g⁻¹ (h i) - h i ∈ H := hAH g⁻¹ hginv (h i)
      have h0 : f (g⁻¹ (h i) - h i) = 0 := by
        have hmem' : g⁻¹ (h i) - h i ∈ LinearMap.ker f := by rwa [hkerf]
        exact LinearMap.mem_ker.mp hmem'
      rwa [map_sub, sub_eq_zero] at h0
    have h4 : B w (h i) = f (h i) := by
      rw [hw]
    rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]
    simp
  have hw_line : w ∈ (ZMod 3) ∙ x := by
    apply hfix w
    intro g hg
    rw [← hrad_eq]
    exact hgw g hg
  have hw_rad : w ∈ LinearMap.ker B := by
    rw [hrad_eq]
    exact hw_line
  exact hw_not_rad hw_rad

theorem spanH_eq_of_card_six
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hV : Nat.card V = 3 ^ 6)
    (hW : Nat.card (e6Weyl hα) = 51840) {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hA : A ≤ e6Weyl hα) (hcardA : 720 ≤ Nat.card A) {x : V} (hx : x ≠ 0)
    (hAx : ∀ g ∈ A, g x = x)
    {H : Submodule (ZMod 3) V} (hH : Nat.card H = 3 ^ 5) (hxH : x ∈ H)
    (hAH : ∀ g ∈ A, ∀ v, g v - v ∈ H)
    (hfix : ∀ v, (∀ g ∈ A, g v - v ∈ (ZMod 3) ∙ x) → v ∈ (ZMod 3) ∙ x) :
    spanH h = H := by
  classical
  have hS_ne_top : spanH h ≠ ⊤ :=
    span_ne_top_of_card_six hP hα hV hW hA hcardA hx hAx hH hxH hAH hfix
  have hfinS : finrank (ZMod 3) (spanH h) = 5 := by
    have hlt : finrank (ZMod 3) (spanH h) < finrank (ZMod 3) V :=
      Submodule.finrank_lt hS_ne_top
    have hV6 : finrank (ZMod 3) V = 6 := finrank_eq_six hV
    have hge : 5 ≤ finrank (ZMod 3) (spanH h) := five_le_finrank_span hP
    omega
  have hS_card : Nat.card (spanH h) = 3 ^ 5 := by
    rw [natCard_submodule, hfinS]
  by_contra hSH
  have hHfin : finrank (ZMod 3) H = 5 := by
    have hc := natCard_submodule H
    rw [hH] at hc
    exact (Nat.pow_right_injective (by norm_num) hc).symm
  have hnotle : ¬ spanH h ≤ H := by
    intro hle
    exact hSH (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinS, hHfin]))
  obtain ⟨s, hsS, hsH⟩ := Set.not_subset.mp hnotle
  obtain ⟨f, hfne, hkerf⟩ := exists_functional_ker_eq hH hV
  have hfs : f s ≠ 0 := by
    intro h0
    apply hsH
    rw [← hkerf]
    exact LinearMap.mem_ker.mpr h0
  let φ : Dual (ZMod 3) (spanH h) := f.comp (spanH h).subtype
  have hφs : φ ⟨s, hsS⟩ = f s := rfl
  have hφne : φ ≠ 0 := by
    intro h0
    have h0' : φ ⟨s, hsS⟩ = 0 := by rw [h0]; rfl
    rw [hφs] at h0'
    exact hfs h0'
  obtain ⟨B', hB'⟩ := exists_bilinForm_span hP hS_card
  have hsymm : ∀ u v : spanH h, B' u v = B' v u :=
    bilinForm_symm (alphaIn_hIn hP) hS_card hB'
  have hB'nondeg : B'.Nondegenerate := by
    refine ⟨?_, ?_⟩
    · intro u hu
      exact bilinForm_nondegenerate (alphaIn_hIn hP) hS_card hB' hu
    · intro u hu
      exact bilinForm_nondegenerate (alphaIn_hIn hP) hS_card hB'
        (fun v => by rw [hsymm u v]; exact hu v)
  let w : spanH h := (B'.toDual hB'nondeg).symm φ
  have hwy : ∀ y : spanH h, B' w y = φ y := by
    intro y
    exact LinearMap.BilinForm.apply_toDual_symm_apply (B := B') (hB := hB'nondeg) φ y
  have hwne : w ≠ 0 := by
    intro h0
    apply hφne
    ext y
    rw [← hwy y, h0]
    simp
  have hwfix : ∀ g ∈ A, g (w : V) = (w : V) := by
    intro g hg
    obtain ⟨g', hg', hg'eq⟩ := restrict_mem_e6Weyl (hα := hα) (hA hg)
    have hφg : ∀ y : spanH h, φ (g' y) = φ y := by
      intro y
      change f (g' y : V) = f (y : V)
      rw [hg'eq y]
      have hmem : g (y : V) - y ∈ H := hAH g hg (y : V)
      have h0 : f (g (y : V) - y) = 0 := by
        rw [← hkerf] at hmem
        exact hmem
      rwa [map_sub, sub_eq_zero] at h0
    have hiso : ∀ u v : spanH h, B' (g' u) (g' v) = B' u v :=
      bilinForm_apply_e6Weyl (alphaIn_hIn hP) hS_card hB' (alphaIn_self hα) hg'
    have hgw : g' w = w := by
      have hsub : g' w - w = 0 := by
        apply hB'nondeg.1
        intro y
        have h1 : B' (g' w) y = B' w (g'⁻¹ y) := by
          have h := hiso w (g'⁻¹ y)
          simpa using h
        have h2 : B' w (g'⁻¹ y) = φ (g'⁻¹ y) := hwy _
        have h3 : φ (g'⁻¹ y) = φ y := by
          have h := hφg (g'⁻¹ y)
          simpa using h.symm
        have h4 : B' w y = φ y := hwy y
        rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]
      exact sub_eq_zero.mp hsub
    have h1 : (g' w : V) = g (w : V) := hg'eq w
    rw [hgw] at h1
    exact h1.symm
  have hw_line : (w : V) ∈ (ZMod 3) ∙ x := by
    apply hfix (w : V)
    intro g hg
    rw [hwfix g hg, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw_line
  have hc0 : c ≠ 0 := by
    intro h0
    apply hwne
    apply Subtype.ext
    rw [← hc, h0, zero_smul]
    rfl
  have hx_eq : x = c⁻¹ • (w : V) := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hxS : x ∈ spanH h := by
    rw [hx_eq]
    exact Submodule.smul_mem _ _ w.2
  have hfx : f x = 0 := by
    rw [← hkerf] at hxH
    exact LinearMap.mem_ker.mp hxH
  have hww : B' w w = 0 := by
    have h1 := hwy w
    have h2 : φ w = f (w : V) := rfl
    have h3 : f (w : V) = 0 := by
      rw [← hc, map_smul, smul_eq_mul, hfx, mul_zero]
    rw [h1, h2, h3]
  have hxw : (⟨x, hxS⟩ : spanH h) = c⁻¹ • w :=
    Subtype.ext (by simpa using hx_eq)
  have hxx0 : B' ⟨x, hxS⟩ ⟨x, hxS⟩ = 0 := by
    rw [hxw]
    have h1 : B' (c⁻¹ • w) (c⁻¹ • w) = (c⁻¹ * c⁻¹) * B' w w := by
      simp [smul_eq_mul, mul_assoc]
    rw [h1, hww, mul_zero]
  rcases stabilizer_cases_of_spanH hP hα hW hS_card hB' hxS hx with
    ⟨h2, -⟩ | ⟨h0, hstab⟩ | ⟨h1, hstab⟩
  · rw [hxx0] at h2
    exact absurd h2 (by decide)
  · have hle := card_le_stabilizer_of_forall_apply_eq (hα := hα) hA hAx
    rw [hstab] at hle
    omega
  · have hle := card_le_stabilizer_of_forall_apply_eq (hα := hα) hA hAx
    rw [hstab] at hle
    omega
