module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4DiagQuat
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4LeviComm
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4LeviVec
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4QuatLift
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4Q8

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm spEnd spEnd_apply)
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull

variable {F : Type} [Field F]

theorem eq_top_of_levi (h2 : (2 : F) ≠ 0) {H : Subgroup (StatedSp 2 F)}
    {X Y : Module.End F (Fin 2 ⊕ Fin 2 → F)}
    (hXadj : ∀ y z, spForm 2 F (X y) z = -spForm 2 F y (X z))
    (hYadj : ∀ y z, spForm 2 F (Y y) z = -spForm 2 F y (Y z)) {lam μ l k : F}
    (hlam : lam ≠ 0) (hXX : ∀ y, X (X y) = (lam * lam) • y) (hμ : μ ≠ 0)
    (hYY : ∀ y, Y (Y y) = -μ • y) (hXY : ∀ y, X (Y y) = -Y (X y))
    (hani : ∀ x, x ≠ 0 → (X x = lam • x ∨ X x = -lam • x) → spForm 2 F x (Y x) ≠ 0)
    (hlk : l * l + μ * (k * k) = 1) (hk : k ≠ 0)
    (hHX : ∀ g : StatedSp 2 F, (∀ y, spEnd g (X y) = X (spEnd g y)) → g ∈ H)
    (hHY : ∀ g : StatedSp 2 F, (∀ y, spEnd g (Y y) = Y (spEnd g y)) → g ∈ H) :
    H = ⊤ := by
  classical
  have h8 : (8 : F) ≠ 0 := by
    have h : (8 : F) = 2 * 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have hself : ∀ y : Fin 2 ⊕ Fin 2 → F, spForm 2 F y y = 0 := fun y =>
    LinearMap.BilinForm.IsAlt.self_eq_zero
      (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := F)) y
  have hcase : ∀ (lam' : F), lam' ≠ 0 → (∀ y, X (X y) = (lam' * lam') • y) →
      ∀ x : Fin 2 ⊕ Fin 2 → F, x ≠ 0 → X x = lam' • x →
      (∀ v, v ≠ 0 → X v = -lam' • v → spForm 2 F v (Y v) ≠ 0) →
      spForm 2 F x (Y x) ≠ 0 → TransCenter H x := by
    intro lam' hlam' hXX' x hx0 hx hani' hxY
    obtain ⟨v, hv0, hXv, hxv⟩ :=
      exists_orth_eig (F := F) h2 hlam' hXX' hμ hYY hXY hx hxY
    have hYx : X (Y x) = (-lam') • (Y x) := by
      rw [hXY, hx, map_smul, neg_smul]
    have hvYx : spForm 2 F v (Y x) = 0 :=
      form_eq_zero_of_skew_eig (r := 2) h2 hXadj (neg_ne_zero.mpr hlam') hXv hYx
    have hvx : spForm 2 F v x = 0 := by
      rw [CFSG.LocalAnalysis.WeakClosure81.SpSeitz.spForm_swap, hxv, neg_zero]
    obtain ⟨g, hgY, hgx, hgv⟩ :=
      exists_sp_fix_of_skew (Y := Y) hYadj hYY hxY hlk
    have hgvv : spEnd g v = l • v + k • Y v := hgv v hvx hvYx
    have hgH : g ∈ H := hHY g hgY
    have hScomm : ∀ s : F, ∀ y,
        spEnd (spTransvection (x + v) s * spTransvection (x - v) (-s)) (X y) =
          X (spEnd (spTransvection (x + v) s * spTransvection (x - v) (-s)) y) :=
      fun s => shortRoot_commute (X := X) hXadj hx hXv hxv s
    have hSH : ∀ s : F,
        spTransvection (x + v) s * spTransvection (x - v) (-s) ∈ H :=
      fun s => hHX _ (hScomm s)
    have hgS : ∀ t : F,
        g * (spTransvection (x + v) t * spTransvection (x - v) (-t)) * g⁻¹ ∈ H :=
      fun t => H.mul_mem (H.mul_mem hgH (hSH t)) (H.inv_mem hgH)
    have hgSeq : ∀ t : F,
        g * (spTransvection (x + v) t * spTransvection (x - v) (-t)) * g⁻¹ =
          spTransvection (x + spEnd g v) t * spTransvection (x - spEnd g v) (-t) := by
      intro t
      calc g * (spTransvection (x + v) t * spTransvection (x - v) (-t)) * g⁻¹
          = (g * spTransvection (x + v) t * g⁻¹) *
              (g * spTransvection (x - v) (-t) * g⁻¹) := by group
        _ = spTransvection (spEnd g (x + v)) t * spTransvection (spEnd g (x - v)) (-t) := by
              rw [spTransvection_conj, spTransvection_conj]
        _ = spTransvection (x + spEnd g v) t * spTransvection (x - spEnd g v) (-t) := by
              rw [map_add, map_sub, hgx]
    have hxYv : spForm 2 F x (Y v) = 0 := by
      have h1 : spForm 2 F (Y x) v = 0 := by
        rw [CFSG.LocalAnalysis.WeakClosure81.SpSeitz.spForm_swap, hvYx, neg_zero]
      have h2 := hYadj x v
      rw [h1] at h2
      exact neg_eq_zero.mp h2.symm
    have hxgv : spForm 2 F x (spEnd g v) = 0 := by
      rw [hgvv, map_add, map_smul, map_smul, hxv, hxYv]
      ring
    have hκ : spForm 2 F v (spEnd g v) = k * spForm 2 F v (Y v) := by
      rw [hgvv, map_add, map_smul, map_smul, hself]
      ring
    have hκ0 : spForm 2 F v (spEnd g v) ≠ 0 := by
      rw [hκ]
      exact mul_ne_zero hk (hani' v hv0 hXv)
    have hcomm : ∀ s t : F,
        spTransvection x (-8 * s * t * spForm 2 F v (spEnd g v)) ∈ H := by
      intro s t
      have hQH : spTransvection (x + spEnd g v) t *
          spTransvection (x - spEnd g v) (-t) ∈ H := by
        rw [← hgSeq t]
        exact hgS t
      have h := shortRoot_commutator (w := x) (v := v) (v' := spEnd g v) hxv hxgv s t
      rw [← h]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hSH s) hQH) (H.inv_mem (hSH s)))
        (H.inv_mem hQH)
    intro tau
    have h8κ : (8 : F) * spForm 2 F v (spEnd g v) ≠ 0 := mul_ne_zero h8 hκ0
    have hs : -8 * (-tau / (8 * spForm 2 F v (spEnd g v))) * 1 *
        spForm 2 F v (spEnd g v) = tau := by
      field_simp
    rw [← hs]
    exact hcomm _ 1

  have heig : ∀ x : Fin 2 ⊕ Fin 2 → F, x ≠ 0 →
      (X x = lam • x ∨ X x = -lam • x) → TransCenter H x := by
    intro x hx0 hx
    rcases hx with hx | hx
    · exact hcase lam hlam hXX x hx0 hx (fun v hv0 hv => hani v hv0 (Or.inr hv))
        (hani x hx0 (Or.inl hx))
    · refine hcase (-lam) (neg_ne_zero.mpr hlam) (fun y => by rw [neg_mul_neg]; exact hXX y)
        x hx0 hx ?_ (hani x hx0 (Or.inr hx))
      intro v hv0 hv
      rw [neg_neg] at hv
      exact hani v hv0 (Or.inl hv)
  refine eq_top_of_transCenter ?_
  refine transCenter_of_eig (r := 2) h2 hXadj hlam hXX ?_
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    exact transCenter_zero
  · exact heig x hx0 hx

theorem seitzFourSp4DiagQuat_holds : SeitzFourSp4DiagQuat := by
  intro F _ _ hF E hE h4 hnoW a B ν haE ha1 hBE hab hA2 hBform hν hB2 hAB
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hν0 : ν ≠ 0 := fun h => hν ⟨0, by rw [h]; ring⟩
  have hb1 : conjAut 2 F B ≠ 1 :=
    conjAut_ne_one_of_anticommute (r := 2) (by norm_num) h2 hAB
  set MA : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((a : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hMA
  set MB : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hMB
  have hA2' : MA * MA = -1 := by rw [hMA]; exact hA2
  have hAform0 : MAᵀ * formJ 2 F * MA = formJ 2 F := by
    have h := SymplecticTorusWeyl.mem_statedSp_iff.mp a.2
    simpa [hMA] using h
  have hAform : MAᵀ * formJ 2 F * MA = (1 : F) • formJ 2 F := by
    rw [hAform0, one_smul]
  have hBform' : MBᵀ * formJ 2 F * MB = ν • formJ 2 F := by rw [hMB]; exact hBform
  have hB2' : MB * MB = (-ν) • 1 := by rw [hMB]; exact hB2
  have hAB' : MA * MB = -(MB * MA) := by rw [hMA, hMB]; exact hAB
  have hA2sq : MA * MA = (-1 : F) • 1 := by rw [hA2', neg_one_smul]
  let H : Subgroup (StatedSp 2 F) := (planeClosure E).comap (proj 2 F)
  have hHA : ∀ g : StatedSp 2 F,
      (∀ y, spEnd g (spEnd a y) = spEnd a (spEnd g y)) → g ∈ H :=
    fun g hg => mem_comap_of_commute_inner (r := 2) haE ha1 hg
  have hHB : ∀ g : StatedSp 2 F,
      (∀ y, spEnd g (Matrix.mulVecLin MB y) = Matrix.mulVecLin MB (spEnd g y)) → g ∈ H := by
    intro g hg
    refine mem_comap_of_commute_gsp (r := 2) hBE hb1 (fun y => ?_)
    have h := hg y
    rwa [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at h
  have hAl : ∀ y, spEnd a y = MA *ᵥ y := by
    intro y
    rw [spEnd_apply, hMA]
  have hAA : ∀ y, spEnd a (spEnd a y) = -y := by
    intro y
    rw [hAl, hAl, Matrix.mulVec_mulVec, hA2', Matrix.neg_mulVec, Matrix.one_mulVec]
  have hBB : ∀ y, Matrix.mulVecLin MB (Matrix.mulVecLin MB y) = -ν • y := by
    intro y
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hB2',
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hABl : ∀ y, spEnd a (Matrix.mulVecLin MB y) = -Matrix.mulVecLin MB (spEnd a y) := by
    intro y
    rw [hAl, Matrix.mulVecLin_apply, hAl, Matrix.mulVec_mulVec, hAB', Matrix.neg_mulVec,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  have finish : H = ⊤ → PlaneGen E := by
    intro htop
    rw [PlaneGen]
    calc planeClosure E = Subgroup.map (proj 2 F) H := by
          rw [show H = (planeClosure E).comap (proj 2 F) from rfl]
          exact (Subgroup.map_comap_eq_self_of_surjective
            (proj_surjective (r := 2) (K := F)) (planeClosure E)).symm
      _ = ⊤ := by
            rw [htop, Subgroup.map_top_of_surjective _ (proj_surjective (r := 2) (K := F))]
  by_cases hsq : IsSquare (-1 : F)
  ·
    obtain ⟨i, hi⟩ := hsq
    have hine : i ≠ 0 := by
      intro h
      rw [h, mul_zero] at hi
      exact one_ne_zero (neg_eq_zero.mp hi)
    have hν1 : ν + 1 ≠ 0 := by
      intro h
      apply hν
      exact ⟨i, by rw [← hi]; exact add_eq_zero_iff_eq_neg.mp h⟩
    have hXXi : ∀ y, spEnd a (spEnd a y) = (i * i) • y := by
      intro y
      rw [hAA, ← hi, neg_one_smul]
    have hlk : (ν - 1) / (ν + 1) * ((ν - 1) / (ν + 1)) +
        ν * ((-2) / (ν + 1) * ((-2) / (ν + 1))) = 1 := by
      field_simp
      ring
    have hk : (-2) / (ν + 1) ≠ 0 := div_ne_zero (neg_ne_zero.mpr h2) hν1
    have hskewA : ∀ y z, spForm 2 F (MA *ᵥ y) z = -spForm 2 F y (MA *ᵥ z) :=
      spForm_mulVec_skew (r := 2) one_ne_zero hAform hA2sq
    have hXadjA : ∀ y z, spForm 2 F (spEnd a y) z = -spForm 2 F y (spEnd a z) :=
      fun y z => by rw [hAl, hAl]; exact hskewA y z
    have hYadjB : ∀ y z,
        spForm 2 F (Matrix.mulVecLin MB y) z = -spForm 2 F y (Matrix.mulVecLin MB z) := by
      intro y z
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
      exact spForm_mulVec_skew (r := 2) hν0 hBform' hB2' y z
    have hani_i : ∀ x : Fin 2 ⊕ Fin 2 → F, x ≠ 0 →
        (spEnd a x = i • x ∨ spEnd a x = -i • x) →
        spForm 2 F x (Matrix.mulVecLin MB x) ≠ 0 := by
      intro x hx0 hx hzero
      exfalso
      have hmem1 : x ∈ Submodule.span F
          ({x, Matrix.mulVecLin MB x} : Set (Fin 2 ⊕ Fin 2 → F)) :=
        Submodule.subset_span (by simp)
      have hmem2 : Matrix.mulVecLin MB x ∈ Submodule.span F
          ({x, Matrix.mulVecLin MB x} : Set (Fin 2 ⊕ Fin 2 → F)) :=
        Submodule.subset_span (by simp)
      have hMx : MA *ᵥ x = i • x ∨ MA *ᵥ x = -i • x := by
        rcases hx with hx | hx
        · left; rw [← hAl]; exact hx
        · right; rw [← hAl]; exact hx
      have hax : MA *ᵥ x ∈ Submodule.span F
          ({x, Matrix.mulVecLin MB x} : Set (Fin 2 ⊕ Fin 2 → F)) := by
        rcases hMx with h | h
        · rw [h]; exact Submodule.smul_mem _ i hmem1
        · rw [h]; exact Submodule.smul_mem _ (-i) hmem1
      have h1 : MA *ᵥ (Matrix.mulVecLin MB x) = -Matrix.mulVecLin MB (MA *ᵥ x) := by
        rw [← hAl (Matrix.mulVecLin MB x), hABl, hAl x]
      have hay : MA *ᵥ (Matrix.mulVecLin MB x) ∈ Submodule.span F
          ({x, Matrix.mulVecLin MB x} : Set (Fin 2 ⊕ Fin 2 → F)) := by
        have hstep : ∀ c : F, MA *ᵥ x = c • x →
            MA *ᵥ (Matrix.mulVecLin MB x) = (-c) • Matrix.mulVecLin MB x := by
          intro c hc
          rw [h1, hc, map_smul, neg_smul]
        rcases hMx with h | h
        · rw [hstep i h]; exact Submodule.smul_mem _ (-i) hmem2
        · rw [hstep (-i) h]; exact Submodule.smul_mem _ (-(-i)) hmem2
      have hbx : MB *ᵥ x ∈ Submodule.span F
          ({x, Matrix.mulVecLin MB x} : Set (Fin 2 ⊕ Fin 2 → F)) := by
        simpa using hmem2
      have hby : MB *ᵥ (Matrix.mulVecLin MB x) ∈ Submodule.span F
          ({x, Matrix.mulVecLin MB x} : Set (Fin 2 ⊕ Fin 2 → F)) := by
        have h2' : MB *ᵥ (Matrix.mulVecLin MB x) = -ν • x := by
          rw [← Matrix.mulVecLin_apply, hBB]
        rw [h2']
        exact Submodule.smul_mem _ (-ν) hmem1
      exact false_of_isotropic_pair (r := 2) (by norm_num) hE h4 haE ha1 hBE hb1 hab hnoW
        hx0 hzero hax hay hbx hby
    have hHtop : H = ⊤ :=
      eq_top_of_levi (H := H) h2 (X := spEnd a) (Y := Matrix.mulVecLin MB)
        (lam := i) (μ := ν) (l := (ν - 1) / (ν + 1)) (k := (-2) / (ν + 1))
        hXadjA hYadjB hine hXXi hν0 hBB hABl hani_i hlk hk hHA hHB
    exact finish hHtop
  ·
    obtain ⟨s, hs⟩ :=
      CFSG.LocalAnalysis.WeakClosure81.SpSeitz.isSquare_neg_of_not hsq hν0 hν
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, mul_zero] at hs
      exact hν0 (neg_eq_zero.mp hs)
    have hXXs : ∀ y, Matrix.mulVecLin MB (Matrix.mulVecLin MB y) = (s * s) • y := by
      intro y
      rw [hBB, ← hs]
    have hYY1 : ∀ y, spEnd a (spEnd a y) = (-1 : F) • y := by
      intro y
      rw [hAA, neg_one_smul]
    have hXYB : ∀ y, Matrix.mulVecLin MB (spEnd a y) = -spEnd a (Matrix.mulVecLin MB y) := by
      intro y
      have h := congrArg Neg.neg (hABl y)
      rw [neg_neg] at h
      exact h.symm
    have hXadjB : ∀ y z,
        spForm 2 F (Matrix.mulVecLin MB y) z = -spForm 2 F y (Matrix.mulVecLin MB z) := by
      intro y z
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
      exact spForm_mulVec_skew (r := 2) hν0 hBform' hB2' y z
    have hskewA : ∀ y z, spForm 2 F (MA *ᵥ y) z = -spForm 2 F y (MA *ᵥ z) :=
      spForm_mulVec_skew (r := 2) one_ne_zero hAform hA2sq
    have hYadjA : ∀ y z, spForm 2 F (spEnd a y) z = -spForm 2 F y (spEnd a z) :=
      fun y z => by rw [hAl, hAl]; exact hskewA y z
    have hani_s : ∀ x : Fin 2 ⊕ Fin 2 → F, x ≠ 0 →
        (Matrix.mulVecLin MB x = s • x ∨ Matrix.mulVecLin MB x = -s • x) →
        spForm 2 F x (spEnd a x) ≠ 0 := by
      intro x hx0 hx hzero
      exfalso
      have hmem1 : x ∈ Submodule.span F
          ({x, MA *ᵥ x} : Set (Fin 2 ⊕ Fin 2 → F)) :=
        Submodule.subset_span (by simp)
      have hmem2 : MA *ᵥ x ∈ Submodule.span F
          ({x, MA *ᵥ x} : Set (Fin 2 ⊕ Fin 2 → F)) :=
        Submodule.subset_span (by simp)
      have hax : MA *ᵥ x ∈ Submodule.span F
          ({x, MA *ᵥ x} : Set (Fin 2 ⊕ Fin 2 → F)) := hmem2
      have hay : MA *ᵥ (MA *ᵥ x) ∈ Submodule.span F
          ({x, MA *ᵥ x} : Set (Fin 2 ⊕ Fin 2 → F)) := by
        have h2' : MA *ᵥ (MA *ᵥ x) = -x := by
          simpa only [hAl] using hAA x
        rw [h2']
        exact Submodule.neg_mem _ hmem1
      have hMx : MB *ᵥ x = s • x ∨ MB *ᵥ x = -s • x := by
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hbx : MB *ᵥ x ∈ Submodule.span F
          ({x, MA *ᵥ x} : Set (Fin 2 ⊕ Fin 2 → F)) := by
        rcases hMx with h | h
        · rw [h]; exact Submodule.smul_mem _ s hmem1
        · rw [h]; exact Submodule.smul_mem _ (-s) hmem1
      have h1 : MB *ᵥ (MA *ᵥ x) = -spEnd a (Matrix.mulVecLin MB x) := hXYB x
      have hby : MB *ᵥ (MA *ᵥ x) ∈ Submodule.span F
          ({x, MA *ᵥ x} : Set (Fin 2 ⊕ Fin 2 → F)) := by
        have hstep : ∀ c : F, Matrix.mulVecLin MB x = c • x →
            MB *ᵥ (MA *ᵥ x) = (-c) • (MA *ᵥ x) := by
          intro c hc
          rw [h1, hc, map_smul, neg_smul, ← hAl x]
        rcases hMx with h | h
        · rw [hstep s h]; exact Submodule.smul_mem _ (-s) hmem2
        · rw [hstep (-s) h]; exact Submodule.smul_mem _ (-(-s)) hmem2
      exact false_of_isotropic_pair (r := 2) (by norm_num) hE h4 haE ha1 hBE hb1 hab hnoW
        hx0 hzero hax hay hbx hby
    have hHtop : H = ⊤ :=
      eq_top_of_levi (H := H) h2 (X := Matrix.mulVecLin MB) (Y := spEnd a)
        (lam := s) (μ := 1) (l := 0) (k := 1)
        hXadjB hYadjA hs0 hXXs one_ne_zero hYY1 hXYB hani_s (by norm_num) one_ne_zero hHB hHA
    exact finish hHtop

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
