module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Model
public import CFSG.LocalAnalysis.StandardType.FS81.RootS3Supp
public import CFSG.LargeExtraspecial.DW4Burn
public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalInvolution.WeakCT
open CFSG.LargeExtraspecial.DW.W4

theorem commute_of_polar_commSpace {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hq : (QuadraticMap.polarBilin q).Nondegenerate)
    {z z' : V ≃ₗ[ZMod 2] V} (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hz' : z' ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (h : ∀ a ∈ CFSG.LargeExtraspecial.DW.W4.commSpace z,
      ∀ b ∈ CFSG.LargeExtraspecial.DW.W4.commSpace z',
      QuadraticMap.polar q a b = 0) : z * z' = z' * z := by
  apply LinearEquiv.ext; intro v
  have hfix_z : CFSG.LargeExtraspecial.DW.W4.commSpace z' ≤
      CFSG.LargeExtraspecial.DW.W4.fixSpace z := by
    rw [show CFSG.LargeExtraspecial.DW.W4.fixSpace z =
        LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin q)
          (CFSG.LargeExtraspecial.DW.W4.commSpace z) from
      CFSG.LargeExtraspecial.fixSpace_eq_orthogonal_commSpace_of_mem hq hz]
    intro b hb
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro a ha
    exact h a ha b hb
  have hfix_z' : CFSG.LargeExtraspecial.DW.W4.commSpace z ≤
      CFSG.LargeExtraspecial.DW.W4.fixSpace z' := by
    rw [show CFSG.LargeExtraspecial.DW.W4.fixSpace z' =
        LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin q)
          (CFSG.LargeExtraspecial.DW.W4.commSpace z') from
      CFSG.LargeExtraspecial.fixSpace_eq_orthogonal_commSpace_of_mem hq hz']
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact h a ha b hb
  have h1 : z' v - v ∈ CFSG.LargeExtraspecial.DW.W4.commSpace z' := by
    rw [CFSG.LargeExtraspecial.DW.W4.mem_commSpace]
    exact ⟨v, by simp⟩
  have h2 := hfix_z h1
  rw [CFSG.LargeExtraspecial.DW.W4.mem_fixSpace] at h2
  have h3 : z v - v ∈ CFSG.LargeExtraspecial.DW.W4.commSpace z := by
    rw [CFSG.LargeExtraspecial.DW.W4.mem_commSpace]
    exact ⟨v, by simp⟩
  have h4 := hfix_z' h3
  rw [CFSG.LargeExtraspecial.DW.W4.mem_fixSpace] at h4
  calc
    z (z' v) = z (z' v - v) + z v := by rw [map_sub, sub_add_cancel]
    _ = (z' v - v) + z v := by rw [h2]
    _ = z' v + z v - v := by abel
    _ = z v + z' v - v := by abel
    _ = z' (z v - v) + z' v := by rw [h4]; abel
    _ = z' (z v) := by rw [map_sub, sub_add_cancel]

theorem commute_of_polar_subCommSpace {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hq : (QuadraticMap.polarBilin q).Nondegenerate)
    {Z Z' : Subgroup (V ≃ₗ[ZMod 2] V)} (hZ : Z ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hZ' : Z' ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (h : ∀ a ∈ subCommSpace Z, ∀ b ∈ subCommSpace Z', QuadraticMap.polar q a b = 0) :
    ∀ z ∈ Z, ∀ z' ∈ Z', z * z' = z' * z := by
  intro z hz z' hz'
  refine commute_of_polar_commSpace hq (hZ hz) (hZ' hz') ?_
  intro a ha b hb
  exact h a (Submodule.mem_iSup_of_mem z (Submodule.mem_iSup_of_mem hz ha))
    b (Submodule.mem_iSup_of_mem z' (Submodule.mem_iSup_of_mem hz' hb))

theorem planeSpan_mono {P P' : Finset (Fin 6)} (h : P ⊆ P') : planeSpan P ≤ planeSpan P' := by
  intro v hv i hi
  exact hv i (fun hmem => hi (h hmem))

theorem polar_eq_zero_of_disjoint {P P' : Finset (Fin 6)} (h : Disjoint P P') :
    ∀ a ∈ planeSpan P, ∀ b ∈ planeSpan P', QuadraticMap.polar Q12 a b = 0 := by
  intro a ha b hb
  rw [CFSG.LieType.Universal.Spin.polar_quadPlus]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hP : i ∈ P
  · have hP' : i ∉ P' := Finset.disjoint_left.mp h hP
    have hb1 : b (Sum.inl i) = 0 := (mem_planeSpan.mp hb i hP').1
    have hb2 : b (Sum.inr i) = 0 := (mem_planeSpan.mp hb i hP').2
    simp [hb1, hb2]
  · have ha1 : a (Sum.inl i) = 0 := (mem_planeSpan.mp ha i hP).1
    have ha2 : a (Sum.inr i) = 0 := (mem_planeSpan.mp ha i hP).2
    simp [ha1, ha2]

noncomputable def planeSpanEquiv (P : Finset (Fin 6)) :
    planeSpan P ≃ₗ[ZMod 2] (P ⊕ P → ZMod 2) where
  toFun v x := match x with
    | Sum.inl i => v.val (Sum.inl i)
    | Sum.inr i => v.val (Sum.inr i)
  invFun w := ⟨fun x => match x with
    | Sum.inl i => if h : i ∈ P then w (Sum.inl ⟨i, h⟩) else 0
    | Sum.inr i => if h : i ∈ P then w (Sum.inr ⟨i, h⟩) else 0, by
      intro i hi
      simp only [dif_neg hi, and_self]⟩
  map_add' v w := by
    ext x
    rcases x with (i | i) <;> simp
  map_smul' c v := by
    ext x
    rcases x with (i | i) <;> simp
  left_inv v := by
    ext i
    rcases i with (j | j)
    · by_cases h : j ∈ P
      · simp [h]
      · simp [h, (mem_planeSpan.mp v.2 j h).1]
    · by_cases h : j ∈ P
      · simp [h]
      · simp [h, (mem_planeSpan.mp v.2 j h).2]
  right_inv w := by
    ext x
    rcases x with (i | i)
    · simp [i.2]
    · simp [i.2]

theorem finrank_Y2 : Module.finrank (ZMod 2) Y2 = 4 := by
  rw [Y2]
  rw [LinearEquiv.finrank_eq (planeSpanEquiv {2, 3})]
  rw [Module.finrank_fintype_fun_eq_card]
  decide

theorem Y2_nondeg : ∀ a ∈ Y2, (∀ b ∈ Y2, QuadraticMap.polar Q12 a b = 0) → a = 0 := by
  intro a ha h
  have ha2_inr : a (Sum.inr 2) = 0 := by
    have hb : Pi.single (Sum.inl 2) 1 ∈ Y2 := by
      rw [Y2, mem_planeSpan]
      intro i hi
      fin_cases i <;> simp_all [Pi.single_eq_of_ne]
    have := h (Pi.single (Sum.inl 2) 1) hb
    rwa [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inl] at this
  have ha2_inl : a (Sum.inl 2) = 0 := by
    have hb : Pi.single (Sum.inr 2) 1 ∈ Y2 := by
      rw [Y2, mem_planeSpan]
      intro i hi
      fin_cases i <;> simp_all [Pi.single_eq_of_ne]
    have := h (Pi.single (Sum.inr 2) 1) hb
    rwa [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr] at this
  have ha3_inr : a (Sum.inr 3) = 0 := by
    have hb : Pi.single (Sum.inl 3) 1 ∈ Y2 := by
      rw [Y2, mem_planeSpan]
      intro i hi
      fin_cases i <;> simp_all [Pi.single_eq_of_ne]
    have := h (Pi.single (Sum.inl 3) 1) hb
    rwa [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inl] at this
  have ha3_inl : a (Sum.inl 3) = 0 := by
    have hb : Pi.single (Sum.inr 3) 1 ∈ Y2 := by
      rw [Y2, mem_planeSpan]
      intro i hi
      fin_cases i <;> simp_all [Pi.single_eq_of_ne]
    have := h (Pi.single (Sum.inr 3) 1) hb
    rwa [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr] at this
  funext x
  rcases x with (i | i)
  · by_cases h : i ∈ ({2, 3} : Finset (Fin 6))
    · fin_cases i <;> simp_all [ha2_inl, ha3_inl]
    · simp [h, (mem_planeSpan.mp ha i h).1]
  · by_cases h : i ∈ ({2, 3} : Finset (Fin 6))
    · fin_cases i <;> simp_all [ha2_inr, ha3_inr]
    · simp [h, (mem_planeSpan.mp ha i h).2]

theorem nondegenerate_Q12 : (QuadraticMap.polarBilin Q12).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)

end CFSG.StandardType.FrameRoute.FS81.D6M
