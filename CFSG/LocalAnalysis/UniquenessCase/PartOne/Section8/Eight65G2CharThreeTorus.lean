module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47

private lemma mul_conj_mul (G : Type*) [Group G] (d₀ d₁ x : G) :
    (d₀ * d₁) * x * (d₀ * d₁)⁻¹ = d₀ * (d₁ * x * d₁⁻¹) * d₀⁻¹ := by
  group

private lemma conj_mul_conj (G : Type*) [Group G] (h a b : G) :
    h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by
  group

private lemma torusElt_one_conj_Xv
    (K : Type) [Field K] (s : K) :
    torusElt .G2 K (1 : Fin 2) (-1 : Kˣ) * Xv s * (torusElt .G2 K (1 : Fin 2) (-1 : Kˣ))⁻¹
      = Xv (-s) := by
  have hα : IsRoot .G2 ![1, 2] := (rootsUVBC_pos (1 : Fin 4)).1
  have key := root_torus_conjugation (τ := .G2) (R := K) (1 : Fin 2) hα (-1 : Kˣ) s
  simp only [Xv]
  rw [key]
  have hexp : (∑ j : Fin 2,
      Tag.cartan .G2 (1 : Fin 2) j * (![1, 2] : Fin 2 → ℤ) j) = 1 := by
    rw [Fin.sum_univ_two]
    decide
  change pinnedX .G2 K ![1, 2]
      ((((-1 : Kˣ) ^ (∑ j : Fin 2,
        Tag.cartan .G2 (1 : Fin 2) j * (![1, 2] : Fin 2 → ℤ) j) : Kˣ) : K) * s)
    = pinnedX .G2 K ![1, 2] (-s)
  rw [hexp]
  norm_num

private lemma torusElt_zero_conj_Xv
    (K : Type) [Field K] (s : K) :
    torusElt .G2 K (0 : Fin 2) (-1 : Kˣ) * Xv s * (torusElt .G2 K (0 : Fin 2) (-1 : Kˣ))⁻¹
      = Xv s := by
  have hα : IsRoot .G2 ![1, 2] := (rootsUVBC_pos (1 : Fin 4)).1
  have key := root_torus_conjugation (τ := .G2) (R := K) (0 : Fin 2) hα (-1 : Kˣ) s
  simp only [Xv]
  rw [key]
  have hexp : (∑ j : Fin 2,
      Tag.cartan .G2 (0 : Fin 2) j * (![1, 2] : Fin 2 → ℤ) j) = 0 := by
    rw [Fin.sum_univ_two]
    decide
  change pinnedX .G2 K ![1, 2]
      ((((-1 : Kˣ) ^ (∑ j : Fin 2,
        Tag.cartan .G2 (0 : Fin 2) j * (![1, 2] : Fin 2 → ℤ) j) : Kˣ) : K) * s)
    = pinnedX .G2 K ![1, 2] s
  rw [hexp]
  norm_num

private lemma torusElt_one_conj_Xc
    (K : Type) [Field K] (s : K) :
    torusElt .G2 K (1 : Fin 2) (-1 : Kˣ) * Xc s * (torusElt .G2 K (1 : Fin 2) (-1 : Kˣ))⁻¹
      = Xc s := by
  have hα : IsRoot .G2 ![2, 3] := (rootsUVBC_pos (3 : Fin 4)).1
  have key := root_torus_conjugation (τ := .G2) (R := K) (1 : Fin 2) hα (-1 : Kˣ) s
  simp only [Xc]
  rw [key]
  have hexp : (∑ j : Fin 2,
      Tag.cartan .G2 (1 : Fin 2) j * (![2, 3] : Fin 2 → ℤ) j) = 0 := by
    rw [Fin.sum_univ_two]
    decide
  change pinnedX .G2 K ![2, 3]
      ((((-1 : Kˣ) ^ (∑ j : Fin 2,
        Tag.cartan .G2 (1 : Fin 2) j * (![2, 3] : Fin 2 → ℤ) j) : Kˣ) : K) * s)
    = pinnedX .G2 K ![2, 3] s
  rw [hexp]
  norm_num

private lemma torusElt_zero_conj_Xc
    (K : Type) [Field K] (s : K) :
    torusElt .G2 K (0 : Fin 2) (-1 : Kˣ) * Xc s * (torusElt .G2 K (0 : Fin 2) (-1 : Kˣ))⁻¹
      = Xc (-s) := by
  have hα : IsRoot .G2 ![2, 3] := (rootsUVBC_pos (3 : Fin 4)).1
  have key := root_torus_conjugation (τ := .G2) (R := K) (0 : Fin 2) hα (-1 : Kˣ) s
  simp only [Xc]
  rw [key]
  have hexp : (∑ j : Fin 2,
      Tag.cartan .G2 (0 : Fin 2) j * (![2, 3] : Fin 2 → ℤ) j) = 1 := by
    rw [Fin.sum_univ_two]
    decide
  change pinnedX .G2 K ![2, 3]
      ((((-1 : Kˣ) ^ (∑ j : Fin 2,
        Tag.cartan .G2 (0 : Fin 2) j * (![2, 3] : Fin 2 → ℤ) j) : Kˣ) : K) * s)
    = pinnedX .G2 K ![2, 3] (-s)
  rw [hexp]
  norm_num

theorem exists_mem_adjointGroup_conj_Xv_Xc_neg_g2
    (K : Type) [Field K] :
    ∃ h : ModGL .G2 K, h ∈ adjointGroup .G2 K ∧
      ∀ s : K, h * Xv s * h⁻¹ = Xv (-s) ∧ h * Xc s * h⁻¹ = Xc (-s) := by
  refine ⟨torusElt .G2 K (0 : Fin 2) (-1 : Kˣ) * torusElt .G2 K (1 : Fin 2) (-1 : Kˣ),
    ?_, ?_⟩
  · exact mul_mem (torusElt_mem_adjointGroup (τ := .G2) (0 : Fin 2) (-1))
      (torusElt_mem_adjointGroup (τ := .G2) (1 : Fin 2) (-1))
  · intro s
    constructor
    · rw [mul_conj_mul, torusElt_one_conj_Xv K s]
      exact torusElt_zero_conj_Xv K (-s)
    · rw [mul_conj_mul, torusElt_one_conj_Xc K s]
      exact torusElt_zero_conj_Xc K s

theorem exists_conj_eq_inv_of_mem_centralizer_posUnipotent_g2
    {F : Type} [Field F] (h3 : (3 : F) = 0) (u : ↥(adjointGroup .G2 F))
    (hu : u ∈ (posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F))
    (huc : u ∈ Subgroup.centralizer
      (((posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F) : Subgroup ↥(adjointGroup .G2 F)) :
        Set ↥(adjointGroup .G2 F))) :
    ∃ t : ↥(adjointGroup .G2 F), t * u * t⁻¹ = u⁻¹ := by
  let U' : Subgroup ↥(adjointGroup .G2 F) :=
    (posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F)
  have hu' : (u : ModGL .G2 F) ∈ posUnipotent .G2 F := Subgroup.mem_subgroupOf.1 hu
  let w : ↥(posUnipotent .G2 F) := ⟨(u : ModGL .G2 F), hu'⟩
  have hw : w ∈ Subgroup.center ↥(posUnipotent .G2 F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy' : (⟨(y : ModGL .G2 F), posUnipotent_le_adjointGroup' .G2 F y.2⟩ :
        ↥(adjointGroup .G2 F)) ∈ U' := Subgroup.mem_subgroupOf.2 y.2
    have hcomm := (Subgroup.mem_centralizer_iff.1 huc) _ hy'
    apply Subtype.ext
    have hcomm' : (y : ModGL .G2 F) * (u : ModGL .G2 F) =
        (u : ModGL .G2 F) * (y : ModGL .G2 F) := by
      have := congrArg (fun x : ↥(adjointGroup .G2 F) => (x : ModGL .G2 F)) hcomm
      simpa using this
    exact hcomm'
  obtain ⟨s, t, hst⟩ := (mem_center_iff h3 w).1 hw
  obtain ⟨h, hhmem, hh⟩ := exists_mem_adjointGroup_conj_Xv_Xc_neg_g2 F
  refine ⟨⟨h, hhmem⟩, ?_⟩
  apply Subtype.ext
  have hst' : (u : ModGL .G2 F) = Xv s * Xc t := hst
  have hXv_inv : (Xv s)⁻¹ = Xv (-s) :=
    inv_eq_of_mul_eq_one_right (by rw [← Xv_add, add_neg_cancel, Xv_zero])
  have hXc_inv : (Xc t)⁻¹ = Xc (-t) :=
    inv_eq_of_mul_eq_one_right (by rw [← Xc_add, add_neg_cancel, Xc_zero])
  have htarget : ((u⁻¹ : ↥(adjointGroup .G2 F)) : ModGL .G2 F) = Xv (-s) * Xc (-t) := by
    rw [Subgroup.coe_inv, hst', mul_inv_rev, hXv_inv, hXc_inv]
    exact (comm_vc (-s) (-t)).eq.symm
  have hleft : ((⟨h, hhmem⟩ * u * ⟨h, hhmem⟩⁻¹ : ↥(adjointGroup .G2 F)) : ModGL .G2 F)
      = Xv (-s) * Xc (-t) := by
    show h * (u : ModGL .G2 F) * h⁻¹ = Xv (-s) * Xc (-t)
    calc h * (u : ModGL .G2 F) * h⁻¹
        = h * (Xv s * Xc t) * h⁻¹ := by rw [hst']
      _ = (h * Xv s * h⁻¹) * (h * Xc t * h⁻¹) := by rw [conj_mul_conj]
      _ = Xv (-s) * Xc (-t) := by rw [(hh s).1, (hh t).2]
  rw [hleft, htarget]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
