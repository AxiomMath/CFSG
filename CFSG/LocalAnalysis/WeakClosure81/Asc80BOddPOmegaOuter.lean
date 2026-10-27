module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmega
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaCore
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddInner
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration
  CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

private theorem not_map_conjNormal_le_inner {G : Type} [Group G] {L E : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (hEL : ¬ E ≤ L) :
    ¬ E.map (MulAut.conjNormal : G →* MulAut ↥L) ≤
      (MulAut.conj : ↥L →* MulAut ↥L).range := by
  intro hle
  apply hEL
  intro e he
  obtain ⟨l, hl⟩ := hle ⟨e, he, rfl⟩
  have hcen : (l : G)⁻¹ * e ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : G)) hl
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc x * ((l : G)⁻¹ * e) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * e := by group
      _ = (l : G)⁻¹ * (e * x * e⁻¹) * e := by rw [h1]
      _ = (l : G)⁻¹ * e * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
  rw [← hcen]
  exact l.2

private theorem mulAut_congr_inv_apply {P : Type} [Group P] (β : MulAut P) (e : MulAut P) :
    MulAut.congr β⁻¹ e = β⁻¹ * e * β := by
  rfl

private theorem mulAut_mul_conj_mul_inv {P : Type} [Group P] (β : MulAut P) (g : P) :
    β * MulAut.conj g * β⁻¹ = MulAut.conj (β g) := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_conj_mem_pointFamilyAut_plus_four {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hE : IsPGroup 2 E) :
    ∃ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      ∀ e ∈ E, β⁻¹ * e * β ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) with hA
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hF
  have hcard := (plus_four_conjugacy (K := K)).2
  have hodd : ¬ 2 ∣ Nat.card (MulAction.orbit A F) := by
    rcases hcard with h | h <;> rw [h] <;> decide
  obtain ⟨⟨x, β, rfl⟩, hx⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card _ hodd
  refine ⟨β, fun e he => ?_⟩
  have h1 := congrArg Subtype.val (hx ⟨e, he⟩)
  change e • β • F = β • F at h1
  rw [mem_projectivePointFamilyAut_iff]
  change (β⁻¹ * e * β) • F = F
  rw [mul_smul, mul_smul, h1, inv_smul_smul]

theorem seitzFourOuter_orthogonal_of_aniso (hR : SeitzFourOOuterAniso) :
    SeitzFourOuter fun X _ => IsOddOrthogonal X := by
  intro G _ _ L E hLn hLs hnab hfam hC hE h4 hEL
  classical
  have : L.Normal := hLn
  apply iSup_centralizer_eq_of_seitzHyperGamma hC h4
  obtain ⟨n, p, f, hp2, hm⟩ := hfam
  rcases hm with hm | hm | hm
  ·
    have hn0 : n ≠ 0 := by have := hm.1.2.2.1; omega
    have hmod : StatedClassicalModel ↥L .POmegaOdd n p f :=
      hm.statedClassicalModel_of_ne_zero hn0
    have hmod' := hmod
    obtain ⟨⟨hp, hf, hn, hp2'⟩, K, _, _, hK, ⟨eS⟩⟩ := hmod
    obtain ⟨hchar, hnd, hS3, hEQ, hAP, -⟩ :=
      coordinate_model_witness_odd hmod' K hK eS
    have hKchar : ringChar K ≠ 2 := by rw [hchar]; exact hp2'
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hKchar
    set Q : QuadraticForm K (Fin (2 * n + 1) → K) := coordinateQuadOdd n K with hQ
    set e := coordinateOddWitnessEquiv K eS with he
    set E' : Subgroup (MulAut ↥L) := E.map (MulAut.conjNormal : G →* MulAut ↥L) with hE'
    have hE' : IsElemAbelian 2 E' := hE.map _
    have h4' : Nat.card E' = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective
        (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC), h4]
      norm_num
    set E'' : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
      E'.map (MulAut.congr e).toMonoidHom with hE''
    have hE'' : IsElemAbelian 2 E'' := hE'.map _
    have h4'' : Nat.card E'' = 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, h4']
      norm_num
    rw [(planeGen_iff_seitzHyperGamma Nat.prime_two h4').symm, ← planeGen_map_congr e E']
    change PlaneGen E''
    have htop := (orthogonal_geometry_tail_model_point_family_invariant
        ↥L .POmegaOdd (Or.inl rfl) n p f hmod') K hK
    have himage : E'' ≤ matrixProjectiveImage Q := fun x _ =>
      mem_image_of_familyAut_eq_top htop.2
        (coordinate_odd_family_eq_matrixImage hmod' K hK eS) x
    have hout : ¬ E'' ≤
        (MulAut.conj : matrixProjectiveDerived Q →*
          MulAut (matrixProjectiveDerived Q)).range := by
      intro hle
      refine not_map_conjNormal_le_inner hC hEL (fun a ha => ?_)
      obtain ⟨y, hy⟩ := hle ⟨a, ha, rfl⟩
      refine ⟨e.symm y, ?_⟩
      have hy' : MulAut.conj (e.symm y) = MulAut.congr e.symm (MulAut.conj y) := by
        ext z
        simp [MulAut.conj_apply, MulAut.congr_apply]
      rw [hy', hy]
      ext z
      simp [MulAut.congr_apply]
    exact planeGen_outer_of_mem_image hR h2 (by omega) hnd hS3 hEQ hAP hE'' h4'' himage hout
  ·
    have hn0 : n ≠ 0 := by have := hm.1.2.2; omega
    have hmod : StatedClassicalModel ↥L .POmegaPlus n p f :=
      hm.statedClassicalModel_of_ne_zero hn0
    have hmod' := hmod
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨eS⟩⟩ := hmod
    obtain ⟨hchar, hnd, hS3, hEQ, hAP, -⟩ :=
      coordinate_model_witness_plus hmod' K hK eS
    have hp2' : p ≠ 2 := by omega
    have hKchar : ringChar K ≠ 2 := by rw [hchar]; exact hp2'
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hKchar
    set Q : QuadraticForm K (Fin (2 * n) → K) := coordinateQuadPlus n K with hQ
    set e := coordinatePlusWitnessEquiv K eS with he
    set E' : Subgroup (MulAut ↥L) := E.map (MulAut.conjNormal : G →* MulAut ↥L) with hE'
    have hE' : IsElemAbelian 2 E' := hE.map _
    have h4' : Nat.card E' = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective
        (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC), h4]
      norm_num
    set E'' : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
      E'.map (MulAut.congr e).toMonoidHom with hE''
    have hE'' : IsElemAbelian 2 E'' := hE'.map _
    have h4'' : Nat.card E'' = 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, h4']
      norm_num
    rw [(planeGen_iff_seitzHyperGamma Nat.prime_two h4').symm, ← planeGen_map_congr e E']
    change PlaneGen E''
    have hout : ¬ E'' ≤
        (MulAut.conj : matrixProjectiveDerived Q →*
          MulAut (matrixProjectiveDerived Q)).range := by
      intro hle
      refine not_map_conjNormal_le_inner hC hEL (fun a ha => ?_)
      obtain ⟨y, hy⟩ := hle ⟨a, ha, rfl⟩
      refine ⟨e.symm y, ?_⟩
      have hy' : MulAut.conj (e.symm y) = MulAut.congr e.symm (MulAut.conj y) := by
        ext z
        simp [MulAut.conj_apply, MulAut.congr_apply]
      rw [hy', hy]
      ext z
      simp [MulAut.congr_apply]
    rcases Nat.lt_or_ge n 5 with hlt | hge
    · obtain rfl : n = 4 := by omega
      obtain ⟨β₀, hβ₀⟩ :=
        exists_conj_mem_pointFamilyAut_plus_four (K := K) (E := E'') hE''.isPGroup
      let β : MulAut (matrixProjectiveDerived Q) := β₀
      have hβ : ∀ e ∈ E'', β⁻¹ * e * β ∈ projectivePointFamilyAut Q := by
        intro e he
        simpa [β, hQ] using hβ₀ e he
      have hfamImg := coordinate_plus_family_eq_matrixImage hmod' K hK eS
      set E''' : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
        E''.map (MulAut.congr β⁻¹).toMonoidHom with hE'''
      have hE''' : IsElemAbelian 2 E''' := hE''.map _
      have h4''' : Nat.card E''' = 4 := by
        rw [Subgroup.card_map_of_injective (MulAut.congr β⁻¹).injective, h4'']
      have himage' : E''' ≤ matrixProjectiveImage Q := by
        intro x hx
        rw [← hfamImg]
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        change MulAut.congr β⁻¹ y ∈ projectivePointFamilyAut Q
        rw [mulAut_congr_inv_apply]
        exact hβ y hy
      have hout' : ¬ E''' ≤
          (MulAut.conj : matrixProjectiveDerived Q →*
            MulAut (matrixProjectiveDerived Q)).range := by
        intro hle
        apply hout
        intro y hy
        have hmem : MulAut.congr β⁻¹ y ∈
            (MulAut.conj : matrixProjectiveDerived Q →*
              MulAut (matrixProjectiveDerived Q)).range :=
          hle (Subgroup.mem_map_of_mem (MulAut.congr β⁻¹).toMonoidHom hy)
        rw [mulAut_congr_inv_apply] at hmem
        obtain ⟨g, hg⟩ := hmem
        refine ⟨β g, ?_⟩
        calc MulAut.conj (β g) = β * MulAut.conj g * β⁻¹ :=
              (mulAut_mul_conj_mul_inv β g).symm
          _ = β * (β⁻¹ * y * β) * β⁻¹ := by rw [← hg]
          _ = y := by group
      have hPG''' := planeGen_outer_of_mem_image hR h2 (by omega) hnd hS3 hEQ hAP
        hE''' h4''' himage' hout'
      exact (planeGen_map_congr β⁻¹ E'').mp hPG'''
    · have himage : E'' ≤ matrixProjectiveImage Q := fun x _ =>
        mem_image_of_familyAut_eq_top
          (coordinate_plus_pointFamilyAut_eq_top hge)
          (coordinate_plus_family_eq_matrixImage hmod' K hK eS) x
      exact planeGen_outer_of_mem_image hR h2 (by omega) hnd hS3 hEQ hAP hE'' h4'' himage hout
  ·
    have hn0 : n ≠ 0 := by have := hm.1.2.2; omega
    have hmod : StatedClassicalModel ↥L .POmegaMinus n p f :=
      hm.statedClassicalModel_of_ne_zero hn0
    have hmod' := hmod
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨eS⟩⟩ := hmod
    have hn1 : 1 ≤ n := by omega
    obtain ⟨hchar, hnd, hS3, hEQ, hAP, -⟩ :=
      coordinate_model_witness_minus hmod' K hK b c hirr eS
    have hp2' : p ≠ 2 := by omega
    have hKchar : ringChar K ≠ 2 := by rw [hchar]; exact hp2'
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hKchar
    set Q : QuadraticForm K (Fin (2 * n) → K) := coordinateQuadMinus n K hn1 b c with hQ
    set e := coordinateMinusWitnessEquiv K hn1 b c eS with he
    set E' : Subgroup (MulAut ↥L) := E.map (MulAut.conjNormal : G →* MulAut ↥L) with hE'
    have hE' : IsElemAbelian 2 E' := hE.map _
    have h4' : Nat.card E' = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective
        (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC), h4]
      norm_num
    set E'' : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
      E'.map (MulAut.congr e).toMonoidHom with hE''
    have hE'' : IsElemAbelian 2 E'' := hE'.map _
    have h4'' : Nat.card E'' = 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, h4']
      norm_num
    rw [(planeGen_iff_seitzHyperGamma Nat.prime_two h4').symm, ← planeGen_map_congr e E']
    change PlaneGen E''
    have htop := (orthogonal_geometry_tail_model_point_family_invariant
        ↥L .POmegaMinus (Or.inr rfl) n p f hmod') hn1 K hK b c hirr
    have himage : E'' ≤ matrixProjectiveImage Q := fun x _ =>
      mem_image_of_familyAut_eq_top htop.2
        (coordinate_minus_family_eq_matrixImage hmod' hn1 K hK b c hirr eS) x
    have hout : ¬ E'' ≤
        (MulAut.conj : matrixProjectiveDerived Q →*
          MulAut (matrixProjectiveDerived Q)).range := by
      intro hle
      refine not_map_conjNormal_le_inner hC hEL (fun a ha => ?_)
      obtain ⟨y, hy⟩ := hle ⟨a, ha, rfl⟩
      refine ⟨e.symm y, ?_⟩
      have hy' : MulAut.conj (e.symm y) = MulAut.congr e.symm (MulAut.conj y) := by
        ext z
        simp [MulAut.conj_apply, MulAut.congr_apply]
      rw [hy', hy]
      ext z
      simp [MulAut.congr_apply]
    exact planeGen_outer_of_mem_image hR h2 (by omega) hnd hS3 hEQ hAP hE'' h4'' himage hout

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
