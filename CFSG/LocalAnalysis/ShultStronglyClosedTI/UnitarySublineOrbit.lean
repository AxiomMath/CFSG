module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

theorem card_unitaryCoverFixedField {q : ℕ} (hfixed : Nat.card {x : K // J.conj x = x} = q) :
    Nat.card (unitaryCoverFixedField J) = q := by
  let e : unitaryCoverFixedField J ≃ {x : K // J.conj x = x} :=
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans hfixed

theorem vec_t_ne_zero (t : K) : (![t, 0, 1] : Fin 3 → K) ≠ 0 := by
  intro h
  simpa using congrFun h 2

@[expose] def tPoint (t : K) : ℙ K (Fin 3 → K) := Projectivization.mk K ![t, 0, 1] (vec_t_ne_zero t)

theorem point_eq (a c : K) (hv : (![a, 0, c] : Fin 3 → K) ≠ 0) :
    (c = 0 ∧ Projectivization.mk K ![a, 0, c] hv = unitaryCoordinatePoint (K := K) 0) ∨
      (c ≠ 0 ∧ Projectivization.mk K ![a, 0, c] hv = tPoint (a / c)) := by
  by_cases hc : c = 0
  · left
    refine ⟨hc, ?_⟩
    have ha : a ≠ 0 := by
      rintro rfl
      exact hv (by subst hc; ext i; fin_cases i <;> rfl)
    rw [unitaryCoordinatePoint, Projectivization.mk_eq_mk_iff']
    refine ⟨a, ?_⟩
    ext i
    fin_cases i <;> simp [hc]
  · right
    refine ⟨hc, ?_⟩
    rw [tPoint, Projectivization.mk_eq_mk_iff']
    refine ⟨c, ?_⟩
    ext i
    fin_cases i <;> simp
    field_simp

theorem tPoint_ne_point (t : K) : tPoint t ≠ unitaryCoordinatePoint (K := K) 0 := by
  rw [tPoint, unitaryCoordinatePoint, Ne, Projectivization.mk_eq_mk_iff']
  rintro ⟨a, ha⟩
  simpa using congrFun ha 2

theorem tPoint_injective : Function.Injective (tPoint : K → ℙ K (Fin 3 → K)) := by
  intro s t h
  rw [tPoint, tPoint, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h2 := congrFun ha 2
  have h0 := congrFun ha 0
  simp at h2 h0
  rw [h2, one_mul] at h0
  exact h0.symm

variable [CharP K 2]

theorem sublineL_injective (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    Function.Injective ((QuotientGroup.mk' C).comp (sublineHom J hJ)) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  have hmem : sublineHom J hJ m ∈ C := (QuotientGroup.eq_one_iff _).mp hm
  obtain ⟨u, hu, -, -⟩ := hC hmem
  rw [coe_sublineHom] at hu
  have e11 := congrFun (congrFun hu 1) 1
  simp [scalar_apply] at e11
  have hone : sublineHom J hJ m = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_sublineHom, hu, ← e11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact sublineHom_injective hJ (hone.trans (map_one _).symm)

@[expose] def sublineEquiv (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) ≃* sublineL J C hJ :=
  MonoidHom.ofInjective (sublineL_injective hJ hC)

theorem sublineL_eq_sup (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    sublineL J C hJ = upperRootL J C hJ ⊔ lowerRootL J C hJ := by
  refine le_antisymm ?_ (sup_le (upperRootL_le_sublineL hJ) (lowerRootL_le_sublineL hJ))
  rintro _ ⟨m, rfl⟩
  set φ := (QuotientGroup.mk' C).comp (sublineHom J hJ)
  have hle : (Subgroup.closure (CFSG.LinearGroups.elementarySet 2 (unitaryCoverFixedField J))).map
      φ ≤ upperRootL J C hJ ⊔ lowerRootL J C hJ := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨A, ⟨i, j, hij, c, rfl⟩, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact le_sup_left (a := upperRootL J C hJ) ⟨Multiplicative.ofAdd c, rfl⟩
    · exact le_sup_right (a := upperRootL J C hJ) ⟨Multiplicative.ofAdd c, rfl⟩
    · exact absurd rfl hij
  apply hle
  refine ⟨m, ?_, rfl⟩
  rw [CFSG.LinearGroups.special_linear_elementary_generation]
  exact Subgroup.mem_top m

theorem card_upperRootL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    Nat.card (upperRootL J C hJ) = Nat.card (unitaryCoverFixedField J) := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' C).comp
        ((sublineHom J hJ).comp (upperSL (unitaryCoverFixedField J)))) := by
    intro s t hst
    have h1 := sublineL_injective hJ hC hst
    have h2 := congrArg (fun x : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) =>
      (x : Matrix (Fin 2) (Fin 2) (unitaryCoverFixedField J)) 0 1) h1
    simp only [coe_upperSL] at h2
    simpa using h2
  rw [upperRootL, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

variable (J C) in
@[expose] def sublineOrbit (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : Set (ℙ K (Fin 3 → K)) :=
  {P | ∃ x ∈ sublineL J C hJ, coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 0 = P}

theorem sublineHom_smul_point (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) :
    ∃ hv : (![fixedToK J (m 0 0), 0, fixedToK J (m 1 0)] : Fin 3 → K) ≠ 0,
      ProjGenLinGroup.mk ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) •
          unitaryCoordinatePoint (K := K) 0 =
        Projectivization.mk K ![fixedToK J (m 0 0), 0, fixedToK J (m 1 0)] hv := by
  have hv : (![fixedToK J (m 0 0), 0, fixedToK J (m 1 0)] : Fin 3 → K) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    simp only [Matrix.cons_val_zero, Pi.zero_apply, map_eq_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at h0 h2
    have hdet := m.2
    rw [det_fin_two, h0, h2] at hdet
    simp at hdet
  refine ⟨hv, ?_⟩
  rw [unitaryCoordinatePoint, Projectivization.PGL.mk_smul_mk]
  congr 1
  change (((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
    (Pi.single 0 1 : Fin 3 → K) = _
  rw [mulVec_single_one, coe_sublineHom]
  ext i
  fin_cases i <;> rfl

theorem card_sublineOrbit [Finite K] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    Nat.card (sublineOrbit J C hJ hC) = Nat.card (unitaryCoverFixedField J) + 1 := by
  have hmem : ∀ t : unitaryCoverFixedField J, tPoint (fixedToK J t) ∈ sublineOrbit J C hJ hC := by
    intro t
    let m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) :=
      ⟨!![t, -1; 1, 0], by simp [det_fin_two]⟩
    refine ⟨_, ⟨m, rfl⟩, ?_⟩
    obtain ⟨hv, hm⟩ := sublineHom_smul_point hJ m
    change ProjGenLinGroup.mk ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) •
      unitaryCoordinatePoint (K := K) 0 = _
    rw [hm]
    rcases point_eq _ _ hv with ⟨h0, -⟩ | ⟨-, h⟩
    · simp [m] at h0
    · rw [h]
      simp [m]
  have hbase : unitaryCoordinatePoint (K := K) 0 ∈ sublineOrbit J C hJ hC :=
    ⟨1, Subgroup.one_mem _, by rw [map_one, one_smul]⟩
  let F : Option (unitaryCoverFixedField J) → sublineOrbit J C hJ hC := fun o =>
    match o with
    | none => ⟨_, hbase⟩
    | some t => ⟨_, hmem t⟩
  have hF : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro (_ | s) (_ | t) h
      · rfl
      · exact absurd (congrArg Subtype.val h).symm (tPoint_ne_point _)
      · exact absurd (congrArg Subtype.val h) (tPoint_ne_point _)
      · exact congrArg some ((fixedToK J).injective (tPoint_injective (congrArg Subtype.val h)))
    · rintro ⟨P, x, ⟨m, rfl⟩, rfl⟩
      obtain ⟨hv, hm⟩ := sublineHom_smul_point hJ m
      rcases point_eq _ _ hv with ⟨-, h⟩ | ⟨hc, h⟩
      · refine ⟨none, Subtype.ext ?_⟩
        change unitaryCoordinatePoint (K := K) 0 = ProjGenLinGroup.mk
          ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) • unitaryCoordinatePoint 0
        rw [hm, h]
      · have hc' : m 1 0 ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
        refine ⟨some (m 0 0 / m 1 0), Subtype.ext ?_⟩
        change tPoint (fixedToK J (m 0 0 / m 1 0)) = ProjGenLinGroup.mk
          ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) • unitaryCoordinatePoint 0
        rw [hm, h, map_div₀]
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Finite.card_option]

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
