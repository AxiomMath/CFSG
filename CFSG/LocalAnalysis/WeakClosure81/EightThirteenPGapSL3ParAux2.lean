module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSL3ParAux1
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open CFSG.Quasithin.H13.KGL34P
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)
open Matrix

variable {F : Type} [Field F]

private abbrev wcgapsp_P0 : Subgroup (SpecialLinearGroup (Fin 3) F) := stabilizer (flagSpace 3 F 1)

private abbrev wcgapsp_P1 : Subgroup (SpecialLinearGroup (Fin 3) F) := stabilizer (flagSpace 3 F 2)

private abbrev wcgapsp_B : Subgroup (SpecialLinearGroup (Fin 3) F) := upperTriangular 3 F

private abbrev wcgapsp_U : Subgroup (SpecialLinearGroup (Fin 3) F) := unitriangular 3 F

private theorem wcgapsp_mem_P1_iff {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ wcgapsp_P1 (F := F) ↔ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  rw [wcgapsp_P1, mem_stabilizer]
  constructor
  · intro h
    have he0 : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
      rw [mem_flagSpace]
      intro j hj
      fin_cases j <;> simp at hj ⊢
    have he1 : (Pi.single 1 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
      rw [mem_flagSpace]
      intro j hj
      fin_cases j <;> simp at hj ⊢
    have h0 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) ∈
        flagSpace 3 F 2 := by
      rw [← h]
      exact ⟨_, he0, rfl⟩
    have h1 : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F) ∈
        flagSpace 3 F 2 := by
      rw [← h]
      exact ⟨_, he1, rfl⟩
    rw [mem_flagSpace] at h0 h1
    refine ⟨?_, ?_⟩
    · have := h0 2 (by decide)
      simpa [mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
    · have := h1 2 (by decide)
      simpa [mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
  · rintro ⟨h1, h2⟩
    have hle : (flagSpace 3 F 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) ≤
        flagSpace 3 F 2 := by
      rintro _ ⟨v, hv, rfl⟩
      have hv2 := (mem_flagSpace.mp hv) 2 (by decide)
      rw [mem_flagSpace]
      intro j hj
      fin_cases j
      · simp at hj
      · simp at hj
      · simp [mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_three, h1, h2, hv2]
    have hinj : Function.Injective (mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) := by
      have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) F) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.2]; exact isUnit_one)
      exact Matrix.mulVec_injective_iff_isUnit.mpr hu
    exact Submodule.eq_of_le_of_finrank_eq hle
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm

private def wcgapsp_tl (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

private theorem wcgapsp_det_eq_mul_det_tl {g : Matrix (Fin 3) (Fin 3) F}
    (hg1 : g 2 0 = 0) (hg2 : g 2 1 = 0) :
    g.det = g 2 2 * (wcgapsp_tl g).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two, hg1, hg2]
  simp only [wcgapsp_tl, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  ring

private theorem wcgapsp_char0_ne_zero (g : ↥(wcgapsp_P0 (F := F))) :
    ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
  obtain ⟨h1, h2⟩ := mem_stabilizer_flagSpace_one.mp g.2
  intro h0
  have hdet := det_eq_mul_det_blk (k := F) h1 h2
  rw [h0, zero_mul] at hdet
  have h1det : ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    (g : SpecialLinearGroup (Fin 3) F).2
  rw [h1det] at hdet
  exact one_ne_zero hdet

private noncomputable def wcgapsp_char0 :
    ↥(wcgapsp_P0 (F := F)) →* Fˣ where
  toFun g := Units.mk0 (((g : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) 0 0) (wcgapsp_char0_ne_zero g)
  map_one' := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    simp
  map_mul' := by
    intro g h
    apply Units.ext
    have hh1 : ((h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 :=
      (mem_stabilizer_flagSpace_one.mp h.2).1
    have hh2 : ((h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 :=
      (mem_stabilizer_flagSpace_one.mp h.2).2
    show (((g * h : ↥(wcgapsp_P0 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 =
      (((g : ↥(wcgapsp_P0 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 *
      (((h : ↥(wcgapsp_P0 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0
    rw [show (((g * h : ↥(wcgapsp_P0 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
        (((g : ↥(wcgapsp_P0 (F := F))) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *
        (((h : ↥(wcgapsp_P0 (F := F))) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) from rfl]
    rw [Matrix.mul_apply, Fin.sum_univ_three, hh1, hh2, mul_zero, mul_zero, add_zero, add_zero]

private theorem wcgapsp_char1_ne_zero (g : ↥(wcgapsp_P1 (F := F))) :
    ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  obtain ⟨h1, h2⟩ := wcgapsp_mem_P1_iff.mp g.2
  intro h0
  have hdet := wcgapsp_det_eq_mul_det_tl (F := F) h1 h2
  rw [h0, zero_mul] at hdet
  have h1det : ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    (g : SpecialLinearGroup (Fin 3) F).2
  rw [h1det] at hdet
  exact one_ne_zero hdet

private noncomputable def wcgapsp_char1 :
    ↥(wcgapsp_P1 (F := F)) →* Fˣ where
  toFun g := Units.mk0 (((g : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) 2 2) (wcgapsp_char1_ne_zero g)
  map_one' := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    simp
  map_mul' := by
    intro g h
    apply Units.ext
    have hg1 : ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 :=
      (wcgapsp_mem_P1_iff.mp g.2).1
    have hg2 : ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
      (wcgapsp_mem_P1_iff.mp g.2).2
    show (((g * h : ↥(wcgapsp_P1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 2 2 =
      (((g : ↥(wcgapsp_P1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 2 2 *
      (((h : ↥(wcgapsp_P1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 2 2
    rw [show (((g * h : ↥(wcgapsp_P1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
        (((g : ↥(wcgapsp_P1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *
        (((h : ↥(wcgapsp_P1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) from rfl]
    rw [Matrix.mul_apply, Fin.sum_univ_three, hg1, hg2, zero_mul, zero_mul, zero_add, zero_add]

private noncomputable abbrev wcgapsp_K0 : Subgroup (SpecialLinearGroup (Fin 3) F) :=
  (wcgapsp_char0 (F := F)).ker.map (wcgapsp_P0 (F := F)).subtype

private noncomputable abbrev wcgapsp_K1 : Subgroup (SpecialLinearGroup (Fin 3) F) :=
  (wcgapsp_char1 (F := F)).ker.map (wcgapsp_P1 (F := F)).subtype

private theorem wcgapsp_mem_K0 {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ wcgapsp_K0 (F := F) ↔ g ∈ wcgapsp_P0 (F := F) ∧
      (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
  rw [wcgapsp_K0, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    refine ⟨hxg ▸ x.2, ?_⟩
    have hx1 : wcgapsp_char0 (F := F) x = 1 := by
      simpa [MonoidHom.mem_ker] using hx
    have hval : ((wcgapsp_char0 (F := F) x : Fˣ) : F) = 1 := by rw [hx1]; rfl
    rw [← hxg]
    simpa [wcgapsp_char0] using hval
  · rintro ⟨hgP, hg00⟩
    refine ⟨⟨g, hgP⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    change ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1
    exact hg00

private theorem wcgapsp_mem_K1 {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ wcgapsp_K1 (F := F) ↔ g ∈ wcgapsp_P1 (F := F) ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  rw [wcgapsp_K1, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    refine ⟨hxg ▸ x.2, ?_⟩
    have hx1 : wcgapsp_char1 (F := F) x = 1 := by
      simpa [MonoidHom.mem_ker] using hx
    have hval : ((wcgapsp_char1 (F := F) x : Fˣ) : F) = 1 := by rw [hx1]; rfl
    rw [← hxg]
    simpa [wcgapsp_char1] using hval
  · rintro ⟨hgP, hg22⟩
    refine ⟨⟨g, hgP⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    change ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1
    exact hg22

private theorem wcgapsp_K0_le_P0 : wcgapsp_K0 (F := F) ≤ wcgapsp_P0 (F := F) :=
  fun _ hg => (wcgapsp_mem_K0.mp hg).1

private theorem wcgapsp_K1_le_P1 : wcgapsp_K1 (F := F) ≤ wcgapsp_P1 (F := F) :=
  fun _ hg => (wcgapsp_mem_K1.mp hg).1

private theorem wcgapsp_U_le_K0 : wcgapsp_U (F := F) ≤ wcgapsp_K0 (F := F) := by
  intro u hu
  rw [wcgapsp_mem_K0]
  obtain ⟨hlo, hdiag⟩ := mem_unitriangular.mp hu
  exact ⟨mem_stabilizer_flagSpace_one.mpr ⟨hlo 1 0 (by decide), hlo 2 0 (by decide)⟩,
    hdiag 0⟩

private theorem wcgapsp_U_le_K1 : wcgapsp_U (F := F) ≤ wcgapsp_K1 (F := F) := by
  intro u hu
  rw [wcgapsp_mem_K1]
  obtain ⟨hlo, hdiag⟩ := mem_unitriangular.mp hu
  exact ⟨wcgapsp_mem_P1_iff.mpr ⟨hlo 2 0 (by decide), hlo 2 1 (by decide)⟩, hdiag 2⟩

private theorem wcgapsp_B_le_P0 : wcgapsp_B (F := F) ≤ wcgapsp_P0 (F := F) :=
  upperTriangular_le_stabilizer_flagSpace 1

private theorem wcgapsp_B_le_P1 : wcgapsp_B (F := F) ≤ wcgapsp_P1 (F := F) :=
  upperTriangular_le_stabilizer_flagSpace 2

private theorem wcgapsp_K0_subgroupOf :
    (wcgapsp_K0 (F := F)).subgroupOf (wcgapsp_P0 (F := F)) =
      (wcgapsp_char0 (F := F)).ker := by
  ext x
  show (x : SpecialLinearGroup (Fin 3) F) ∈ wcgapsp_K0 (F := F) ↔
    x ∈ (wcgapsp_char0 (F := F)).ker
  rw [wcgapsp_K0, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem wcgapsp_K1_subgroupOf :
    (wcgapsp_K1 (F := F)).subgroupOf (wcgapsp_P1 (F := F)) =
      (wcgapsp_char1 (F := F)).ker := by
  ext x
  show (x : SpecialLinearGroup (Fin 3) F) ∈ wcgapsp_K1 (F := F) ↔
    x ∈ (wcgapsp_char1 (F := F)).ker
  rw [wcgapsp_K1, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem wcgapsp_char0_surjective (hF : Nat.card F = 4) :
    Function.Surjective (wcgapsp_char0 (F := F)) := by
  intro u
  have hc : u ^ 3 = 1 := by
    simpa [Nat.card_units, hF] using pow_card_eq_one' (x := u)
  refine ⟨⟨scalarElement u hc, scalars_le_stabilizer (flagSpace 3 F 1)
    (scalarElement_mem_scalars u hc)⟩, ?_⟩
  apply Units.ext
  change ((scalarElement u hc : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) 0 0 = (u : F)
  rw [coe_scalarElement]
  simp [scalar_apply]

private theorem wcgapsp_char1_surjective (hF : Nat.card F = 4) :
    Function.Surjective (wcgapsp_char1 (F := F)) := by
  intro u
  have hc : u ^ 3 = 1 := by
    simpa [Nat.card_units, hF] using pow_card_eq_one' (x := u)
  refine ⟨⟨scalarElement u hc, scalars_le_stabilizer (flagSpace 3 F 2)
    (scalarElement_mem_scalars u hc)⟩, ?_⟩
  apply Units.ext
  change ((scalarElement u hc : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) 2 2 = (u : F)
  rw [coe_scalarElement]
  simp [scalar_apply]

private theorem wcgapsp_K0_relIndex (hF : Nat.card F = 4) :
    (wcgapsp_K0 (F := F)).relIndex (wcgapsp_P0 (F := F)) = 3 := by
  change ((wcgapsp_K0 (F := F)).subgroupOf (wcgapsp_P0 (F := F))).index = 3
  rw [wcgapsp_K0_subgroupOf, Subgroup.index_ker]
  rw [(MonoidHom.range_eq_top (f := wcgapsp_char0 (F := F))).mpr
    (wcgapsp_char0_surjective hF), Subgroup.card_top, Nat.card_units, hF]

private theorem wcgapsp_K1_relIndex (hF : Nat.card F = 4) :
    (wcgapsp_K1 (F := F)).relIndex (wcgapsp_P1 (F := F)) = 3 := by
  change ((wcgapsp_K1 (F := F)).subgroupOf (wcgapsp_P1 (F := F))).index = 3
  rw [wcgapsp_K1_subgroupOf, Subgroup.index_ker]
  rw [(MonoidHom.range_eq_top (f := wcgapsp_char1 (F := F))).mpr
    (wcgapsp_char1_surjective hF), Subgroup.card_top, Nat.card_units, hF]

private def wcgapsp_rad1 (b c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, b; 0, 1, c; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private theorem wcgapsp_coe_rad1 (b c : F) :
    ((wcgapsp_rad1 b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, b; 0, 1, c; 0, 0, 1] := rfl

private theorem wcgapsp_rad1_mul (b c b' c' : F) :
    wcgapsp_rad1 b c * wcgapsp_rad1 b' c' = wcgapsp_rad1 (b + b') (c + c') := by
  apply Subtype.ext
  show !![1, 0, b; 0, 1, c; 0, 0, 1] * !![1, 0, b'; 0, 1, c'; 0, 0, 1] =
    !![1, 0, b + b'; 0, 1, c + c'; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem wcgapsp_rad1_zero : wcgapsp_rad1 (0 : F) 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wcgapsp_rad1]

private def wcgapsp_radSub1 : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := Set.range (fun bc : F × F => wcgapsp_rad1 bc.1 bc.2)
  one_mem' := ⟨(0, 0), wcgapsp_rad1_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨b, c⟩, rfl⟩ ⟨⟨b', c'⟩, rfl⟩
    exact ⟨(b + b', c + c'), (wcgapsp_rad1_mul b c b' c').symm⟩
  inv_mem' := by
    rintro _ ⟨⟨b, c⟩, rfl⟩
    exact ⟨(-b, -c), eq_inv_of_mul_eq_one_right (by
      rw [wcgapsp_rad1_mul b c (-b) (-c), add_neg_cancel, add_neg_cancel,
        wcgapsp_rad1_zero])⟩

private theorem wcgapsp_mem_radSub1 {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ wcgapsp_radSub1 (F := F) ↔ ∃ b c : F, wcgapsp_rad1 b c = g :=
  ⟨fun ⟨⟨b, c⟩, h⟩ => ⟨b, c, h⟩, fun ⟨b, c, h⟩ => ⟨(b, c), h⟩⟩

private theorem wcgapsp_radSub_le_K0 : radSub (k := F) ≤ wcgapsp_K0 (F := F) := by
  intro r hr
  obtain ⟨b, c, rfl⟩ := mem_radSub.mp hr
  rw [wcgapsp_mem_K0]
  exact ⟨rad_mem_stabilizer b c, by rw [coe_rad]; simp⟩

private theorem wcgapsp_radSub1_le_K1 : wcgapsp_radSub1 (F := F) ≤ wcgapsp_K1 (F := F) := by
  intro r hr
  obtain ⟨b, c, rfl⟩ := wcgapsp_mem_radSub1.mp hr
  rw [wcgapsp_mem_K1]
  refine ⟨wcgapsp_mem_P1_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [wcgapsp_coe_rad1]; simp
  · rw [wcgapsp_coe_rad1]; simp
  · rw [wcgapsp_coe_rad1]; simp

private theorem wcgapsp_card_radSub (hF : Nat.card F = 4) : Nat.card (radSub (k := F)) = 16 := by
  have : Finite F := finite_of_card_eq_four hF
  have hinj : Function.Injective (fun bc : F × F => rad bc.1 bc.2) := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ h
    have h01 := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
      ((g : Matrix (Fin 3) (Fin 3) F)) 0 1) h
    have h02 := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
      ((g : Matrix (Fin 3) (Fin 3) F)) 0 2) h
    simp [coe_rad] at h01 h02
    exact Prod.ext h01 h02
  have he : ((radSub (k := F) : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) =
      Set.range (fun bc : F × F => rad bc.1 bc.2) := rfl
  rw [← SetLike.coe_sort_coe, he, Nat.card_range_of_injective hinj, Nat.card_prod, hF]

private theorem wcgapsp_card_radSub1 (hF : Nat.card F = 4) :
    Nat.card (wcgapsp_radSub1 (F := F)) = 16 := by
  have : Finite F := finite_of_card_eq_four hF
  have hinj : Function.Injective (fun bc : F × F => wcgapsp_rad1 bc.1 bc.2) := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ h
    have h02 := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
      ((g : Matrix (Fin 3) (Fin 3) F)) 0 2) h
    have h12 := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
      ((g : Matrix (Fin 3) (Fin 3) F)) 1 2) h
    simp [wcgapsp_coe_rad1] at h02 h12
    exact Prod.ext h02 h12
  have he : ((wcgapsp_radSub1 (F := F) : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) =
      Set.range (fun bc : F × F => wcgapsp_rad1 bc.1 bc.2) := rfl
  rw [← SetLike.coe_sort_coe, he, Nat.card_range_of_injective hinj, Nat.card_prod, hF]

private theorem wcgapsp_isPGroup_radSub (hF : Nat.card F = 4) :
    IsPGroup 2 (radSub (k := F)) :=
  IsPGroup.of_card (p := 2) (n := 4) (by rw [wcgapsp_card_radSub hF]; norm_num)

private theorem wcgapsp_isPGroup_radSub1 (hF : Nat.card F = 4) :
    IsPGroup 2 (wcgapsp_radSub1 (F := F)) :=
  IsPGroup.of_card (p := 2) (n := 4) (by rw [wcgapsp_card_radSub1 hF]; norm_num)


private noncomputable def wcgapsp_leviK0 (hF : Nat.card F = 4) :
    ↥(wcgapsp_K0 (F := F)) →* SpecialLinearGroup (Fin 2) F :=
  (levi hF).comp (Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)))

private theorem wcgapsp_leviK0_surjective (hF : Nat.card F = 4) :
    Function.Surjective (wcgapsp_leviK0 hF) := by
  intro B
  have hmem : emb B ∈ wcgapsp_K0 (F := F) := by
    rw [wcgapsp_mem_K0]
    exact ⟨emb_mem_stabilizer B, by rw [coe_emb]; simp⟩
  refine ⟨⟨emb B, hmem⟩, ?_⟩
  show levi hF (Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)) ⟨emb B, hmem⟩) = B
  rw [show Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)) ⟨emb B, hmem⟩ =
      (⟨emb B, emb_mem_stabilizer B⟩ : ↥(wcgapsp_P0 (F := F))) from rfl]
  exact levi_emb hF B

private theorem wcgapsp_leviK0_ker (hF : Nat.card F = 4) :
    (wcgapsp_leviK0 hF).ker = (radSub (k := F)).subgroupOf (wcgapsp_K0 (F := F)) := by
  ext x
  show (wcgapsp_leviK0 hF x = 1) ↔ (x : SpecialLinearGroup (Fin 3) F) ∈ radSub (k := F)
  constructor
  · intro hx
    have hx00 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 :=
      (wcgapsp_mem_K0.mp x.2).2
    have hle : levi hF (Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)) x) = 1 := hx
    obtain ⟨μ, hμ, b, c, hg⟩ := exists_rad_of_levi_eq_one hF hle
    have hg' : (x : SpecialLinearGroup (Fin 3) F) =
        (μ : SpecialLinearGroup (Fin 3) F) * rad b c := by
      simpa using hg
    obtain ⟨d, -, hd⟩ := mem_scalars.mp hμ
    have hprod00 : (((μ : SpecialLinearGroup (Fin 3) F) * rad b c :
        SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = d := by
      rw [show (((μ : SpecialLinearGroup (Fin 3) F) * rad b c :
          SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (((μ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((rad b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) from rfl]
      rw [hd, Matrix.mul_apply, Fin.sum_univ_three]
      simp [scalar_apply, coe_rad]
    have hd1 : d = 1 := by
      have h1 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = d := by
        rw [hg', hprod00]
      rw [hx00] at h1
      exact Units.ext h1.symm
    have hμ1 : μ = 1 := by
      apply Subtype.ext
      rw [hd, hd1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    rw [hg', hμ1, one_mul]
    exact mem_radSub.mpr ⟨b, c, rfl⟩
  · intro hx
    obtain ⟨b, c, hbc⟩ := mem_radSub.mp hx
    show levi hF (Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)) x) = 1
    have hx' : Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)) x =
        (⟨rad b c, rad_mem_stabilizer b c⟩ : ↥(wcgapsp_P0 (F := F))) :=
      Subtype.ext hbc.symm
    rw [hx']
    exact levi_rad hF b c

private noncomputable def wcgapsp_leviK1 :
    ↥(wcgapsp_K1 (F := F)) →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨wcgapsp_tl ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), by
    have hgP1 := (wcgapsp_mem_K1.mp g.2).1
    have hg22 := (wcgapsp_mem_K1.mp g.2).2
    have hg1 := (wcgapsp_mem_P1_iff.mp hgP1).1
    have hg2 := (wcgapsp_mem_P1_iff.mp hgP1).2
    have hdet := wcgapsp_det_eq_mul_det_tl (F := F) hg1 hg2
    rw [hg22, one_mul] at hdet
    have hgdet : (((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det = 1 :=
      (g : SpecialLinearGroup (Fin 3) F).2
    rw [hgdet] at hdet
    exact hdet.symm⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wcgapsp_tl]
  map_mul' := by
    intro g h
    apply Subtype.ext
    have hhP1 := (wcgapsp_mem_K1.mp h.2).1
    have hh1 := (wcgapsp_mem_P1_iff.mp hhP1).1
    have hh2 := (wcgapsp_mem_P1_iff.mp hhP1).2
    show wcgapsp_tl (((g * h : ↥(wcgapsp_K1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      wcgapsp_tl (((g : ↥(wcgapsp_K1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *
      wcgapsp_tl (((h : ↥(wcgapsp_K1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)
    rw [show (((g * h : ↥(wcgapsp_K1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
        (((g : ↥(wcgapsp_K1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *
        (((h : ↥(wcgapsp_K1 (F := F))) : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) from rfl]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wcgapsp_tl, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hh1, hh2]

private def wcgapsp_emb1 (B : SpecialLinearGroup (Fin 2) F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![(B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
      (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1, 0;
      0, 0, 1], by
    have hB := B.2
    rw [Matrix.det_fin_two] at hB
    rw [Matrix.det_fin_three]
    simp
    linear_combination hB⟩

private theorem wcgapsp_coe_emb1 (B : SpecialLinearGroup (Fin 2) F) :
    ((wcgapsp_emb1 B : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
        (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1, 0;
        0, 0, 1] := rfl

private theorem wcgapsp_emb1_mem_K1 (B : SpecialLinearGroup (Fin 2) F) :
    wcgapsp_emb1 B ∈ wcgapsp_K1 (F := F) := by
  rw [wcgapsp_mem_K1]
  refine ⟨wcgapsp_mem_P1_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [wcgapsp_coe_emb1]; simp
  · rw [wcgapsp_coe_emb1]; simp
  · rw [wcgapsp_coe_emb1]; simp

private theorem wcgapsp_leviK1_emb1 (B : SpecialLinearGroup (Fin 2) F) :
    wcgapsp_leviK1 (F := F) ⟨wcgapsp_emb1 B, wcgapsp_emb1_mem_K1 B⟩ = B := by
  apply Subtype.ext
  change wcgapsp_tl ((wcgapsp_emb1 B : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = (B : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wcgapsp_tl, wcgapsp_coe_emb1]

private theorem wcgapsp_leviK1_surjective :
    Function.Surjective (wcgapsp_leviK1 (F := F)) :=
  fun B => ⟨⟨wcgapsp_emb1 B, wcgapsp_emb1_mem_K1 B⟩, wcgapsp_leviK1_emb1 B⟩

private theorem wcgapsp_leviK1_ker :
    (wcgapsp_leviK1 (F := F)).ker =
      (wcgapsp_radSub1 (F := F)).subgroupOf (wcgapsp_K1 (F := F)) := by
  ext x
  show (wcgapsp_leviK1 x = 1) ↔ (x : SpecialLinearGroup (Fin 3) F) ∈ wcgapsp_radSub1 (F := F)
  constructor
  · intro hx
    have htl : wcgapsp_tl ((x : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by
      have h := congrArg (fun A : SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F)) hx
      change wcgapsp_tl ((x : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 at h
      exact h
    have h00 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
      have := congrFun (congrFun htl 0) 0; simpa [wcgapsp_tl] using this
    have h01 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
      have := congrFun (congrFun htl 0) 1; simpa [wcgapsp_tl] using this
    have h10 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
      have := congrFun (congrFun htl 1) 0; simpa [wcgapsp_tl] using this
    have h11 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := by
      have := congrFun (congrFun htl 1) 1; simpa [wcgapsp_tl] using this
    have hxP1 := (wcgapsp_mem_K1.mp x.2).1
    have hx22 := (wcgapsp_mem_K1.mp x.2).2
    have h20 := (wcgapsp_mem_P1_iff.mp hxP1).1
    have h21 := (wcgapsp_mem_P1_iff.mp hxP1).2
    refine wcgapsp_mem_radSub1.mpr ⟨((x : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 2, ((x : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 1 2, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wcgapsp_coe_rad1, h00, h01, h10, h11, h20, h21, hx22]
  · intro hx
    obtain ⟨b, c, hbc⟩ := wcgapsp_mem_radSub1.mp hx
    have hxK : x = (⟨wcgapsp_rad1 b c,
        wcgapsp_radSub1_le_K1 (wcgapsp_mem_radSub1.mpr ⟨b, c, rfl⟩)⟩ :
        ↥(wcgapsp_K1 (F := F))) := Subtype.ext hbc.symm
    rw [hxK]
    apply Subtype.ext
    change wcgapsp_tl ((wcgapsp_rad1 b c : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (1 : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wcgapsp_tl, wcgapsp_coe_rad1]

private theorem wcgapsp_oTwoMod_K0 (hF : Nat.card F = 4) :
    oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_K0 (F := F)) =
      radSub (k := F) := by
  haveI : Finite F := finite_of_card_eq_four hF
  apply le_antisymm
  · rw [oTwoMod]
    refine iSup₂_le fun W hW => ?_
    have hW2' : IsPGroup 2 W := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro x
      obtain ⟨k, hk⟩ := hW.2.2.2 (x : SpecialLinearGroup (Fin 3) F) x.2
      exact ⟨k, orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext (Subgroup.mem_bot.mp hk))⟩
    have hW2 : IsPGroup 2 (W.subgroupOf (wcgapsp_K0 (F := F))) :=
      hW2'.of_equiv (Subgroup.subgroupOfEquivOfLe hW.2.1).symm
    have hS2 : IsPGroup 2 ((W.subgroupOf (wcgapsp_K0 (F := F))).map (wcgapsp_leviK0 hF)) :=
      hW2.map (wcgapsp_leviK0 hF)
    have hSn : ((W.subgroupOf (wcgapsp_K0 (F := F))).map (wcgapsp_leviK0 hF)).Normal :=
      hW.2.2.1.map (wcgapsp_leviK0 hF) (wcgapsp_leviK0_surjective hF)
    rcases (isSimpleGroup_sl_two hF).eq_bot_or_eq_top_of_normal
      ((W.subgroupOf (wcgapsp_K0 (F := F))).map (wcgapsp_leviK0 hF)) with h | h
    · intro w hw
      have hle : W.subgroupOf (wcgapsp_K0 (F := F)) ≤ (wcgapsp_leviK0 hF).ker := by
        rw [← Subgroup.map_eq_bot_iff]; exact h
      have hmem : (⟨w, hW.2.1 hw⟩ : ↥(wcgapsp_K0 (F := F))) ∈ (wcgapsp_leviK0 hF).ker :=
        hle hw
      rw [wcgapsp_leviK0_ker hF] at hmem
      exact hmem
    · exfalso
      obtain ⟨n, hn⟩ := hS2.exists_card_dvd_pow
      rw [h, Subgroup.card_top, card_sl_two hF] at hn
      have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h32
  · have hRn : ((radSub (k := F)).subgroupOf (wcgapsp_K0 (F := F))).Normal :=
      (wcgapsp_leviK0_ker hF).symm ▸ MonoidHom.normal_ker _
    exact wcgapsp_le_oTwoMod_of_isPGroup (wcgapsp_radSub_le_K0 (F := F)) hRn
      (wcgapsp_isPGroup_radSub hF)

private theorem wcgapsp_oTwoMod_K1 (hF : Nat.card F = 4) :
    oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_K1 (F := F)) =
      wcgapsp_radSub1 (F := F) := by
  haveI : Finite F := finite_of_card_eq_four hF
  apply le_antisymm
  · rw [oTwoMod]
    refine iSup₂_le fun W hW => ?_
    have hW2' : IsPGroup 2 W := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro x
      obtain ⟨k, hk⟩ := hW.2.2.2 (x : SpecialLinearGroup (Fin 3) F) x.2
      exact ⟨k, orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext (Subgroup.mem_bot.mp hk))⟩
    have hW2 : IsPGroup 2 (W.subgroupOf (wcgapsp_K1 (F := F))) :=
      hW2'.of_equiv (Subgroup.subgroupOfEquivOfLe hW.2.1).symm
    have hS2 : IsPGroup 2 ((W.subgroupOf (wcgapsp_K1 (F := F))).map wcgapsp_leviK1) :=
      hW2.map wcgapsp_leviK1
    have hSn : ((W.subgroupOf (wcgapsp_K1 (F := F))).map wcgapsp_leviK1).Normal :=
      hW.2.2.1.map wcgapsp_leviK1 (wcgapsp_leviK1_surjective)
    rcases (isSimpleGroup_sl_two hF).eq_bot_or_eq_top_of_normal
      ((W.subgroupOf (wcgapsp_K1 (F := F))).map wcgapsp_leviK1) with h | h
    · intro w hw
      have hle : W.subgroupOf (wcgapsp_K1 (F := F)) ≤ (wcgapsp_leviK1 (F := F)).ker := by
        rw [← Subgroup.map_eq_bot_iff]; exact h
      have hmem : (⟨w, hW.2.1 hw⟩ : ↥(wcgapsp_K1 (F := F))) ∈
          (wcgapsp_leviK1 (F := F)).ker := hle hw
      rw [wcgapsp_leviK1_ker] at hmem
      exact hmem
    · exfalso
      obtain ⟨n, hn⟩ := hS2.exists_card_dvd_pow
      rw [h, Subgroup.card_top, card_sl_two hF] at hn
      have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h32
  · have hRn : ((wcgapsp_radSub1 (F := F)).subgroupOf (wcgapsp_K1 (F := F))).Normal :=
      (wcgapsp_leviK1_ker (F := F)).symm ▸ MonoidHom.normal_ker _
    exact wcgapsp_le_oTwoMod_of_isPGroup (wcgapsp_radSub1_le_K1 (F := F)) hRn
      (wcgapsp_isPGroup_radSub1 hF)

private theorem wcgapsp_oddResMod_P0 (hF : Nat.card F = 4) :
    oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_P0 (F := F)) =
      wcgapsp_K0 (F := F) := by
  haveI : Finite F := finite_of_card_eq_four hF
  apply le_antisymm
  · have hmem : (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ wcgapsp_K0 (F := F) ∧
        wcgapsp_K0 (F := F) ≤ wcgapsp_P0 (F := F) ∧
        ((wcgapsp_K0 (F := F)).subgroupOf (wcgapsp_P0 (F := F))).Normal ∧
        Odd ((wcgapsp_K0 (F := F)).relIndex (wcgapsp_P0 (F := F))) := by
      refine ⟨bot_le, wcgapsp_K0_le_P0, ?_, ?_⟩
      · rw [wcgapsp_K0_subgroupOf]; infer_instance
      · rw [wcgapsp_K0_relIndex hF]; norm_num
    exact wcgapsp_oddResMod_le_of_mem (G := SpecialLinearGroup (Fin 3) F)
      (P := wcgapsp_P0 (F := F)) (K := wcgapsp_K0 (F := F))
      hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
  · intro k hk
    rw [oddResMod]
    rw [Subgroup.mem_iInf]
    intro Q
    rw [Subgroup.mem_iInf]
    intro hQ
    exact wcgapsp_le_of_surj_simple (K := wcgapsp_K0 (F := F)) (P := wcgapsp_P0 (F := F))
      (Q := Q) (R := radSub (k := F)) wcgapsp_K0_le_P0 hQ.2.2.1 hQ.2.2.2
      (wcgapsp_radSub_le_K0 (F := F)) (wcgapsp_isPGroup_radSub hF) (wcgapsp_leviK0 hF)
      (wcgapsp_leviK0_surjective hF) (wcgapsp_leviK0_ker hF) (isSimpleGroup_sl_two hF)
      (by rw [card_sl_two hF]; norm_num) hk

private theorem wcgapsp_oddResMod_P1 (hF : Nat.card F = 4) :
    oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_P1 (F := F)) =
      wcgapsp_K1 (F := F) := by
  haveI : Finite F := finite_of_card_eq_four hF
  apply le_antisymm
  · have hmem : (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ wcgapsp_K1 (F := F) ∧
        wcgapsp_K1 (F := F) ≤ wcgapsp_P1 (F := F) ∧
        ((wcgapsp_K1 (F := F)).subgroupOf (wcgapsp_P1 (F := F))).Normal ∧
        Odd ((wcgapsp_K1 (F := F)).relIndex (wcgapsp_P1 (F := F))) := by
      refine ⟨bot_le, wcgapsp_K1_le_P1, ?_, ?_⟩
      · rw [wcgapsp_K1_subgroupOf]; infer_instance
      · rw [wcgapsp_K1_relIndex hF]; norm_num
    exact wcgapsp_oddResMod_le_of_mem (G := SpecialLinearGroup (Fin 3) F)
      (P := wcgapsp_P1 (F := F)) (K := wcgapsp_K1 (F := F))
      hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
  · intro k hk
    rw [oddResMod]
    rw [Subgroup.mem_iInf]
    intro Q
    rw [Subgroup.mem_iInf]
    intro hQ
    exact wcgapsp_le_of_surj_simple (K := wcgapsp_K1 (F := F)) (P := wcgapsp_P1 (F := F))
      (Q := Q) (R := wcgapsp_radSub1 (F := F)) wcgapsp_K1_le_P1 hQ.2.2.1 hQ.2.2.2
      (wcgapsp_radSub1_le_K1 (F := F)) (wcgapsp_isPGroup_radSub1 hF) wcgapsp_leviK1
      wcgapsp_leviK1_surjective
      (wcgapsp_leviK1_ker (F := F)) (isSimpleGroup_sl_two hF)
      (by rw [card_sl_two hF]; norm_num) hk

private theorem wcgapsp_isMaxParabolicMod_P0 (hF : Nat.card F = 4) :
    IsMaxParabolicMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) ⊤
      (wcgapsp_P0 (F := F)) := by
  haveI : Finite F := finite_of_card_eq_four hF
  haveI : CharP F 2 := charP_two_of_card_eq_four hF
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  refine ⟨bot_le, ?_, ?_, wcgapsp_U (F := F), bot_le, le_top, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne le_top (stabilizer_flagSpace_ne_top (K := F) (n := 3) (d := 1)
      le_rfl (by norm_num))
  · intro Y hY _
    rcases eq_of_stabilizer_flagSpace_le (K := F) (n := 3) (d := 1) Y hY.1 with h | h
    · exact absurd (le_of_eq h) hY.2
    · exact h
  · intro s hs
    have hs2 : IsPGroup 2 (wcgapsp_U (F := F)) := by
      change IsPGroup 2 (unitriangular 3 F)
      rw [← hP]; exact P.isPGroup'
    obtain ⟨k, hk⟩ := hs2 ⟨s, hs⟩
    exact ⟨k, Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hk)⟩
  · rw [Subgroup.relIndex_top_right]
    change ¬ 2 ∣ (unitriangular 3 F).index
    rw [← hP]
    exact P.not_dvd_index
  · intro x hx
    rw [top_inf_eq] at hx
    rw [normalizer_unitriangular] at hx
    exact wcgapsp_B_le_P0 hx

private theorem wcgapsp_isMaxParabolicMod_P1 (hF : Nat.card F = 4) :
    IsMaxParabolicMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) ⊤
      (wcgapsp_P1 (F := F)) := by
  haveI : Finite F := finite_of_card_eq_four hF
  haveI : CharP F 2 := charP_two_of_card_eq_four hF
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  refine ⟨bot_le, ?_, ?_, wcgapsp_U (F := F), bot_le, le_top, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne le_top (stabilizer_flagSpace_ne_top (K := F) (n := 3) (d := 2)
      (by norm_num) (by norm_num))
  · intro Y hY _
    rcases eq_of_stabilizer_flagSpace_le (K := F) (n := 3) (d := 2) Y hY.1 with h | h
    · exact absurd (le_of_eq h) hY.2
    · exact h
  · intro s hs
    have hs2 : IsPGroup 2 (wcgapsp_U (F := F)) := by
      change IsPGroup 2 (unitriangular 3 F)
      rw [← hP]; exact P.isPGroup'
    obtain ⟨k, hk⟩ := hs2 ⟨s, hs⟩
    exact ⟨k, Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hk)⟩
  · rw [Subgroup.relIndex_top_right]
    change ¬ 2 ∣ (unitriangular 3 F).index
    rw [← hP]
    exact P.not_dvd_index
  · intro x hx
    rw [top_inf_eq] at hx
    rw [normalizer_unitriangular] at hx
    exact wcgapsp_B_le_P1 hx


private theorem wcgapsp_index_upperTriangular_two
    (hF : Nat.card F = 4) : (upperTriangular 2 F).index = 5 := by
  classical
  haveI : Finite F := finite_of_card_eq_four hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU₂card : Nat.card (unitriangular 2 F) = 4 := by
    rw [card_unitriangular (K := F) 2, hF]; norm_num
  have hU₂pgroup : IsPGroup 2 (unitriangular 2 F) :=
    IsPGroup.of_card (n := 2) (by rw [hU₂card]; norm_num)
  have hL2 : IsL2 (Matrix.SpecialLinearGroup (Fin 2) F) 2 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL (n := 2) (F := F)
      (by norm_num) (by rw [hF]; norm_num)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
  obtain ⟨e⟩ : Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
      alternatingGroup (Fin 5)) :=
    CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL2
  have hA₅card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
  have hP₀card : Nat.card ((unitriangular 2 F).map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hU₂card]
  have hP₀idx : ¬ 2 ∣ ((unitriangular 2 F).map e.toMonoidHom).index := by
    have h := Subgroup.index_mul_card ((unitriangular 2 F).map e.toMonoidHom)
    rw [hP₀card, hA₅card] at h
    have h15 : ((unitriangular 2 F).map e.toMonoidHom).index = 15 := by omega
    rw [h15]; norm_num
  let P : Sylow 2 (alternatingGroup (Fin 5)) :=
    (hU₂pgroup.map e.toMonoidHom).toSylow hP₀idx
  have hPcoe : (P : Subgroup (alternatingGroup (Fin 5))) =
      (unitriangular 2 F).map e.toMonoidHom := IsPGroup.toSylow_coe _ _
  have hPindex : (Subgroup.normalizer (P : Set (alternatingGroup (Fin 5)))).index = 5 := by
    rw [← Sylow.card_eq_index_normalizer P, CFSG.GroupTheory.AlternatingFive.card_sylowTwo]
  have hmapB : (upperTriangular 2 F).map e.toMonoidHom =
      Subgroup.normalizer (P : Set (alternatingGroup (Fin 5))) := by
    rw [← normalizer_unitriangular,
      Subgroup.map_normalizer_eq_of_bijective (unitriangular 2 F)
        (f := e.toMonoidHom) e.bijective, ← hPcoe]
    rfl
  have hmapidx : ((upperTriangular 2 F).map e.toMonoidHom).index =
      (upperTriangular 2 F).index := by
    rw [Subgroup.index_map_of_injective (H := upperTriangular 2 F) (f := e.toMonoidHom)
      e.injective, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.index_top, mul_one]
  rw [← hmapidx, hmapB, hPindex]

private theorem wcgapsp_leviK0_apply (hF : Nat.card F = 4)
    (x : ↥(wcgapsp_K0 (F := F))) :
    ((wcgapsp_leviK0 hF x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1,
          ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2;
          ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1,
          ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2] := by
  have hx00 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 :=
    (wcgapsp_mem_K0.mp x.2).2
  have hx1 := (mem_stabilizer_flagSpace_one.mp (wcgapsp_mem_K0.mp x.2).1).1
  have hx2 := (mem_stabilizer_flagSpace_one.mp (wcgapsp_mem_K0.mp x.2).1).2
  have hblkdet : (blk ((x : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    have hdet := det_eq_mul_det_blk (k := F) hx1 hx2
    rw [hx00, one_mul] at hdet
    rw [show ((x : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 from (x : SpecialLinearGroup (Fin 3) F).2] at hdet
    exact hdet.symm
  change (levi hF (Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)) x) :
    Matrix (Fin 2) (Fin 2) F) = _
  rw [show (levi hF (Subgroup.inclusion (wcgapsp_K0_le_P0 (F := F)) x) :
      Matrix (Fin 2) (Fin 2) F) =
      (blk ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det •
        blk ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) from rfl]
  rw [hblkdet, one_smul]
  rfl

private theorem wcgapsp_K0_inf_B_subgroupOf (hF : Nat.card F = 4) :
    (wcgapsp_K0 (F := F) ⊓ wcgapsp_B (F := F)).subgroupOf (wcgapsp_K0 (F := F)) =
      (upperTriangular 2 F).comap (wcgapsp_leviK0 hF) := by
  ext x
  have hx10 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 :=
    (mem_stabilizer_flagSpace_one.mp (wcgapsp_mem_K0.mp x.2).1).1
  have hx20 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 :=
    (mem_stabilizer_flagSpace_one.mp (wcgapsp_mem_K0.mp x.2).1).2
  have hxB : (x : SpecialLinearGroup (Fin 3) F) ∈ wcgapsp_B (F := F) ↔
      ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    change (x : SpecialLinearGroup (Fin 3) F) ∈ upperTriangular 3 F ↔ _
    rw [mem_upperTriangular]
    constructor
    · intro h; exact h 2 1 (by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact hx10
      · exact hx20
      · exact h
  have hxU : wcgapsp_leviK0 hF x ∈ upperTriangular 2 F ↔
      ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    rw [mem_upperTriangular]
    constructor
    · intro h
      have h10 := h 1 0 (by decide)
      rw [wcgapsp_leviK0_apply hF x] at h10
      simpa using h10
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      rw [wcgapsp_leviK0_apply hF x]
      simpa using h
  show (x : SpecialLinearGroup (Fin 3) F) ∈ wcgapsp_K0 (F := F) ⊓ wcgapsp_B (F := F) ↔
    wcgapsp_leviK0 hF x ∈ upperTriangular 2 F
  rw [Subgroup.mem_inf, hxB, hxU]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

private theorem wcgapsp_relIndex_K0_B (hF : Nat.card F = 4) :
    (wcgapsp_K0 (F := F) ⊓ (⊤ ⊓ normalizer (wcgapsp_U (F := F) :
      Set (SpecialLinearGroup (Fin 3) F)))).relIndex (wcgapsp_K0 (F := F)) = 5 := by
  haveI : Finite F := finite_of_card_eq_four hF
  rw [top_inf_eq]
  change ((wcgapsp_K0 (F := F) ⊓ Subgroup.normalizer
    (unitriangular 3 F : Set (SpecialLinearGroup (Fin 3) F))).subgroupOf
    (wcgapsp_K0 (F := F))).index = 5
  rw [normalizer_unitriangular]
  change ((wcgapsp_K0 (F := F) ⊓ wcgapsp_B (F := F)).subgroupOf
    (wcgapsp_K0 (F := F))).index = 5
  rw [wcgapsp_K0_inf_B_subgroupOf hF]
  have hidx : ((upperTriangular 2 F).comap (wcgapsp_leviK0 hF)).index =
      (upperTriangular 2 F).index :=
    Subgroup.index_comap_of_surjective (H := upperTriangular 2 F)
      (wcgapsp_leviK0_surjective hF)
  exact hidx.trans (wcgapsp_index_upperTriangular_two hF)

private theorem wcgapsp_K1_inf_B_subgroupOf :
    (wcgapsp_K1 (F := F) ⊓ wcgapsp_B (F := F)).subgroupOf (wcgapsp_K1 (F := F)) =
      (upperTriangular 2 F).comap (wcgapsp_leviK1 (F := F)) := by
  ext x
  have hx10 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 :=
    (wcgapsp_mem_P1_iff.mp (wcgapsp_mem_K1.mp x.2).1).1
  have hx11 : ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
    (wcgapsp_mem_P1_iff.mp (wcgapsp_mem_K1.mp x.2).1).2
  have hxB : (x : SpecialLinearGroup (Fin 3) F) ∈ wcgapsp_B (F := F) ↔
      ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
    change (x : SpecialLinearGroup (Fin 3) F) ∈ upperTriangular 3 F ↔ _
    rw [mem_upperTriangular]
    constructor
    · intro h; exact h 1 0 (by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact h
      · exact hx10
      · exact hx11
  have hxU : wcgapsp_leviK1 (F := F) x ∈ upperTriangular 2 F ↔
      ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
    rw [mem_upperTriangular]
    constructor
    · intro h
      have h10 := h 1 0 (by decide)
      change wcgapsp_tl ((x : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 0 = 0 at h10
      simpa [wcgapsp_tl] using h10
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      change wcgapsp_tl ((x : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 1 0 = 0
      simpa [wcgapsp_tl] using h
  show (x : SpecialLinearGroup (Fin 3) F) ∈ wcgapsp_K1 (F := F) ⊓ wcgapsp_B (F := F) ↔
    wcgapsp_leviK1 (F := F) x ∈ upperTriangular 2 F
  rw [Subgroup.mem_inf, hxB, hxU]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

private theorem wcgapsp_relIndex_K1_B (hF : Nat.card F = 4) :
    (wcgapsp_K1 (F := F) ⊓ (⊤ ⊓ normalizer (wcgapsp_U (F := F) :
      Set (SpecialLinearGroup (Fin 3) F)))).relIndex (wcgapsp_K1 (F := F)) = 5 := by
  haveI : Finite F := finite_of_card_eq_four hF
  rw [top_inf_eq]
  change ((wcgapsp_K1 (F := F) ⊓ Subgroup.normalizer
    (unitriangular 3 F : Set (SpecialLinearGroup (Fin 3) F))).subgroupOf
    (wcgapsp_K1 (F := F))).index = 5
  rw [normalizer_unitriangular]
  change ((wcgapsp_K1 (F := F) ⊓ wcgapsp_B (F := F)).subgroupOf
    (wcgapsp_K1 (F := F))).index = 5
  rw [wcgapsp_K1_inf_B_subgroupOf]
  have hidx : ((upperTriangular 2 F).comap (wcgapsp_leviK1 (F := F))).index =
      (upperTriangular 2 F).index :=
    Subgroup.index_comap_of_surjective (H := upperTriangular 2 F)
      wcgapsp_leviK1_surjective
  exact hidx.trans (wcgapsp_index_upperTriangular_two hF)

private theorem wcgapsp_unitri_entries {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ unitriangular 3 F) :
    ((A : Matrix (Fin 3) (Fin 3) F)) 0 0 = 1 ∧ ((A : Matrix (Fin 3) (Fin 3) F)) 1 1 = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) F)) 2 2 = 1 ∧ ((A : Matrix (Fin 3) (Fin 3) F)) 1 0 = 0 ∧
      ((A : Matrix (Fin 3) (Fin 3) F)) 2 0 = 0 ∧ ((A : Matrix (Fin 3) (Fin 3) F)) 2 1 = 0 := by
  obtain ⟨hlo, hdiag⟩ := mem_unitriangular.mp hA
  exact ⟨hdiag 0, hdiag 1, hdiag 2, hlo 1 0 (by decide), hlo 2 0 (by decide),
    hlo 2 1 (by decide)⟩

private theorem wcgapsp_wMat_commute_unitriangular (c : F)
    {s : SpecialLinearGroup (Fin 3) F} (hs : s ∈ unitriangular 3 F) :
    wMat c * s = s * wMat c := by
  obtain ⟨h00, h11, h22, h10, h20, h21⟩ := wcgapsp_unitri_entries hs
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [wMat, wM, coe_wMat, Matrix.mul_apply, Fin.sum_univ_three, h00, h11, h22, h10, h20,
      h21]
  all_goals ring

private theorem wcgapsp_central (hF : Nat.card F = 4) :
    ∀ a ∈ radSub (k := F), a ∈ wcgapsp_radSub1 (F := F) →
      ∀ s ∈ unitriangular 3 F, a * s = s * a := by
  intro a ha ha1 s hs
  obtain ⟨b, c, rfl⟩ := mem_radSub.mp ha
  obtain ⟨b', c', hbc⟩ := wcgapsp_mem_radSub1.mp ha1
  have h01 : b = 0 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
      ((g : Matrix (Fin 3) (Fin 3) F)) 0 1) hbc
    simpa [coe_rad, wcgapsp_coe_rad1] using this.symm
  have hae : rad b c = wMat c := by
    rw [h01]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_rad, coe_wMat, wM]
  rw [hae]
  exact wcgapsp_wMat_commute_unitriangular c hs

theorem wcgapsp_rankTwoParabData_slThree_unitriangular {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 4) :
    RankTwoParabData (unitriangular 3 F : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  let P : Fin 2 → Subgroup (SpecialLinearGroup (Fin 3) F) :=
    ![wcgapsp_P0 (F := F), wcgapsp_P1 (F := F)]
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · show IsMaxParabolicMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) ⊤
        (wcgapsp_P0 (F := F))
      exact wcgapsp_isMaxParabolicMod_P0 hF
    · show IsMaxParabolicMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) ⊤
        (wcgapsp_P1 (F := F))
      exact wcgapsp_isMaxParabolicMod_P1 hF
  · intro i
    fin_cases i
    · show unitriangular 3 F ≤ oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
        (wcgapsp_P0 (F := F))
      rw [wcgapsp_oddResMod_P0 hF]
      exact wcgapsp_U_le_K0 (F := F)
    · show unitriangular 3 F ≤ oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
        (wcgapsp_P1 (F := F))
      rw [wcgapsp_oddResMod_P1 hF]
      exact wcgapsp_U_le_K1 (F := F)
  · intro i
    fin_cases i
    · show HasQuotShape (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
          (wcgapsp_P0 (F := F)))
          (oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
            (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
              (wcgapsp_P0 (F := F))) : Set (SpecialLinearGroup (Fin 3) F))
          (fun X _ => IsL2 X 2)
      rw [wcgapsp_oddResMod_P0 hF, wcgapsp_oTwoMod_K0 hF]
      refine ⟨SpecialLinearGroup (Fin 2) F, inferInstance, wcgapsp_leviK0 hF,
        wcgapsp_leviK0_surjective hF, ?_, ?_⟩
      · intro k
        rw [← MonoidHom.mem_ker, wcgapsp_leviK0_ker hF, Subgroup.mem_subgroupOf]
        rfl
      · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL
          (X := SpecialLinearGroup (Fin 2) F) (n := 2) (by norm_num) (by rw [hF]; norm_num)
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
    · show HasQuotShape (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
          (wcgapsp_P1 (F := F)))
          (oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
            (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
              (wcgapsp_P1 (F := F))) : Set (SpecialLinearGroup (Fin 3) F))
          (fun X _ => IsL2 X 2)
      rw [wcgapsp_oddResMod_P1 hF, wcgapsp_oTwoMod_K1 hF]
      refine ⟨SpecialLinearGroup (Fin 2) F, inferInstance, wcgapsp_leviK1,
        wcgapsp_leviK1_surjective, ?_, ?_⟩
      · intro k
        rw [← MonoidHom.mem_ker, wcgapsp_leviK1_ker, Subgroup.mem_subgroupOf]
        rfl
      · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL
          (X := SpecialLinearGroup (Fin 2) F) (n := 2) (by norm_num) (by rw [hF]; norm_num)
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
  · intro i
    fin_cases i
    · show (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_P0 (F := F)) ⊓
          (⊤ ⊓ normalizer (unitriangular 3 F :
            Set (SpecialLinearGroup (Fin 3) F)))).relIndex
          (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_P0 (F := F))) = 5
      rw [wcgapsp_oddResMod_P0 hF]
      exact wcgapsp_relIndex_K0_B hF
    · show (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_P1 (F := F)) ⊓
          (⊤ ⊓ normalizer (unitriangular 3 F :
            Set (SpecialLinearGroup (Fin 3) F)))).relIndex
          (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F)) (wcgapsp_P1 (F := F))) = 5
      rw [wcgapsp_oddResMod_P1 hF]
      exact wcgapsp_relIndex_K1_B hF
  · intro a ha ha1 s hs
    have ha' : a ∈ radSub (k := F) := by
      have h0 : oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
          (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
            (wcgapsp_P0 (F := F))) = radSub (k := F) := by
        rw [wcgapsp_oddResMod_P0 hF, wcgapsp_oTwoMod_K0 hF]
      have := ha
      change a ∈ oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
        (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
          (wcgapsp_P0 (F := F))) at this
      rwa [h0] at this
    have ha1' : a ∈ wcgapsp_radSub1 (F := F) := by
      have h1 : oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
          (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
            (wcgapsp_P1 (F := F))) = wcgapsp_radSub1 (F := F) := by
        rw [wcgapsp_oddResMod_P1 hF, wcgapsp_oTwoMod_K1 hF]
      have := ha1
      change a ∈ oTwoMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
        (oddResMod (⊥ : Subgroup (SpecialLinearGroup (Fin 3) F))
          (wcgapsp_P1 (F := F))) at this
      rwa [h1] at this
    exact wcgapsp_central hF a ha' ha1' s hs

end CFSG.LocalAnalysis.WeakClosure81

end
