module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofSp4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofCubeField
public import CFSG.Assembly.InCatalog

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census5Proof

open Matrix CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
open scoped commutatorElement

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem mem_ker_det_conj_iff {ι : Type} [Fintype ι] [DecidableEq ι] (P g : GL ι K) :
    g ∈ (GeneralLinearGroup.det : GL ι K →* Kˣ).ker ↔
      P * g * P⁻¹ ∈ (GeneralLinearGroup.det : GL ι K →* Kˣ).ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
    mul_comm (GeneralLinearGroup.det P), mul_inv_cancel_right]

theorem isCentData_det_plane (h3 : (3 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0) {D : GL V₄ K}
    (hD : (D : Matrix V₄ V₄ K) = fromBlocks M 0 0 1) :
    IsCentData (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker D iotaPlane := by
  refine ⟨fun B => ?_, fun B => Units.ext ?_, fun g hg h hh hgD hhD => ?_⟩
  · rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, coe_iotaPlane, det_fromBlocks_zero₂₁, det_one, one_mul,
      B.2, Units.val_one]
  · rw [Units.val_mul, Units.val_mul, coe_iotaPlane, hD, fromBlocks_multiply,
      fromBlocks_multiply]
    simp
  · obtain ⟨hk, hkb⟩ := commutator_eq_diag_one h3 hdet hM hD hg hh hgD hhD
    have hkdet : ((g * h * g⁻¹ * h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₂₂.det = 1 := by
      have e := congrArg Units.val (MonoidHom.mem_ker.mp hk)
      rw [GeneralLinearGroup.val_det_apply, hkb, det_fromBlocks_zero₂₁, det_one, one_mul,
        Units.val_one] at e
      exact e
    exact ⟨(⟨_, hkdet⟩ : SpecialLinearGroup (Fin 2) K), Units.ext hkb.symm⟩

@[expose] def cubeBlockHom : Matrix (Fin 2) (Fin 2) (cubeAlg K) →* Matrix V₄ V₄ K where
  toFun B := fromBlocks ((B 0 0 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
    ((B 0 1 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
    ((B 1 0 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
    ((B 1 1 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
  map_one' := by
    simp
  map_mul' B B' := by
    rw [fromBlocks_multiply]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def iotaCube : SpecialLinearGroup (Fin 2) (cubeAlg K) →* GL V₄ K :=
  (Units.map cubeBlockHom).comp SpecialLinearGroup.toGL

theorem coe_iotaCube (B : SpecialLinearGroup (Fin 2) (cubeAlg K)) :
    ((iotaCube B : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks (((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 0 0 : cubeAlg K) :
          Matrix (Fin 2) (Fin 2) K)
        (((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 0 1 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
        (((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 1 0 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)
        (((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 1 1 : cubeAlg K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem iotaCube_mem_ker [Group.IsPerfect (SpecialLinearGroup (Fin 2) (cubeAlg K))]
    (B : SpecialLinearGroup (Fin 2) (cubeAlg K)) :
    iotaCube B ∈ (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker := by
  have hB : B ∈ commutator (SpecialLinearGroup (Fin 2) (cubeAlg K)) := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top B
  exact Abelianization.commutator_subset_ker
    (f := (GeneralLinearGroup.det : GL V₄ K →* Kˣ).comp iotaCube) hB

theorem isCentData_det_cube [Group.IsPerfect (SpecialLinearGroup (Fin 2) (cubeAlg K))]
    {D : GL V₄ K} (hD : (D : Matrix V₄ V₄ K) = fromBlocks (cubeMat K) 0 0 (cubeMat K)) :
    IsCentData (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker D iotaCube := by
  refine ⟨iotaCube_mem_ker, fun B => Units.ext ?_, fun g hg h hh hgD hhD => ?_⟩
  · rw [Units.val_mul, Units.val_mul, coe_iotaCube, hD, fromBlocks_multiply,
      fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [mem_cubeAlg.mp ((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 0 0).2,
      mem_cubeAlg.mp ((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 0 1).2,
      mem_cubeAlg.mp ((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 1 0).2,
      mem_cubeAlg.mp ((B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 1 1).2]
  · set Cg := (GeneralLinearGroup.det : GL V₄ K →* Kˣ).ker ⊓
      Subgroup.centralizer ({D} : Set (GL V₄ K)) with hCg
    have hblk : ∀ x ∈ Cg, ((x : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₁ ∈ cubeAlg K ∧
        ((x : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₁₂ ∈ cubeAlg K ∧
        ((x : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₂₁ ∈ cubeAlg K ∧
        ((x : GL V₄ K) : Matrix V₄ V₄ K).toBlocks₂₂ ∈ cubeAlg K := by
      intro x hx
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      apply blocks_mem_cubeAlg
      rw [← hD, ← Units.val_mul, ← Units.val_mul, hc]
    have hdetC : ∀ x ∈ Cg, detC ((x : GL V₄ K) : Matrix V₄ V₄ K) ∈ cubeAlg K := by
      intro x hx
      obtain ⟨b1, b2, b3, b4⟩ := hblk x hx
      exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ b1 b4) (Subalgebra.mul_mem _ b2 b3)
    have hgC : g ∈ Cg := ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgD⟩
    have hhC : h ∈ Cg := ⟨hh, Subgroup.mem_centralizer_singleton_iff.mpr hhD⟩
    let χ : Cg →* cubeAlg K :=
      { toFun := fun x => ⟨_, hdetC x x.2⟩
        map_one' := by
          apply Subtype.ext
          change detC (1 : Matrix V₄ V₄ K) = 1
          obtain ⟨o1, o2, o3, o4⟩ := toBlocks_one (K := K) (n := Fin 2)
          rw [detC, o1, o2, o3, o4, Matrix.mul_one, Matrix.zero_mul, sub_zero]
        map_mul' := fun x y => Subtype.ext (by
          change detC ((x : GL V₄ K) * (y : GL V₄ K) : GL V₄ K).val = _
          rw [Units.val_mul]
          exact detC_mul (hblk x x.2) (hblk y y.2)) }
    have hχ : χ.toHomUnits ⁅(⟨g, hgC⟩ : Cg), ⟨h, hhC⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have hk : g * h * g⁻¹ * h⁻¹ ∈ Cg :=
      Cg.mul_mem (Cg.mul_mem (Cg.mul_mem hgC hhC) (Cg.inv_mem hgC)) (Cg.inv_mem hhC)
    set k := ((g * h * g⁻¹ * h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) with hkdef
    have hkdet : detC k = 1 := by
      have := congrArg (fun u : (cubeAlg K)ˣ => ((u : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)) hχ
      rw [commutatorElement_def] at this
      exact this
    obtain ⟨ha, hb, hc, hd⟩ := hblk _ hk
    set B : Matrix (Fin 2) (Fin 2) (cubeAlg K) :=
      !![⟨k.toBlocks₁₁, ha⟩, ⟨k.toBlocks₁₂, hb⟩; ⟨k.toBlocks₂₁, hc⟩, ⟨k.toBlocks₂₂, hd⟩] with hB
    have hBdet : B.det = 1 := by
      rw [Matrix.det_fin_two]
      apply Subtype.ext
      exact hkdet
    refine ⟨(⟨B, hBdet⟩ : SpecialLinearGroup (Fin 2) (cubeAlg K)), Units.ext ?_⟩
    change fromBlocks k.toBlocks₁₁ k.toBlocks₁₂ k.toBlocks₂₁ k.toBlocks₂₂ = k
    exact fromBlocks_toBlocks k

theorem scalar_eq_fromBlocks (c : K) :
    (Matrix.scalar V₄ c : Matrix V₄ V₄ K) =
      fromBlocks (Matrix.scalar (Fin 2) c) 0 0 (Matrix.scalar (Fin 2) c) := by
  ext (i | i) (j | j) <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem ker_mk_iotaCube (hK : ∀ s : K, s * s + s + 1 ≠ 0) :
    (ProjGenLinGroup.mk.comp (iotaCube (K := K))).ker =
      Subgroup.center (SpecialLinearGroup (Fin 2) (cubeAlg K)) := by
  have := (isField_cubeAlg hK).isDomain
  ext B
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar, Matrix.SpecialLinearGroup.mem_center_iff,
    Fintype.card_fin]
  constructor
  · rintro ⟨u, hu⟩
    have e := congrArg (fun x : GL V₄ K => (x : Matrix V₄ V₄ K)) hu
    simp only [GeneralLinearGroup.coe_scalar, coe_iotaCube, scalar_eq_fromBlocks] at e
    obtain ⟨e00, e01, e10, e11⟩ := Matrix.fromBlocks_inj.mp e
    set r : cubeAlg K := (B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 0 0 with hr
    have h01 : (B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 0 1 = 0 := Subtype.ext e01.symm
    have h10 : (B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 1 0 = 0 := Subtype.ext e10.symm
    have h11 : (B : Matrix (Fin 2) (Fin 2) (cubeAlg K)) 1 1 = r :=
      Subtype.ext (e11.symm.trans e00)
    refine ⟨r, ?_, ?_⟩
    · have hdet := B.2
      rw [Matrix.det_fin_two, h01, h10, h11, mul_zero, sub_zero] at hdet
      rw [sq]
      exact hdet
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h11, hr]
  · rintro ⟨r, hr2, hr⟩
    have hr' : r = 1 ∨ r = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hr2)
    rcases hr' with rfl | rfl
    · refine ⟨1, Units.ext ?_⟩
      rw [GeneralLinearGroup.coe_scalar, coe_iotaCube, ← hr, scalar_eq_fromBlocks]
      simp [Matrix.scalar_apply]
    · refine ⟨-1, Units.ext ?_⟩
      rw [GeneralLinearGroup.coe_scalar, coe_iotaCube, ← hr]
      ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply]

end CFSG.RankThree.PartTwo.Sec21.Item228Census5Proof
