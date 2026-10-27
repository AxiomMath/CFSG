module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerYMatrix
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerOrder
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Transport

public section

open CFSG.HardMathSupport.Dickson.I271.TabFi23O7
open CFSG.LieType.Multipliers.O73
open CFSG.YGroups

namespace CFSG.OddTranspositions.FischerMarkedY

open CFSG.Fischer.Classification CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.N143.O7 (Om Iso)
open CFSG.LieType.Multipliers.O73 Matrix

@[expose] noncomputable def sevenForm : LinearMap.BilinForm (ZMod 3) (Fin 7 → ZMod 3) :=
  Matrix.toBilin' !![0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 2]

@[expose] noncomputable def coordinates : (Idx → ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3) :=
  LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) CFSG.HardMathSupport.Timmesfeld.LieRank.O7.e7

theorem sevenForm_apply (v w : Fin 7 → ZMod 3) :
    sevenForm v w = v 0 * w 3 + v 1 * w 4 + v 2 * w 5 + v 3 * w 0 +
      v 4 * w 1 + v 5 * w 2 + 2 * v 6 * w 6 := by
  simp [sevenForm, Matrix.toBilin'_apply, Fin.sum_univ_seven]
  ring_nf
  simp

theorem sevenForm_coordinates (v w : Idx → ZMod 3) :
    sevenForm (coordinates v) (coordinates w) = ∑ i, gv v i * w i := by
  rw [sevenForm_apply]
  simp [coordinates, LinearEquiv.funCongrLeft_apply,
    CFSG.HardMathSupport.Timmesfeld.LieRank.O7.e7, gv, Fintype.sum_sum_type,
    Fin.sum_univ_three]
  ring

theorem isF3Form_sevenForm : IsF3Form sevenForm := by
  constructor
  · intro v w
    rw [sevenForm_apply, sevenForm_apply]
    ring
  · intro v hv
    have h0 := hv (Pi.single 0 1)
    have h1 := hv (Pi.single 1 1)
    have h2 := hv (Pi.single 2 1)
    have h3 := hv (Pi.single 3 1)
    have h4 := hv (Pi.single 4 1)
    have h5 := hv (Pi.single 5 1)
    have h6 := hv (Pi.single 6 1)
    simp only [sevenForm_apply] at h0 h1 h2 h3 h4 h5 h6
    norm_num [Pi.single_apply] at h0 h1 h2 h3 h4 h5 h6
    have hn : (2 : ZMod 3) ≠ 0 := by decide
    have h6' : v 6 = 0 := h6.resolve_left hn
    ext i
    fin_cases i <;> simp_all

theorem sevenForm_vecs (i : Fin 8) : sevenForm (coordinates (vecs i)) (coordinates (vecs i)) = 1 := by
  rw [sevenForm_coordinates]
  have h := vecs_check.1 i
  have hpolar : ∑ j, gv (vecs i) j * vecs i j = 2 * q3 (vecs i) := by
    simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Finset.univ_unique,
      Finset.sum_singleton, gv, q3]
    ring
  rw [hpolar, h]
  decide

@[expose] noncomputable def reindexGL : GL Idx (ZMod 3) ≃* GL (Fin 7) (ZMod 3) :=
  CFSG.HardMathSupport.Timmesfeld.LieRank.O7.Phi.symm

theorem reindexGL_apply (g : GL Idx (ZMod 3)) (v : Idx → ZMod 3) :
    F3.act (reindexGL g) (coordinates v) = coordinates ((g : Matrix Idx Idx (ZMod 3)) *ᵥ v) := by
  ext i
  simp [reindexGL, CFSG.HardMathSupport.Timmesfeld.LieRank.O7.Phi, coordinates,
    LinearEquiv.funCongrLeft_apply, F3.act_def, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_seven,
    CFSG.HardMathSupport.Timmesfeld.LieRank.O7.e7]
  fin_cases i <;> simp <;> ring

theorem reindex_refl_formula (i : Fin 8) (g : GL Idx (ZMod 3))
    (hmat : (g : Matrix Idx Idx (ZMod 3)) = rMat (vecs i)) :
    reindexGL g = F3.refl sevenForm (coordinates (vecs i)) := by
  refine F3.gl_ext fun x => ?_
  obtain ⟨v, rfl⟩ := coordinates.surjective x
  rw [reindexGL_apply, F3.act_refl (sevenForm_vecs i)]
  have hact : rMat (vecs i) *ᵥ v = v + (∑ j, gv (vecs i) j * v j) • vecs i := by
    ext a
    simp only [rMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rcases a with a | a
    · fin_cases a <;> simp <;> ring
    · rcases a with a | a
      · fin_cases a <;> simp <;> ring
      · cases a; simp; ring
  rw [hmat, hact, map_add, map_smul, isF3Form_sevenForm.symm, sevenForm_coordinates]

theorem exists_y322_reflHom_of_data
    {f : LinearMap.BilinForm (ZMod 3) (Fin 7 → ZMod 3)}
    (e : GL Idx (ZMod 3) ≃* GL (Fin 7) (ZMod 3))
    (ρ : YGroup 3 2 2 →* GL Idx (ZMod 3)) (hρ : Function.Injective ρ)
    (v : Fin 8 → Fin 7 → ZMod 3)
    (hgen : ∀ i : Fin 8, e (ρ (yGen 3 2 2 i.val)) = F3.refl f (v i)) :
    ∃ σ : YGroup 3 2 2 →* F3.reflGroup f, Function.Injective σ ∧
      (∀ g, (σ g : GL (Fin 7) (ZMod 3)) = e (ρ g)) ∧
      ∀ i : Fin 8, σ (yGen 3 2 2 i.val) = reflElt f (v i) := by
  let σ : YGroup 3 2 2 →* GL (Fin 7) (ZMod 3) := e.toMonoidHom.comp ρ
  have hσR : σ.range ≤ F3.reflGroup f := by
    rw [MonoidHom.range_eq_map, ← closure_yGen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro g ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have hc8 : c < 8 := by simpa [ngen] using hc
    change e (ρ (yGen 3 2 2 c)) ∈ _
    rw [hgen ⟨c, hc8⟩]
    exact F3.refl_mem_reflGroup _
  let σR : YGroup 3 2 2 →* F3.reflGroup f := σ.codRestrict (F3.reflGroup f) (fun g => hσR ⟨g, rfl⟩)
  refine ⟨σR, fun x y h => hρ (e.injective (congrArg Subtype.val h)), fun g => rfl, fun i => ?_⟩
  exact Subtype.ext (hgen i)


attribute [local irreducible] sevenForm coordinates reindexGL

theorem exists_y322_reflHom :
    ∃ ρ : YGroup 3 2 2 →* F3.reflGroup sevenForm, Function.Injective ρ ∧
      (∀ i : Fin 8, ρ (yGen 3 2 2 i.val) = reflElt sevenForm (coordinates (vecs i))) ∧
      (ρ y322F1 : GL (Fin 7) (ZMod 3)) = -1 := by
  obtain ⟨ρ, hρ, hρgen, hρf⟩ :=
    CFSG.HardMathSupport.Dickson.I271.TabFi23O7.exists_y322_matrix_refl
  obtain ⟨σ, hσ, hσval, hσgen⟩ := exists_y322_reflHom_of_data reindexGL ρ hρ
    (fun i => coordinates (vecs i)) (fun i => reindex_refl_formula i _ (hρgen i))
  refine ⟨σ, hσ, hσgen, ?_⟩
  rw [hσval, hρf]
  unfold reindexGL
  change CFSG.HardMathSupport.Timmesfeld.LieRank.O7.Phi.symm (-1) = -1
  ext i j
  simp [CFSG.HardMathSupport.Timmesfeld.LieRank.O7.Phi]

theorem exists_y322_reflEquiv :
    ∃ e : YGroup 3 2 2 ≃* F3.reflGroup sevenForm,
      (∀ i : Fin 8, e (yGen 3 2 2 i.val) = reflElt sevenForm (coordinates (vecs i))) ∧
      (e y322F1 : GL (Fin 7) (ZMod 3)) = -1 := by
  obtain ⟨ρ, hρ, hgen, hf⟩ := exists_y322_reflHom
  have hcard : Nat.card (F3.reflGroup sevenForm) ≤ Nat.card (YGroup 3 2 2) := by
    rw [card_y322]
    exact CFSG.OddTranspositions.PartFour.natCard_reflGroup_seven_le isF3Form_sevenForm
  have hbij : Function.Bijective ρ := hρ.bijective_of_nat_card_le hcard
  exact ⟨MulEquiv.ofBijective ρ hbij, hgen, hf⟩

theorem exists_y322_reflQuot :
    ∃ π : YGroup 3 2 2 →* R3 sevenForm, Function.Surjective π ∧
      π.ker = Subgroup.zpowers y322F1 ∧
      ∀ i : Fin 8, π (yGen 3 2 2 i.val) = reflBar sevenForm (coordinates (vecs i)) := by
  obtain ⟨e, hegen, hef⟩ := exists_y322_reflEquiv
  let π := (QuotientGroup.mk' (Subgroup.center (F3.reflGroup sevenForm))).comp e.toMonoidHom
  have hsurj : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hfcent : e y322F1 ∈ Subgroup.center (F3.reflGroup sevenForm) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : GL (Fin 7) (ZMod 3)) * (e y322F1 : GL (Fin 7) (ZMod 3)) =
      (e y322F1 : GL (Fin 7) (ZMod 3)) * (g : GL (Fin 7) (ZMod 3))
    rw [hef, mul_neg_one, neg_one_mul]
  have hfle : Subgroup.zpowers y322F1 ≤ π.ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr hfcent
  have hker : π.ker ≤ Subgroup.zpowers y322F1 := by
    intro y hy
    have hcent : e y ∈ Subgroup.center (F3.reflGroup sevenForm) :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    rcases F3.coe_eq_of_mem_center isF3Form_sevenForm (by decide) hcent with h | h
    · have hey : e y = 1 := Subtype.ext h
      have hy1 : y = 1 := e.injective (hey.trans (map_one e).symm)
      rw [hy1]
      exact Subgroup.one_mem _
    · have hyf : y = y322F1 := e.injective (Subtype.ext (h.trans hef.symm))
      rw [hyf]
      exact Subgroup.mem_zpowers _
  refine ⟨π, hsurj, le_antisymm hker hfle, fun i => ?_⟩
  change QuotientGroup.mk (e (yGen 3 2 2 i.val)) = _
  rw [hegen]
  rfl

end CFSG.OddTranspositions.FischerMarkedY
