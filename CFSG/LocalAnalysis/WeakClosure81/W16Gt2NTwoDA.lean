module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

private lemma rank_sub_one_conj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {H : Subgroup (GL ι F)} (g h : ↥H) :
    Matrix.rank (((↑(h * g * h⁻¹) : GL ι F) : Matrix ι ι F) - 1) =
      Matrix.rank (((g : GL ι F) : Matrix ι ι F) - 1) := by
  set A : Matrix ι ι F := ((h : GL ι F) : Matrix ι ι F) with hA
  set B : Matrix ι ι F := ((g : GL ι F) : Matrix ι ι F) with hB
  have hcoe : ((↑(h * g * h⁻¹) : GL ι F) : Matrix ι ι F) = A * B * A⁻¹ := by
    rw [hA, hB, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
  have hAC : A * A⁻¹ = 1 := by
    rw [hA, ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hdetA : IsUnit A.det := by
    rw [hA, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det (h : GL ι F)).isUnit
  have hdetC : IsUnit A⁻¹.det := by
    rw [hA, ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det ((h⁻¹ : ↥H) : GL ι F)).isUnit
  have hsub : A * B * A⁻¹ - 1 = A * (B - 1) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hAC]
  rw [hcoe, hsub, Matrix.rank_mul_eq_left_of_isUnit_det A⁻¹ (A * (B - 1)) hdetC,
    Matrix.rank_mul_eq_right_of_isUnit_det A (B - 1) hdetA]

theorem isSymplecticTransvectionIn_conj {k : ℕ} {F : Type} [Field F] {g : ↥(StatedSp k F)}
    (hg : SevenK.IsSymplecticTransvectionIn k g) (h : ↥(StatedSp k F)) :
    SevenK.IsSymplecticTransvectionIn k (h * g * h⁻¹) := by
  unfold SevenK.IsSymplecticTransvectionIn at hg ⊢
  rw [rank_sub_one_conj g h]
  exact hg

theorem isUnitaryTransvectionIn_conj {m n : ℕ} {F : Type} [Field F]
    {x : StatedProj (StatedSU m (2 ^ n) F)} (hx : SevenK.IsUnitaryTransvectionIn m n x)
    (y : StatedProj (StatedSU m (2 ^ n) F)) :
    SevenK.IsUnitaryTransvectionIn m n (y * x * y⁻¹) := by
  unfold SevenK.IsUnitaryTransvectionIn at hx ⊢
  obtain ⟨g, hgx, hgrank⟩ := hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨h * g * h⁻¹, ?_, ?_⟩
  · rw [← hgx, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  · rw [rank_sub_one_conj g h]
    exact hgrank

theorem rank_transport {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {N : ℕ}
    (h : ∀ E : Subgroup Y', IsElemAbelian 2 E → Nat.card E ≤ N) :
    ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E ≤ N := by
  intro E hE
  have hmap : IsElemAbelian 2 (E.map e.toMonoidHom) := hE.map e.toMonoidHom
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  rw [← hcard]
  exact h _ hmap

theorem out_transport {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ∀ E : Subgroup (MulAut Y'), IsElemAbelian 2 E →
      E ⊓ (MulAut.conj : Y' →* MulAut Y').range = ⊥ → Nat.card E ≤ 2) :
    ∀ E : Subgroup (MulAut Y), IsElemAbelian 2 E →
      E ⊓ (MulAut.conj : Y →* MulAut Y).range = ⊥ → Nat.card E ≤ 2 := by
  intro E hE hinn
  let φ : MulAut Y ≃* MulAut Y' := MulAut.congr e
  let E' : Subgroup (MulAut Y') := E.map φ.toMonoidHom
  have hcongr_conj : ∀ y : Y, φ (MulAut.conj y) = MulAut.conj (e y) := by
    intro y
    ext z
    simp [φ, MulAut.congr_apply, MulAut.conj_apply]
  have hE' : IsElemAbelian 2 E' := hE.map φ.toMonoidHom
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective φ.injective
  have hinn' : E' ⊓ (MulAut.conj : Y' →* MulAut Y').range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro α ⟨hαE, hαI⟩
    obtain ⟨β, hβE, hβ⟩ := Subgroup.mem_map.mp hαE
    obtain ⟨y', hy'⟩ := hαI
    have hβmem : β ∈ E ⊓ (MulAut.conj : Y →* MulAut Y).range := by
      refine ⟨hβE, ⟨e.symm y', ?_⟩⟩
      apply φ.injective
      rw [show φ β = α from hβ, ← hy', hcongr_conj (e.symm y'), e.apply_symm_apply]
    have hβ1 : β = 1 := (Subgroup.eq_bot_iff_forall _).mp hinn β hβmem
    rw [← hβ, hβ1, map_one]
  have hle := h E' hE' hinn'
  exact hcard ▸ hle

end CFSG.LocalAnalysis.WeakClosure81
