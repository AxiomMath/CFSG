module

public import CFSG.RankThree.PartOne.CTP.LinearModel
public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open CFSG.LieType.Universal.Unitary (SUid conjTr conjTr_mul)
open CFSG.LieType.Steinberg (embPair embSUid coe_embSUid embPair_mul embPair_one embPair_injective
  conjTr_embPair conjTr_diagonal)
open CFSG.ClassicalGroups.Unitary (herm herm_mulVec mkSU)
open CFSG.ClassicalInvolution.WeakCT (coe_blockSL)
open CFSG.ClassicalInvolution.Phan (embPair_two_eq_blockMat embPair_zero_eq_blockMat)
open scoped MatrixGroups

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] def ublkGroup (W ℓ : Submodule F (Fin 3 → F)) : Subgroup (SUid σ 3) where
  carrier := {g | (∀ v ∈ ℓ, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) ∧
    ∀ v, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W ↔ v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · simp [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb1 v hv, ha1 v hv]
    · simp [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ha2, hb2]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · have := ha1 v hv
      calc (((a⁻¹ : SUid σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
          = ((((a : GL (Fin 3) F))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              (((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by rw [this]; rfl
        _ = v := glInv_mulVec _ v
    · rw [← ha2 ((((a⁻¹ : SUid σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)]
      exact iff_of_eq (by rw [show ((a⁻¹ : SUid σ 3) : GL (Fin 3) F) = (a : GL (Fin 3) F)⁻¹ from
        rfl, gl_mulVec_inv])

@[expose] def suToSL : SUid σ 3 →* SL(3, F) where
  toFun g := ⟨((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), g.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem suToSL_injective : Function.Injective (suToSL σ) := by
  intro g h hgh
  have := congrArg (fun s : SL(3, F) => (s : Matrix (Fin 3) (Fin 3) F)) hgh
  exact Subtype.ext (Units.ext this)

theorem mem_ublkGroup_iff (W ℓ : Submodule F (Fin 3 → F)) (g : SUid σ 3) :
    g ∈ ublkGroup σ W ℓ ↔ suToSL σ g ∈ blkGroup F W ℓ :=
  Iff.rfl

theorem mem_range_embSUid_iff (c : Fin 3) (g : SUid σ 3) :
    g ∈ (embSUid σ c).range ↔ ∃ A : SL(2, F),
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        embPair c (A : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨⟨((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), A.2.1⟩, coe_embSUid σ c A⟩
  · rintro ⟨A, hA⟩
    have hconj : conjTr σ (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have h := g.2.2
      rw [hA, conjTr_embPair, ← embPair_mul] at h
      exact embPair_injective c (h.trans (embPair_one c).symm)
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL A, A.2, hconj⟩, ?_⟩
    exact Subtype.ext (Units.ext (by rw [coe_embSUid]; exact hA.symm))

private theorem mem_blkGroup_std_B12_iff (g : SL(3, F)) :
    g ∈ blkGroup F (Submodule.span F {Pi.single 0 1, Pi.single 1 1})
        (Submodule.span F {Pi.single 2 1}) ↔
      ∃ A : SL(2, F), (g : Matrix (Fin 3) (Fin 3) F) =
        embPair 2 (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [blkGroup_std_B12]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, by rw [coe_blockSL, embPair_two_eq_blockMat]⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, Subtype.ext (by rw [coe_blockSL, ← embPair_two_eq_blockMat, hA])⟩

private theorem mem_blkGroup_std_B23_iff (g : SL(3, F)) :
    g ∈ blkGroup F (Submodule.span F {Pi.single 1 1, Pi.single 2 1})
        (Submodule.span F {Pi.single 0 1}) ↔
      ∃ A : SL(2, F), (g : Matrix (Fin 3) (Fin 3) F) =
        embPair 0 (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [blkGroup_std_B23]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, by rw [coe_blockSL, embPair_zero_eq_blockMat]⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, Subtype.ext (by rw [coe_blockSL, ← embPair_zero_eq_blockMat, hA])⟩

theorem ublk_std_B12 :
    ublkGroup σ (Submodule.span F {Pi.single 0 1, Pi.single 1 1})
      (Submodule.span F {Pi.single 2 1}) = (embSUid σ 2).range := by
  ext g
  rw [mem_ublkGroup_iff, mem_blkGroup_std_B12_iff, mem_range_embSUid_iff]
  rfl

theorem ublk_std_B23 :
    ublkGroup σ (Submodule.span F {Pi.single 1 1, Pi.single 2 1})
      (Submodule.span F {Pi.single 0 1}) = (embSUid σ 0).range := by
  ext g
  rw [mem_ublkGroup_iff, mem_blkGroup_std_B23_iff, mem_range_embSUid_iff]
  rfl

private theorem exists_su_columns (b : Fin 3 → Fin 3 → F)
    (hb : ∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) :
    ∃ (P : SUid σ 3) (d : F), d ≠ 0 ∧ ∀ i j,
      ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j = (if j = 2 then d⁻¹ else 1) * b j i := by
  set Q : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => b j i with hQ
  have hQQ : conjTr σ Q * Q = 1 := by
    ext i j
    have := hb i j
    simpa [Matrix.mul_apply, conjTr, herm, Matrix.one_apply, hQ] using this
  have hd : σ Q.det * Q.det = 1 := by
    have h1 := congrArg Matrix.det hQQ
    rw [Matrix.det_mul, Matrix.det_one] at h1
    have h2 : (conjTr σ Q).det = σ Q.det := by
      rw [conjTr, Matrix.det_transpose]
      exact (RingHom.map_det σ.toRingHom Q).symm
    rwa [h2] at h1
  have hd0 : Q.det ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hd
    exact zero_ne_one hd
  set s : Fin 3 → F := fun j => if j = 2 then (Q.det)⁻¹ else 1 with hs
  have hss : ∀ j, σ (s j) * s j = 1 := by
    intro j
    by_cases hj : j = 2
    · simp only [hs, hj, ite_true, map_inv₀]
      rw [← mul_inv, hd, inv_one]
    · simp [hs, hj]
  have hPm : (Q * Matrix.diagonal s).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hs, hd0]
  have hconj : conjTr σ (Q * Matrix.diagonal s) * (Q * Matrix.diagonal s) = 1 := by
    rw [conjTr_mul, conjTr_diagonal, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ Q) Q,
      hQQ, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
    simp_rw [hss]
    exact Matrix.diagonal_one
  have hiso : ∀ x y, herm σ ((Q * Matrix.diagonal s) *ᵥ x) ((Q * Matrix.diagonal s) *ᵥ y) =
      herm σ x y := fun x y => by rw [herm_mulVec, hconj, one_mulVec]
  refine ⟨mkSU σ (Q * Matrix.diagonal s) hPm hiso, Q.det, hd0, fun i j => ?_⟩
  change (Q * Matrix.diagonal s) i j = _
  rw [Matrix.mul_diagonal, mul_comm]
  rfl

private theorem map_std_spans_su (b : Fin 3 → Fin 3 → F) (P : Matrix (Fin 3) (Fin 3) F) (d : F)
    (hd : d ≠ 0) (hP : ∀ i j, P i j = (if j = 2 then d⁻¹ else 1) * b j i) :
    (Submodule.span F {Pi.single 0 1, Pi.single 1 1}).map (Matrix.mulVecLin P) =
        Submodule.span F {b 0, b 1} ∧
      (Submodule.span F {Pi.single 2 1}).map (Matrix.mulVecLin P) = Submodule.span F {b 2} ∧
      (Submodule.span F {Pi.single 1 1, Pi.single 2 1}).map (Matrix.mulVecLin P) =
        Submodule.span F {b 1, b 2} ∧
      (Submodule.span F {Pi.single 0 1}).map (Matrix.mulVecLin P) = Submodule.span F {b 0} := by
  have hPe : ∀ j : Fin 3, P *ᵥ Pi.single j 1 = (if j = 2 then d⁻¹ else 1) • b j := by
    intro j
    funext i
    simp [hP]
  have e0 : P *ᵥ Pi.single 0 1 = b 0 := by simpa using hPe 0
  have e1 : P *ᵥ Pi.single 1 1 = b 1 := by simpa using hPe 1
  have e2 : P *ᵥ Pi.single 2 1 = d⁻¹ • b 2 := by simpa using hPe 2
  have hu : IsUnit d⁻¹ := (inv_ne_zero hd).isUnit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Submodule.map_span, Set.image_pair]
    simp only [Matrix.mulVecLin_apply, e0, e1]
  · rw [Submodule.map_span, Set.image_singleton]
    simp only [Matrix.mulVecLin_apply, e2]
    exact Submodule.span_singleton_smul_eq hu _
  · rw [Submodule.map_span, Set.image_pair]
    simp only [Matrix.mulVecLin_apply, e1, e2]
    rw [Submodule.span_insert, Submodule.span_insert, Submodule.span_singleton_smul_eq hu]
  · rw [Submodule.map_span, Set.image_singleton]
    simp only [Matrix.mulVecLin_apply, e0]

private theorem map_conj_ublkGroup (P : SUid σ 3) (W ℓ W' ℓ' : Submodule F (Fin 3 → F))
    (hW : W.map (Matrix.mulVecLin ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = W')
    (hℓ : ℓ.map (Matrix.mulVecLin ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = ℓ') :
    (ublkGroup σ W ℓ).map (MulAut.conj P).toMonoidHom = ublkGroup σ W' ℓ' := by
  have hconj : ∀ g : SUid σ 3, ((suToSL σ (MulAut.conj P g) : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) =
      ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((suToSL σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        ((((P : GL (Fin 3) F))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := fun g => rfl
  subst hW hℓ
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine (mem_ublkGroup_iff σ _ _ _).mpr ?_
    exact (mem_blkGroup_map_iff (P : GL (Fin 3) F) W ℓ (hconj g)).mpr
      ((mem_ublkGroup_iff σ W ℓ g).mp hg)
  · intro hx
    have hx' : MulAut.conj P (P⁻¹ * x * P) = x := by
      rw [MulAut.conj_apply]; group
    have hg : P⁻¹ * x * P ∈ ublkGroup σ W ℓ := by
      rw [mem_ublkGroup_iff]
      rw [mem_ublkGroup_iff] at hx
      refine (mem_blkGroup_map_iff (P : GL (Fin 3) F) W ℓ (g := suToSL σ (P⁻¹ * x * P))
        (g' := suToSL σ x) ?_).mp hx
      have := hconj (P⁻¹ * x * P)
      rwa [hx'] at this
    exact ⟨_, hg, hx'⟩

theorem exists_conj_of_orthonormal (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (hb : ∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) :
    ∃ c : SUid σ 3,
      ((embSUid σ 2).range.map (MulAut.conj c⁻¹).toMonoidHom =
        ublkGroup σ (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2})) ∧
      ((embSUid σ 0).range.map (MulAut.conj c⁻¹).toMonoidHom =
        ublkGroup σ (Submodule.span F {b 1, b 2}) (Submodule.span F {b 0})) := by
  obtain ⟨P, d, hd, hP⟩ := exists_su_columns σ ⇑b hb
  obtain ⟨m1, m2, m3, m4⟩ := map_std_spans_su ⇑b ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    d hd hP
  refine ⟨P⁻¹, ?_, ?_⟩
  · rw [inv_inv, ← ublk_std_B12]
    exact map_conj_ublkGroup σ P _ _ _ _ m1 m2
  · rw [inv_inv, ← ublk_std_B23]
    exact map_conj_ublkGroup σ P _ _ _ _ m3 m4

end CFSG.RankThree.PartOne.CTP
