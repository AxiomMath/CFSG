module

public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.ClassicalInvolution.WeakCT.Blocks
import CFSG.Quasithin.Vol2.Ch7Prop711Facts
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree
public import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.StandardType.FF81

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.RankThree.CALinearPlane
open CFSG.ClassicalInvolution.Phan (blockMat det_blockMat blockMat_apply)
open scoped MatrixGroups

section Blocks

variable {K : Type} [Field K]

theorem range_blockSL_le_coordBlockSL {m k i : ℕ} (h : i + k ≤ m) {J : Finset (Fin m)}
    (hJ : ∀ x : Fin m, i ≤ x.val → x.val < i + k → x ∈ J) :
    (blockSL K m k i h).range ≤ coordBlockSL K J := by
  rintro _ ⟨A, rfl⟩
  rw [mem_coordBlockSL_iff]
  intro a b hab
  rw [coe_blockSL, blockMat_apply, dif_neg, Matrix.one_apply]
  rintro ⟨ha, hb⟩
  rcases hab with h' | h'
  · exact h' (hJ a ha.1 ha.2)
  · exact h' (hJ b hb.1 hb.2)

theorem coordBlockSL_le_range_blockSL {m k i : ℕ} (h : i + k ≤ m) {J : Finset (Fin m)}
    (hJ : ∀ x ∈ J, i ≤ x.val ∧ x.val < i + k) :
    coordBlockSL K J ≤ (blockSL K m k i h).range := by
  intro u hu
  rw [mem_coordBlockSL_iff] at hu
  let z : Matrix (Fin k) (Fin k) K := Matrix.of fun a b =>
    (u : Matrix (Fin m) (Fin m) K) ⟨i + a.val, by have := a.isLt; omega⟩
      ⟨i + b.val, by have := b.isLt; omega⟩
  have hz : blockMat m i z = (u : Matrix (Fin m) (Fin m) K) := by
    ext a b
    rw [blockMat_apply]
    split_ifs with hab
    · obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hab
      have e1 : (⟨i + (a.val - i), by omega⟩ : Fin m) = a :=
        Fin.ext (show i + (a.val - i) = a.val by omega)
      have e2 : (⟨i + (b.val - i), by omega⟩ : Fin m) = b :=
        Fin.ext (show i + (b.val - i) = b.val by omega)
      exact congrArg₂ (fun p q => (u : Matrix (Fin m) (Fin m) K) p q) e1 e2
    · have h' : a ∉ J ∨ b ∉ J := by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hab ⟨hJ a hcon.1, hJ b hcon.2⟩
      rw [Matrix.one_apply, hu a b h']
  have hdet : z.det = 1 := by rw [← det_blockMat h z, hz]; exact u.2
  exact ⟨⟨z, hdet⟩, Subtype.ext hz⟩

theorem range_blockSL_eq {m k i : ℕ} (h : i + k ≤ m) {J : Finset (Fin m)}
    (hJ : ∀ x : Fin m, x ∈ J ↔ i ≤ x.val ∧ x.val < i + k) :
    (blockSL K m k i h).range = coordBlockSL K J :=
  le_antisymm (range_blockSL_le_coordBlockSL h fun x h1 h2 => (hJ x).2 ⟨h1, h2⟩)
    (coordBlockSL_le_range_blockSL h fun x hx => (hJ x).1 hx)

theorem invTransposeSL_mem_coordBlockSL {m : ℕ} {J : Finset (Fin m)} {u : SL(m, K)}
    (hu : u ∈ coordBlockSL K J) : invTransposeSL m u ∈ coordBlockSL K J := by
  have hu' := (coordBlockSL K J).inv_mem hu
  rw [mem_coordBlockSL_iff] at hu' ⊢
  intro a b hab
  rw [coe_invTransposeSL, transpose_apply, hu' b a hab.symm]
  by_cases hab' : a = b
  · rw [if_pos hab'.symm, if_pos hab']
  · rw [if_neg (Ne.symm hab'), if_neg hab']

variable [CharP K 2]

theorem coe_permSL_conj_submatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) (A : SL(m, K)) :
    ((TypeA.permSL σ * A * (TypeA.permSL σ)⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      (A : Matrix (Fin m) (Fin m) K).submatrix σ σ := by
  rw [TypeA.permSL_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    TypeA.coe_permSL, TypeA.coe_permSL, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem permSL_conj_mem_coordBlockSL {m : ℕ} (σ : Equiv.Perm (Fin m)) {J J' : Finset (Fin m)}
    (hJ : ∀ a, σ a ∈ J → a ∈ J') {u : SL(m, K)} (hu : u ∈ coordBlockSL K J) :
    TypeA.permSL σ * u * (TypeA.permSL σ)⁻¹ ∈ coordBlockSL K J' := by
  rw [mem_coordBlockSL_iff] at hu ⊢
  intro a b hab
  rw [coe_permSL_conj_submatrix, submatrix_apply,
    hu (σ a) (σ b) (hab.imp (mt (hJ a)) (mt (hJ b)))]
  simp only [EmbeddingLike.apply_eq_iff_eq]

end Blocks

section Rotation

@[expose] def overlapRot (M : ℕ) : Equiv.Perm (Fin (M + 2)) :=
  Equiv.addRight ⟨M, by omega⟩

theorem overlapRot_val (M : ℕ) (p : Fin (M + 2)) :
    (overlapRot M p).val = if p.val < 2 then p.val + M else p.val - 2 := by
  have hv : (overlapRot M p).val = (p.val + M) % (M + 2) := by
    simp only [overlapRot, Equiv.coe_addRight, Fin.val_add]
  rw [hv]
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem permSL_overlapRot_conj_blockSL {K : Type} [Field K] [CharP K 2] {M : ℕ} (z : SL(M, K)) :
    TypeA.permSL (overlapRot M) * blockSL K (M + 2) M 0 (by omega) z *
        (TypeA.permSL (overlapRot M))⁻¹ = blockSL K (M + 2) M 2 (by omega) z := by
  apply Subtype.ext
  rw [coe_permSL_conj_submatrix, coe_blockSL, coe_blockSL]
  ext a b
  rw [submatrix_apply, blockMat_apply, blockMat_apply]
  have ha := overlapRot_val M a
  have hb := overlapRot_val M b
  by_cases hab : 2 ≤ a.val ∧ 2 ≤ b.val
  · rw [if_neg (by omega)] at ha
    rw [if_neg (by omega)] at hb
    rw [dif_pos (by omega), dif_pos (by omega)]
    have e1 : (⟨(overlapRot M a).val - 0, by omega⟩ : Fin M) = ⟨a.val - 2, by omega⟩ :=
      Fin.ext (show (overlapRot M a).val - 0 = a.val - 2 by omega)
    have e2 : (⟨(overlapRot M b).val - 0, by omega⟩ : Fin M) = ⟨b.val - 2, by omega⟩ :=
      Fin.ext (show (overlapRot M b).val - 0 = b.val - 2 by omega)
    exact congrArg₂ (fun p q => (z : Matrix (Fin M) (Fin M) K) p q) e1 e2
  · have h1 : ¬((0 ≤ (overlapRot M a).val ∧ (overlapRot M a).val < 0 + M) ∧
        (0 ≤ (overlapRot M b).val ∧ (overlapRot M b).val < 0 + M)) := by
      split_ifs at ha hb <;> omega
    have h2 : ¬((2 ≤ a.val ∧ a.val < 2 + M) ∧ (2 ≤ b.val ∧ b.val < 2 + M)) := by omega
    rw [dif_neg h1, dif_neg h2, Matrix.one_apply, Matrix.one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]

@[expose] def overlapJQ {M : ℕ} (J' : Finset (Fin M)) : Finset (Fin (M + 2)) :=
  Finset.univ.filter fun q => ∀ h : q.val < M, (⟨q.val, h⟩ : Fin M) ∈ J'

@[expose] def overlapJK {M : ℕ} (J' : Finset (Fin M)) : Finset (Fin (M + 2)) :=
  Finset.univ.filter fun p => ∀ h : 2 ≤ p.val, (⟨p.val - 2, by have := p.isLt; omega⟩ : Fin M) ∈ J'

theorem mem_overlapJQ {M : ℕ} {J' : Finset (Fin M)} {q : Fin (M + 2)} :
    q ∈ overlapJQ J' ↔ ∀ h : q.val < M, (⟨q.val, h⟩ : Fin M) ∈ J' := by
  rw [overlapJQ, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_overlapJK {M : ℕ} {J' : Finset (Fin M)} {p : Fin (M + 2)} :
    p ∈ overlapJK J' ↔
      ∀ h : 2 ≤ p.val, (⟨p.val - 2, by have := p.isLt; omega⟩ : Fin M) ∈ J' := by
  rw [overlapJK, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_overlapJK_of_rot {M : ℕ} {J' : Finset (Fin M)} {a : Fin (M + 2)}
    (h : overlapRot M a ∈ overlapJQ J') : a ∈ overlapJK J' := by
  rw [mem_overlapJQ] at h
  rw [mem_overlapJK]
  intro ha
  have hv := overlapRot_val M a
  rw [if_neg (by omega)] at hv
  have hlt : (overlapRot M a).val < M := by omega
  have e : (⟨(overlapRot M a).val, hlt⟩ : Fin M) = ⟨a.val - 2, by omega⟩ := Fin.ext hv
  exact e ▸ h hlt

theorem compIndicator_overlapJQ_mul_blockMat {K : Type} [Field K] {M : ℕ}
    {J' : Finset (Fin M)} {a : Matrix (Fin M) (Fin M) K}
    (ha : compIndicator K J' * a = a * compIndicator K J') :
    compIndicator K (overlapJQ J') * blockMat (M + 2) 0 a =
      blockMat (M + 2) 0 a * compIndicator K (overlapJQ J') := by
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply, blockMat_apply]
  by_cases hij : (0 ≤ i.val ∧ i.val < 0 + M) ∧ (0 ≤ j.val ∧ j.val < 0 + M)
  · rw [dif_pos hij]
    have hiM : i.val < M := by omega
    have hjM : j.val < M := by omega
    have h := congrFun (congrFun ha ⟨i.val, hiM⟩) ⟨j.val, hjM⟩
    rw [compIndicator_mul_apply, mul_compIndicator_apply] at h
    have hi : i ∈ overlapJQ J' ↔ (⟨i.val, hiM⟩ : Fin M) ∈ J' :=
      mem_overlapJQ.trans ⟨fun h => h hiM, fun h _ => h⟩
    have hj : j ∈ overlapJQ J' ↔ (⟨j.val, hjM⟩ : Fin M) ∈ J' :=
      mem_overlapJQ.trans ⟨fun h => h hjM, fun h _ => h⟩
    simp only [hi, hj]
    exact h
  · rw [dif_neg hij, Matrix.one_apply]
    by_cases hij' : i = j
    · subst hij'
      rfl
    · simp only [hij', if_false, ite_self]

end Rotation

theorem eq_one_of_mem_center_SL_two {M : ℕ} (hM : 1 ≤ M) {Y : SL(M, ZMod 2)}
    (hY : Y ∈ Subgroup.center SL(M, ZMod 2)) : Y = 1 := by
  obtain ⟨c, hc, hcY⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hY
  rw [Fintype.card_fin] at hc
  have hc1 : c = 1 := by
    rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) c with rfl | rfl
    · rw [zero_pow (by omega)] at hc
      exact absurd hc (by decide)
    · rfl
  rw [hc1, map_one] at hcY
  exact Subtype.ext hcY.symm

section Overlap

variable {G : Type} [Group G]

private theorem exists_overlap_chart_aux {M : ℕ} (ψ : SL(M + 2, ZMod 2) →* G)
    (hψ : Function.Injective ψ) (x : G) (θ' : SL(M, ZMod 2) ≃* SL(M, ZMod 2))
    (hθ' : ∀ z, ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (θ' z)) =
      x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹)
    (A : SL(M, ZMod 2)) (γ : SL(M, ZMod 2) ≃* SL(M, ZMod 2))
    (γ' : SL(M + 2, ZMod 2) ≃* SL(M + 2, ZMod 2)) (hθA : ∀ z, θ' z = A * γ z * A⁻¹)
    (hγ' : ∀ z, γ' (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) =
      blockSL (ZMod 2) (M + 2) M 0 (by omega) (γ z))
    (hγ'J : ∀ (J : Finset (Fin (M + 2))) (u : SL(M + 2, ZMod 2)),
      u ∈ coordBlockSL (ZMod 2) J → γ'.symm u ∈ coordBlockSL (ZMod 2) J)
    (hcomm : ∀ (J' : Finset (Fin M)) (T : SL(M, ZMod 2)) (o : ℕ),
      compIndicator (ZMod 2) J' = ((T : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o →
      compIndicator (ZMod 2) J' =
        (((T⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o →
      (∀ z, θ' (T * z * T⁻¹) = T * θ' z * T⁻¹) →
      compIndicator (ZMod 2) J' * (A : Matrix (Fin M) (Fin M) (ZMod 2)) =
        (A : Matrix (Fin M) (Fin M) (ZMod 2)) * compIndicator (ZMod 2) J') :
    ∃ ψ₂ : SL(M + 2, ZMod 2) →* G, Function.Injective ψ₂ ∧
      ψ₂.range = ψ.range.map (MulAut.conj x).toMonoidHom ∧
      (∀ z : SL(M, ZMod 2), ψ₂ (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) =
        ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z)) ∧
      ∀ (J' : Finset (Fin M)) (T : SL(M, ZMod 2)) (o : ℕ),
        compIndicator (ZMod 2) J' = ((T : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o →
        compIndicator (ZMod 2) J' =
          (((T⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o →
        (∀ z : SL(M, ZMod 2), x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (T * z * T⁻¹)) * x⁻¹ =
          ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) T) *
            (x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹) *
              (ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) T))⁻¹) →
        (coordBlockSL (ZMod 2) (overlapJQ J')).map ψ₂ ≤
          ((coordBlockSL (ZMod 2) (overlapJK J')).map ψ).map (MulAut.conj x).toMonoidHom := by
  let θ'' : SL(M + 2, ZMod 2) ≃* SL(M + 2, ZMod 2) :=
    γ'.trans (MulAut.conj (blockSL (ZMod 2) (M + 2) M 0 (by omega) A))
  have hθ'' : ∀ z, θ'' (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) =
      blockSL (ZMod 2) (M + 2) M 0 (by omega) (θ' z) := by
    intro z
    show blockSL (ZMod 2) (M + 2) M 0 (by omega) A * γ' (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) *
      (blockSL (ZMod 2) (M + 2) M 0 (by omega) A)⁻¹ = _
    rw [hγ', hθA, map_mul, map_mul, map_inv]
  have hθ''s : ∀ z, θ''.symm (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) =
      blockSL (ZMod 2) (M + 2) M 0 (by omega) (θ'.symm z) := by
    intro z
    rw [MulEquiv.symm_apply_eq, hθ'', MulEquiv.apply_symm_apply]
  let h : SL(M + 2, ZMod 2) →* SL(M + 2, ZMod 2) :=
    (MulAut.conj (TypeA.permSL (K := ZMod 2) (overlapRot M))).toMonoidHom.comp
      θ''.symm.toMonoidHom
  refine ⟨(MulAut.conj x).toMonoidHom.comp (ψ.comp h), ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj x).injective.comp
      (hψ.comp ((MulAut.conj _).injective.comp θ''.symm.injective))
  · have hh : Function.Surjective h := (MulAut.conj _).surjective.comp θ''.symm.surjective
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hh,
      ← MonoidHom.range_eq_map]
  · intro z
    show x * ψ (TypeA.permSL (overlapRot M) * θ''.symm (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) *
      (TypeA.permSL (overlapRot M))⁻¹) * x⁻¹ = _
    rw [hθ''s, permSL_overlapRot_conj_blockSL, ← hθ', MulEquiv.apply_symm_apply]
  · intro J' T o hP1 hP2 hTx
    have hθT : ∀ z, θ' (T * z * T⁻¹) = T * θ' z * T⁻¹ := by
      intro z
      apply hψ.comp (blockSL_injective (K := ZMod 2) (by omega : 2 + M ≤ M + 2))
      show ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (θ' (T * z * T⁻¹))) =
        ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (T * θ' z * T⁻¹))
      rw [hθ', hTx, ← hθ']
      simp only [map_mul, map_inv]
    have hAP := hcomm J' T o hP1 hP2 hθT
    have h1 : (A : Matrix (Fin M) (Fin M) (ZMod 2)) * ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : ((A⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) * (A : Matrix _ _ _) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hAP' : compIndicator (ZMod 2) J' * ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) =
        ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) * compIndicator (ZMod 2) J' := by
      calc compIndicator (ZMod 2) J' * ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _)
          = ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) *
              ((A : Matrix (Fin M) (Fin M) (ZMod 2)) * compIndicator (ZMod 2) J') *
              ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) := by
            rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
        _ = ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) *
              (compIndicator (ZMod 2) J' * (A : Matrix (Fin M) (Fin M) (ZMod 2))) *
              ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) := by rw [hAP]
        _ = ((A⁻¹ : SL(M, ZMod 2)) : Matrix _ _ _) * compIndicator (ZMod 2) J' := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hinv : compIndicator (ZMod 2) (overlapJQ J') *
        (((blockSL (ZMod 2) (M + 2) M 0 (by omega) A)⁻¹ : SL(M + 2, ZMod 2)) : Matrix _ _ _) =
        (((blockSL (ZMod 2) (M + 2) M 0 (by omega) A)⁻¹ : SL(M + 2, ZMod 2)) : Matrix _ _ _) *
          compIndicator (ZMod 2) (overlapJQ J') := by
      rw [← map_inv, coe_blockSL]
      exact compIndicator_overlapJQ_mul_blockMat hAP'
    rintro _ ⟨u, hu, rfl⟩
    have hu1 := conj_mem_coordBlockSL hinv hu
    rw [inv_inv] at hu1
    have hu2 : θ''.symm u ∈ coordBlockSL (ZMod 2) (overlapJQ J') := hγ'J _ _ hu1
    have hu3 := permSL_conj_mem_coordBlockSL (overlapRot M)
      (fun a ha => mem_overlapJK_of_rot ha) hu2
    exact ⟨ψ (TypeA.permSL (overlapRot M) * θ''.symm u * (TypeA.permSL (overlapRot M))⁻¹),
      ⟨_, hu3, rfl⟩, rfl⟩

theorem exists_overlap_chart {M : ℕ} (hM : 3 ≤ M) (ψ : SL(M + 2, ZMod 2) →* G)
    (hψ : Function.Injective ψ) (x : G)
    (hN : ∀ z : SL(M, ZMod 2), ∃ z' : SL(M, ZMod 2),
      x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹ =
        ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z')) :
    ∃ ψ₂ : SL(M + 2, ZMod 2) →* G, Function.Injective ψ₂ ∧
      ψ₂.range = ψ.range.map (MulAut.conj x).toMonoidHom ∧
      (∀ z : SL(M, ZMod 2), ψ₂ (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) =
        ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z)) ∧
      ∀ (J' : Finset (Fin M)) (T : SL(M, ZMod 2)) (o : ℕ),
        compIndicator (ZMod 2) J' = ((T : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o →
        compIndicator (ZMod 2) J' =
          (((T⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o →
        (∀ z : SL(M, ZMod 2), x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (T * z * T⁻¹)) * x⁻¹ =
          ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) T) *
            (x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹) *
              (ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) T))⁻¹) →
        (coordBlockSL (ZMod 2) (overlapJQ J')).map ψ₂ ≤
          ((coordBlockSL (ZMod 2) (overlapJK J')).map ψ).map (MulAut.conj x).toMonoidHom := by
  classical
  have hov : Function.Injective (ψ.comp (blockSL (ZMod 2) (M + 2) M 2 (by omega))) :=
    hψ.comp (blockSL_injective _)
  choose f hf using hN
  have hfmul : ∀ z w, f (z * w) = f z * f w := fun z w => hov (by
    simp only [MonoidHom.comp_apply, map_mul, ← hf]
    group)
  have hfinj : Function.Injective f := by
    intro z w hzw
    apply hov
    have h2 : x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹ =
        x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) w) * x⁻¹ := by
      rw [hf, hf, hzw]
    simpa using h2
  let θ' : SL(M, ZMod 2) ≃* SL(M, ZMod 2) :=
    MulEquiv.ofBijective (MonoidHom.mk' f hfmul) ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  have hθ' : ∀ z, ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (θ' z)) =
      x * ψ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹ := fun z => (hf z).symm
  obtain ⟨A, hA⟩ := CFSG.Quasithin.H13.Prop711.aut_SL_of_card_two (K := ZMod 2)
    (by rw [Nat.card_eq_fintype_card, ZMod.card]) hM θ'
  have hdet : (A : Matrix (Fin M) (Fin M) (ZMod 2)).det = 1 := by
    have hu : IsUnit (A : Matrix (Fin M) (Fin M) (ZMod 2)).det := A.isUnit.map Matrix.detMonoidHom
    obtain ⟨u, hu⟩ := hu
    rw [← hu, Subsingleton.elim u 1, Units.val_one]
  let As : SL(M, ZMod 2) := ⟨A, hdet⟩
  have hAinv : ((As⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) =
      ((A⁻¹ : GL (Fin M) (ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) := by
    have h1 : ((As⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) *
        (A : Matrix (Fin M) (Fin M) (ZMod 2)) = 1 := by
      rw [show (A : Matrix (Fin M) (Fin M) (ZMod 2)) = ((As : SL(M, ZMod 2)) : Matrix _ _ _) from rfl,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((As⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2))
        = ((As⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) *
            ((A : Matrix (Fin M) (Fin M) (ZMod 2)) *
              ((A⁻¹ : GL (Fin M) (ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2))) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rcases hA with hA | hA
  ·
    have hc : ∀ g, θ' g = As * g * As⁻¹ := by
      intro g
      apply Subtype.ext
      rw [hA g, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hAinv]
    refine exists_overlap_chart_aux ψ hψ x θ' hθ' As (MulEquiv.refl _) (MulEquiv.refl _) hc
      (fun _ => rfl) (fun _ _ hu => hu) ?_
    intro J' T o hP1 _ hθT
    have hY : (T * As)⁻¹ * (As * T) ∈ Subgroup.center SL(M, ZMod 2) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := hθT w
      rw [hc, hc] at h1
      calc w * ((T * As)⁻¹ * (As * T)) = (T * As)⁻¹ * (T * (As * w * As⁻¹) * T⁻¹) * (As * T) := by
            group
        _ = (T * As)⁻¹ * (As * (T * w * T⁻¹) * As⁻¹) * (As * T) := by rw [h1]
        _ = (T * As)⁻¹ * (As * T) * w := by group
    have hAT : T * As = As * T := inv_mul_eq_one.mp (eq_one_of_mem_center_SL_two (by omega) hY)
    have hm : Commute (T : Matrix (Fin M) (Fin M) (ZMod 2)) (As : Matrix (Fin M) (Fin M) (ZMod 2)) := by
      show (T : Matrix (Fin M) (Fin M) (ZMod 2)) * (As : Matrix _ _ _) =
        (As : Matrix _ _ _) * (T : Matrix (Fin M) (Fin M) (ZMod 2))
      rw [← Matrix.SpecialLinearGroup.coe_mul, hAT, Matrix.SpecialLinearGroup.coe_mul]
    rw [hP1]
    exact ((hm.sub_left (Commute.one_left _)).pow_left o).eq
  ·
    have hc : ∀ g, θ' g = As * invTransposeSL M g * As⁻¹ := by
      intro g
      apply Subtype.ext
      rw [hA g, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hAinv]
      rfl
    refine exists_overlap_chart_aux ψ hψ x θ' hθ' As (invTransposeSL M) (invTransposeSL (M + 2))
      hc (fun z => invTransposeSL_blockSL _ z) (fun _ _ hu => invTransposeSL_mem_coordBlockSL hu) ?_
    intro J' T o hP1 hP2 hθT
    have hY : (T * As)⁻¹ * (As * invTransposeSL M T) ∈ Subgroup.center SL(M, ZMod 2) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨v, rfl⟩ := (invTransposeSL M).surjective w
      have h1 := hθT v
      rw [hc, hc, map_mul, map_mul, map_inv] at h1
      calc invTransposeSL M v * ((T * As)⁻¹ * (As * invTransposeSL M T))
          = (T * As)⁻¹ * (T * (As * invTransposeSL M v * As⁻¹) * T⁻¹) *
              (As * invTransposeSL M T) := by group
        _ = (T * As)⁻¹ * (As * (invTransposeSL M T * invTransposeSL M v *
              (invTransposeSL M T)⁻¹) * As⁻¹) * (As * invTransposeSL M T) := by rw [h1]
        _ = (T * As)⁻¹ * (As * invTransposeSL M T) * invTransposeSL M v := by group
    have hAT : T * As = As * invTransposeSL M T :=
      inv_mul_eq_one.mp (eq_one_of_mem_center_SL_two (by omega) hY)
    have key : SemiconjBy (As : Matrix (Fin M) (Fin M) (ZMod 2))
        ((invTransposeSL M T : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2))
        (T : Matrix (Fin M) (Fin M) (ZMod 2)) := by
      show (As : Matrix (Fin M) (Fin M) (ZMod 2)) * _ = _ * _
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hAT]
    have hs : (((invTransposeSL M T : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o =
        compIndicator (ZMod 2) J' := by
      rw [coe_invTransposeSL, ← transpose_one, ← transpose_sub, ← transpose_pow, ← hP2,
        compIndicator, diagonal_transpose]
    have key2 := (key.sub_right (SemiconjBy.one_right _)).pow_right o
    rw [hs, ← hP1] at key2
    exact key2.eq.symm

end Overlap

end CFSG.StandardType.FF81

end
