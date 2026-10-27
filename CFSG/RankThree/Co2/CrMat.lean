module

public import CFSG.RankThree.Co2.Classes
public import CFSG.RankThree.Co2.CrConj
public import CFSG.Certificates.Kernel.Co2Syl.Words
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CFSG.RankThree.Co2.ClassesCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Co2Inv CFSG.KC.Co2Syl

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

@[expose] def endMat (f : Module.End (ZMod 2) (Wv v0)) : M22 :=
  (LinearMap.toMatrix qbWBasis qbWBasis f).transpose

theorem endMat_mul (f g : Module.End (ZMod 2) (Wv v0)) : endMat (f * g) = endMat g * endMat f := by
  unfold endMat
  rw [LinearMap.toMatrix_mul, Matrix.transpose_mul]

theorem endMat_one : endMat 1 = 1 := by
  unfold endMat
  rw [LinearMap.toMatrix_one, Matrix.transpose_one]

theorem endMat_injective : Function.Injective endMat := fun f g h =>
  (LinearMap.toMatrix qbWBasis qbWBasis).injective (Matrix.transpose_injective h)

theorem endMat_rowsEnd (R : Array ℕ) : endMat (rowsEnd R) = rowsMat R := by
  ext t j
  change LinearMap.toMatrix qbWBasis qbWBasis (rowsEnd R) j t = rowsMat R t j
  rw [LinearMap.toMatrix_apply, qbWBasis_apply, rowsEnd_qbW, decW_eq_equivFun,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, rowsMat_apply, Code.bvec_apply, bitZ]

@[expose] def crMat : Cr →* M22 where
  toFun x := endMat (wAct v0 (x : Kstab v0))
  map_one' := by
    change endMat (wAct v0 1) = 1
    rw [wAct_one, endMat_one]
  map_mul' x y := by
    change endMat (wAct v0 ((x : Kstab v0) * (y : Kstab v0))) =
      endMat (wAct v0 (x : Kstab v0)) * endMat (wAct v0 (y : Kstab v0))
    rw [wAct_mul, endMat_mul]

theorem crMat_eq_of_hasRows {x : Cr} {R : Array ℕ} (h : HasRows (x : Kstab v0) R) : crMat x = rowsMat R := by
  change endMat (wAct v0 (x : Kstab v0)) = rowsMat R
  rw [h, endMat_rowsEnd]

theorem crMat_injective : Function.Injective (crMat : Cr → M22) :=
  fun _ _ h => Subtype.ext (eq_of_wAct_eq (endMat_injective h))

theorem crMat_wordCr {w : List ℕ} (hw : ∀ l ∈ w, l < 42) : crMat (wordCr w) = wordMat w :=
  crMat_eq_of_hasRows (hasRows_wordCr hw)

theorem crMat_rep {i : ℕ} (hi : i < 10) : crMat (rep i) = repMat i :=
  crMat_eq_of_hasRows (hasRows_rep hi)

theorem Cm_le_mrange : Cm ≤ MonoidHom.mrange (crMat : Cr →* M22) := by
  have hl : ∀ k : Fin letters21.size, ∀ l ∈ letters21[k], l < 42 := by decide
  unfold Cm matGrp
  rw [Submonoid.closure_le]
  rintro _ ⟨k, rfl⟩
  exact ⟨wordCr letters21[k], crMat_wordCr (hl k)⟩

theorem matGrp_le_map {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) :
    matGrp ws ≤ (subW ws).toSubmonoid.map crMat := by
  unfold matGrp
  rw [Submonoid.closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  refine ⟨gensW ws k, gensW_mem_subW hk, ?_⟩
  change crMat (wordCr ws[k]!) = wordMat ws[k]
  rw [crMat_wordCr (hws k hk), getElem!_pos ws k hk]

theorem card_map_subW (ws : Array (List ℕ)) :
    Nat.card ((subW ws).toSubmonoid.map crMat) = Nat.card (subW ws) :=
  (Nat.card_congr (Submonoid.equivMapOfInjective _ crMat crMat_injective).toEquiv).symm

theorem card_matGrp_le {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) :
    Nat.card (matGrp ws) ≤ Nat.card (subW ws) := by
  rw [← card_map_subW]
  exact Nat.card_mono (Set.toFinite _) (matGrp_le_map hws)

theorem matGrp_eq_map {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42)
    (hc : Nat.card (subW ws) ≤ Nat.card (matGrp ws)) :
    matGrp ws = (subW ws).toSubmonoid.map crMat := by
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_ncard_le (matGrp_le_map hws) _ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card ((subW ws).toSubmonoid.map crMat) ≤ Nat.card (matGrp ws)
  rw [card_map_subW]
  exact hc

theorem map_subW_le {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) :
    (subW ws).toSubmonoid.map crMat ≤ matGrp ws := by
  let S : Subgroup Cr :=
    { Submonoid.comap crMat (matGrp ws) with
      inv_mem' := fun {a} ha => by
        have hn : orderOf a ≠ 0 := (orderOf_pos a).ne'
        have e : a ^ (orderOf a - 1) = a⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hn, pow_orderOf_eq_one])
        change crMat a⁻¹ ∈ matGrp ws
        rw [← e, map_pow]
        exact Submonoid.pow_mem (matGrp ws) ha _ }
  have hle : subW ws ≤ S := by
    rw [subW, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    change crMat (wordCr ws[k]!) ∈ matGrp ws
    rw [crMat_wordCr (hws k hk), getElem!_pos ws k hk]
    exact Submonoid.subset_closure ⟨⟨k, hk⟩, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hle hy

end CFSG.RankThree.Co2

end
