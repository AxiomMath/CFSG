module

public import CFSG.RankThree.PartTwo.CTU6.Long
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Basic

public section

namespace CFSG.RankThree.PartTwo.CTU6

open Matrix CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg (fixedSubfield mem_fixedSubfield hypMat card_fixedSubfield)
open CFSG.ClassicalInvolution.WeakCT (torusHom coe_torusHom diagConj2 coe_diagConj2)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2Model)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)

@[expose] noncomputable def su4Nu (t : Kˣ) : (fixedSubfield K 2 f)ˣ :=
  Units.mk0 ⟨((t : K) * unitaryInvolution K 2 f t)⁻¹, by
    rw [mem_fixedSubfield, map_inv₀, map_mul, unitaryInvolution_involutive hK, mul_comm]⟩
    (fun h => by
      have h' : ((t : K) * unitaryInvolution K 2 f t)⁻¹ = 0 := congrArg Subtype.val h
      have ht : (t : K) ≠ 0 := t.ne_zero
      have ht' : unitaryInvolution K 2 f (t : K) ≠ 0 := fun h0 =>
        ht ((map_eq_zero (unitaryInvolution K 2 f)).1 h0)
      exact (inv_ne_zero (mul_ne_zero ht ht')) h')

@[expose] noncomputable def su4Mu (s : (fixedSubfield K 2 f)ˣ) : Kˣ :=
  Units.map (fixedSubfield K 2 f).subtype.toMonoidHom s⁻¹

theorem coe_su4Nu (t : Kˣ) :
    (((su4Nu hK t : (fixedSubfield K 2 f)ˣ) : fixedSubfield K 2 f) : K) =
      ((t : K) * unitaryInvolution K 2 f t)⁻¹ :=
  rfl

theorem coe_su4Mu (s : (fixedSubfield K 2 f)ˣ) :
    ((su4Mu s : Kˣ) : K) = ((((s : fixedSubfield K 2 f) : K))⁻¹) := by
  simp [su4Mu, Units.val_inv_eq_inv_val]

theorem sbEmb_torus_conj_lbSU4 (t : Kˣ) (A : SL(2, fixedSubfield K 2 f)) :
    sbEmb _ (unitaryInvolution_involutive hK) (torusHom K t) * lbSU4 K f A *
        (sbEmb _ (unitaryInvolution_involutive hK) (torusHom K t))⁻¹ =
      lbSU4 K f (diagConj2 (su4Nu hK t) 1 A) := by
  rw [← map_inv, ← map_inv]
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_lbSU4, coe_lbSU4]
  change sbMat _ ((torusHom K t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * _ *
    sbMat _ ((torusHom K t⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
  have ht : (t : K) ≠ 0 := t.ne_zero
  have ht' : unitaryInvolution K 2 f (t : K) ≠ 0 := fun h0 =>
    ht ((map_eq_zero (unitaryInvolution K 2 f)).1 h0)
  rw [coe_torusHom, coe_torusHom, coe_diagConj2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sbMat, embMid, hypMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
      Units.val_inv_eq_inv_val, coe_su4Nu] <;> field_simp

theorem lbSU4_torus_conj_sbEmb (s : (fixedSubfield K 2 f)ˣ) (B : SL(2, K)) :
    lbSU4 K f (torusHom (fixedSubfield K 2 f) s) * sbEmb _ (unitaryInvolution_involutive hK) B *
        (lbSU4 K f (torusHom (fixedSubfield K 2 f) s))⁻¹ =
      sbEmb _ (unitaryInvolution_involutive hK) (diagConj2 (su4Mu s) 1 B) := by
  rw [← map_inv, ← map_inv]
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_lbSU4, coe_lbSU4]
  change _ * sbMat _ ((B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * _ =
    sbMat _ ((diagConj2 (su4Mu s) 1 B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  have hs : ((s : fixedSubfield K 2 f) : K) ≠ 0 := fun h0 =>
    s.ne_zero (Subtype.ext h0)
  have hsσ : unitaryInvolution K 2 f ((s : fixedSubfield K 2 f) : K) =
      ((s : fixedSubfield K 2 f) : K) := (s : fixedSubfield K 2 f).2
  have hsσ' : iterateFrobenius K 2 f ((s : fixedSubfield K 2 f) : K) =
      ((s : fixedSubfield K 2 f) : K) := by
    rw [← iterateFrobeniusEquiv_apply]
    exact hsσ
  rw [coe_torusHom, coe_torusHom, coe_diagConj2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sbMat, embMid, hypMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
      Units.val_inv_eq_inv_val, coe_su4Mu, hsσ'] <;>
    field_simp

@[expose] noncomputable def su4Model :
    TwistedB2Model (fixedSubfield K 2 f) K (SU (unitaryInvolution K 2 f) 4) where
  lb := lbSU4 K f
  sb := sbEmb _ (unitaryInvolution_involutive hK)
  nu := su4Nu hK
  mu := su4Mu
  conj_sl := sbEmb_torus_conj_lbSU4 hK
  conj_ls := lbSU4_torus_conj_sbEmb hK

theorem exists_su4Mu_ne (hf : 2 ≤ f) : ∃ s, (su4Model hK).mu s ≠ 1 := by
  have hq : 3 ≤ Nat.card (fixedSubfield K 2 f) := by
    rw [card_fixedSubfield hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.WeakCT.exists_unit_ne_one hq
  refine ⟨s, fun h => hs ?_⟩
  have h1 : su4Mu s = 1 := h
  have h2 : ((s : fixedSubfield K 2 f) : K)⁻¹ = 1 := by
    rw [← coe_su4Mu, h1, Units.val_one]
  exact Units.ext (Subtype.ext (by rw [inv_eq_one.mp h2]; rfl))

end CFSG.RankThree.PartTwo.CTU6
