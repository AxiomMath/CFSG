module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CE
public import CFSG.Quasithin.Vol2.Ch3E213MP6CB

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ mem_antiSp uElt)

variable {k : Type} [Field k]

theorem natAct_add (g : antiSp k) (u v : Fin 4 → k) :
    natAct g (u + v) = natAct g u + natAct g v :=
  Matrix.mulVec_add _ _ _

theorem natAct_smul (g : antiSp k) (r : k) (v : Fin 4 → k) :
    natAct g (r • v) = r • natAct g v :=
  Matrix.mulVec_smul _ _ _

theorem natAct_sub (g : antiSp k) (u v : Fin 4 → k) :
    natAct g (u - v) = natAct g u - natAct g v :=
  Matrix.mulVec_sub _ _ _

theorem natAct_single_apply (g : antiSp k) (i j : Fin 4) :
    natAct g (Pi.single j 1) i = glMat (g : GL (Fin 4) k) i j := by
  simp [natAct]

theorem spBil_natAct (g : antiSp k) (x y : Fin 4 → k) :
    spBil (natAct g x) (natAct g y) = spBil x y := by
  have hJ : (glMat (g : GL (Fin 4) k)).transpose * minorJ k * glMat (g : GL (Fin 4) k) =
      minorJ k := mem_antiSp.mp g.2
  simp only [spBil, natAct, Matrix.toBilin'_apply']
  rw [← Matrix.vecMul_transpose _ x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hJ]

theorem natAct_subAntiSp (F₀ : Subfield k) (g : antiSp ↥F₀) (v : Fin 4 → ↥F₀) :
    natAct (subAntiSp F₀ g) (fun i => (v i : k)) =
      fun i => ((natAct (k := ↥F₀) g v i : ↥F₀) : k) := by
  ext i
  simp [natAct, glMat_subAntiSp, Matrix.mulVec, dotProduct]

theorem spBil_coe (F₀ : Subfield k) (x y : Fin 4 → ↥F₀) :
    ((spBil x y : ↥F₀) : k) = spBil (fun i => (x i : k)) (fun i => (y i : k)) := by
  rw [spBil_apply, spBil_apply]
  simp

theorem map_conj_eq_of_mem {X : Subgroup (antiSp k)} {z : antiSp k} (hz : z ∈ X) :
    X.map (MulAut.conj z).toMonoidHom = X := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact X.mul_mem (X.mul_mem hz hx) (X.inv_mem hz)
  · intro hg
    refine ⟨z⁻¹ * g * z, X.mul_mem (X.mul_mem (X.inv_mem hz) hg) hz, ?_⟩
    change z * (z⁻¹ * g * z) * z⁻¹ = g
    group

theorem exists_three_ne_zero (c : antiSp k) : ∃ j, glMat (c : GL (Fin 4) k) 3 j ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : glMat (c : GL (Fin 4) k) * glMat ((c⁻¹ : antiSp k) : GL (Fin 4) k) = 1 :=
    (c : GL (Fin 4) k).mul_inv
  have h2 := congrFun (congrFun h1 3) 3
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h2
  simp [hc] at h2

section CharTwo

variable [CharP k 2]

omit [CharP k 2] in
theorem coe_single (F₀ : Subfield k) (j : Fin 4) :
    (fun i => ((Pi.single j 1 : Fin 4 → ↥F₀) i : k)) = Pi.single j 1 := by
  ext i
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem exists_isUpper_conj {F₀ : Subfield k} {c : antiSp k} {a b : k} (ha : a ≠ 0)
    (hb : b ≠ 0) (hl : uElt 0 0 a 0 ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom)
    (hs : uElt 0 b 0 0 ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom) :
    ∃ c' : antiSp k, IsUpper c' ∧ (subfieldSp F₀).map (MulAut.conj c').toMonoidHom =
      (subfieldSp F₀).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨x, hx, hxe⟩ := hl
  obtain ⟨y, hy, hye⟩ := hs
  change c * x * c⁻¹ = uElt 0 0 a 0 at hxe
  change c * y * c⁻¹ = uElt 0 b 0 0 at hye
  obtain ⟨j, hj⟩ := exists_three_ne_zero c
  set u := natAct c (Pi.single j 1) with hu
  have hu3 : u 3 ≠ 0 := by rw [hu, natAct_single_apply]; exact hj
  set w := natAct x (Pi.single j 1) - Pi.single j 1 with hw
  set w' := natAct y (Pi.single j 1) - Pi.single j 1 with hw'
  have hcx : c * x = uElt 0 0 a 0 * c := by rw [← hxe]; group
  have hcy : c * y = uElt 0 b 0 0 * c := by rw [← hye]; group
  have hcw : natAct c w = (a * u 3) • Pi.single 0 1 := by
    rw [hw, natAct_sub, ← natAct_mul, hcx, natAct_mul, natAct_zl, ← hu, add_sub_cancel_left]
  have hcw' : natAct c w' = (b * u 2) • Pi.single 0 1 + (b * u 3) • Pi.single 1 1 := by
    rw [hw', natAct_sub, ← natAct_mul, hcy, natAct_mul, natAct_zs, ← hu, add_assoc,
      add_sub_cancel_left]
  have hsF : ∀ i, (Pi.single j 1 : Fin 4 → k) i ∈ F₀ := fun i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [F₀.one_mem, F₀.zero_mem]
  have hwF : ∀ i, w i ∈ F₀ := fun i => by
    rw [hw, Pi.sub_apply, natAct_single_apply]
    exact F₀.sub_mem (hx i j) (hsF i)
  have hwF' : ∀ i, w' i ∈ F₀ := fun i => by
    rw [hw', Pi.sub_apply, natAct_single_apply]
    exact F₀.sub_mem (hy i j) (hsF i)
  set w₀ : Fin 4 → ↥F₀ := fun i => ⟨w i, hwF i⟩ with hw₀
  set w₀' : Fin 4 → ↥F₀ := fun i => ⟨w' i, hwF' i⟩ with hw₀'
  have hli : LinearIndependent ↥F₀ ![w₀, w₀'] := by
    rw [LinearIndependent.pair_iff]
    intro p q hpq
    have hk : (p : k) • w + (q : k) • w' = 0 := by
      ext i
      have h1 := congrArg Subtype.val (congrFun hpq i)
      simpa [hw₀, hw₀'] using h1
    have hc := congrArg (natAct c) hk
    rw [natAct_add, natAct_smul, natAct_smul, hcw, hcw',
      show natAct c 0 = 0 from Matrix.mulVec_zero _] at hc
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    have e1' : (q : k) * (b * u 3) = 0 := by simpa [Pi.single_apply] using e1
    have hq : (q : k) = 0 := (mul_eq_zero.1 e1').resolve_right (mul_ne_zero hb hu3)
    have e0' : (p : k) * (a * u 3) = 0 := by simpa [Pi.single_apply, hq] using e0
    have hp : (p : k) = 0 := (mul_eq_zero.1 e0').resolve_right (mul_ne_zero ha hu3)
    exact ⟨Subtype.ext hp, Subtype.ext hq⟩
  have hww : spBil w₀ w₀' = 0 := by
    apply Subtype.val_injective
    rw [spBil_coe]
    change spBil w w' = 0
    rw [← spBil_natAct c, hcw, hcw', spBil_apply]
    simp
  obtain ⟨z₀, hz0, hz1⟩ := exists_antiSp_flag hli hww
  have hzmem : subAntiSp F₀ z₀ ∈ subfieldSp F₀ := range_subAntiSp F₀ ▸ ⟨z₀, rfl⟩
  have hze : ∀ i : Fin 4, natAct (subAntiSp F₀ z₀) (Pi.single i 1) =
      fun m => ((natAct (k := ↥F₀) z₀ (Pi.single i 1) m : ↥F₀) : k) := fun i => by
    rw [← natAct_subAntiSp, coe_single]
  have hze0 : natAct (subAntiSp F₀ z₀) (Pi.single 0 1) = w := by
    rw [hze, hz0]
  have hze1 : natAct (subAntiSp F₀ z₀) (Pi.single 1 1) = w' := by
    rw [hze, hz1]
  have hcol : ∀ (i m : Fin 4), glMat ((c * subAntiSp F₀ z₀ : antiSp k) : GL (Fin 4) k) i m =
      natAct c (natAct (subAntiSp F₀ z₀) (Pi.single m 1)) i := fun i m => by
    rw [← natAct_single_apply, natAct_mul]
  refine ⟨c * subAntiSp F₀ z₀, ?_, ?_⟩
  · refine isUpper_of_flag ?_ ?_ ?_ ?_ ?_ <;>
      (rw [hcol]; simp [hze0, hze1, hcw, hcw'])
  · have hcomp : (MulAut.conj (c * subAntiSp F₀ z₀)).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj (subAntiSp F₀ z₀)).toMonoidHom := by
      ext g
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
        Function.comp_apply]
      group
    rw [hcomp, ← Subgroup.map_map, map_conj_eq_of_mem hzmem]

end CharTwo

end CFSG.Quasithin.Ch3E213M
