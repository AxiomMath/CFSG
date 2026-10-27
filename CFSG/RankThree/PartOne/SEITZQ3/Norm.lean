module

public import CFSG.RankThree.PartOne.SEITZQ1.Norm
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ3

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.SEITZQ1
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L]

theorem q3_conj_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) {ω : L}
    (E : Subgroup (ReeTag.F4.reeGamma K a))
    (hT : ∀ x ∈ E, (q1C ω)⁻¹ * thetaGamma L a x * q1C ω ∈ torusGroup ReeTag.F4.tag L)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 3 ^ 2) (g : ReeTag.F4.reeGamma K a)
    (hg : thetaGamma L a g =
      q1C ω * canonicalRep (coxeterSystem ReeTag.F4.tag) L q1V * (q1C ω)⁻¹) :
    ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  let T : Subgroup (ReeTag.F4.reeGamma K a) :=
    (torusGroup ReeTag.F4.tag L).comap
      ((MulAut.conj (q1C ω)⁻¹).toMonoidHom.comp (thetaGamma L a))
  have hmemT : ∀ y, y ∈ T ↔
      (q1C ω)⁻¹ * thetaGamma L a y * q1C ω ∈ torusGroup ReeTag.F4.tag L := fun y => by
    simp only [T, Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  have hcomm : ∀ x y : ReeTag.F4.reeGamma K a, x ∈ T → y ∈ T → x * y = y * x := fun x y hx hy =>
    q1_mul_comm_of_mem_torus (q1C ω) ((hmemT x).1 hx) ((hmemT y).1 hy)
  let W : Subgroup (ReeTag.F4.reeGamma K a) :=
    { carrier := {y | y ∈ T ∧ y ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
        have hc : Commute x y := hcomm x y hx.1 hy.1
        rw [hc.mul_pow, hx.2, hy.2, one_mul]
      one_mem' := ⟨T.one_mem, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨T.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hWab : CFSG.Assembly.IsElemAbelian 3 W :=
    ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (hcomm x y x.2.1 y.2.1), fun x hx => hx.2⟩
  have hW9 : Nat.card W ≤ 9 :=
    CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK W hWab
  have hEW : E ≤ W := fun x hx => ⟨(hmemT x).2 (hT x hx), hexp x hx⟩
  have hEeq : E = W := Subgroup.eq_of_le_of_card_ge hEW (by rw [hcard]; exact hW9)
  intro x hx
  rw [hEeq]
  exact ⟨(hmemT _).2 (q1_conj_mem_torus hg (hT x hx)), by
    rw [conj_pow, hexp x hx, mul_one, mul_inv_cancel]⟩

end CFSG.RankThree.PartOne.SEITZQ3
