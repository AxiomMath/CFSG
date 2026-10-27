module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTS
public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5_V_le : Vh hK ≤ Uh hK := Vh_le_Sh.trans Sh_le_Uh

theorem un5_V_ab {a b : MulAut (hypPSU hK 2 1)} (ha : a ∈ Vh hK) (hb : b ∈ Vh hK) :
    a * b = b * a := Vh_comm ha hb

theorem un5_V_sq {a : MulAut (hypPSU hK 2 1)} (ha : a ∈ Vh hK) : a ^ 2 = 1 := by
  rw [sq]
  exact Vh_sq ha

theorem un5_V_zt : innM hK (z₁SU hK) ∈ Vh hK ∧ innM hK (z₂SU hK) ∈ Vh hK :=
  ⟨⟨z₁SU hK, ZPsub_le_Vsub z₁SU_mem_ZPsub, rfl⟩, ⟨z₂SU hK, Z₂Psub_le_Vsub z₂SU_mem_Z₂Psub, rfl⟩⟩

theorem un5_V_unique (hf : 2 ≤ f) {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ)
    (E : Subgroup (MulAut (hypPSU hK 2 1))) (hE : E ≤ T) (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) (hcard : Nat.card E = Nat.card (Vh hK)) : E = Vh hK := by
  have hZ := u5_center_eq_bot hK
  have hq : 3 ≤ 2 ^ f := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsq' : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := hsq x hx
    rwa [sq] at this
  have h1 := elemAb_T hZ hq (un5t_inf_Pi hK hU hT) hE hab hsq'
  exact h1.2 (hcard.trans (card_Vh hZ))

end CFSG.Quasithin.H13.F431.Un.OL5
