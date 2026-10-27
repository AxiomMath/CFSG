module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinJ3ExtraInvolution
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! The centralizer of the order-three subgroup inverted by a `J₃`
involution has odd order. -/

public theorem firstCase_klein_J3_centralizer_odd
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hyJ : y ∈ firstCaseJ c 3)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXcard : Nat.card X = 3)
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hXinf : X ⊓ (twoCoreOf c.Hhat ⊔ c.U) = ⊥) :
    Odd (Nat.card (Subgroup.centralizer (X : Set G))) := by
  classical
  apply Nat.not_even_iff_odd.mp
  intro hC_even
  obtain ⟨e, heH, heI, hey⟩ :=
    firstCase_klein_J3_extra_commuting_involution_of_centralizer_even
      hmin c hfirst hklein hyJ hXne hXle hXcard hXinv hXinf hC_even
  have hy : IsInvolution y := by simpa [firstCaseJ] using hyJ |>.1
  have hyH : y ∉ c.Hhat := by simpa [firstCaseJ] using hyJ |>.2.1
  have he2 : e * e = 1 := by simpa [pow_two] using heI.2
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have heInv : e ∈ invertedElements c.Hhat y := by
    refine ⟨heH, ?_⟩
    calc
      y * e * y⁻¹ = e * y * y⁻¹ := by rw [hey.eq.symm]
      _ = e := by simp
      _ = e⁻¹ := heinv.symm
  have hIcard : Nat.card {z : G // z ∈ invertedElements c.Hhat y} = 3 := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH]
    simpa [firstCaseJ] using hyJ |>.2.2
  let I : Type u := {z : G // z ∈ invertedElements c.Hhat y}
  let f : X → I := fun z => ⟨z, hXinv z z.2⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    exact congrArg (fun q : I => (q : G)) hzw
  have hfbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).2 ⟨hf, by
      change Nat.card X = Nat.card {z : G // z ∈ invertedElements c.Hhat y}
      rw [hXcard, hIcard]⟩
  obtain ⟨eX, heXeq⟩ := hfbij.2 (⟨e, heInv⟩ : I)
  have heX : e ∈ X := by
    have heq : (eX : G) = e := congrArg (fun q : I => (q : G)) heXeq
    simpa [heq] using eX.2
  have hdvd : orderOf e ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X heX
  have heord : orderOf e = 2 := orderOf_eq_prime heI.2 heI.1
  rw [heord, hXcard] at hdvd
  norm_num at hdvd

end CFSG.GorensteinWalter
