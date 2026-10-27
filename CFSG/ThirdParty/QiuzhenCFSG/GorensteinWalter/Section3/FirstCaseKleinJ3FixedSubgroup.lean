module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinJ3CentralizerOdd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCardThreeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvertedInfVU
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The odd centralizer in the `J₃` argument has a nontrivial fixed part
under the outside involution.  If it were fixed-point-free, Fact 1.5(ii)
would invert both commuting order-three factors and produce nine inverted
elements. -/

public theorem firstCase_klein_J3_centralizer_fixed_nontrivial
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
    let A := Subgroup.centralizer (X : Set G)
    A ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥ := by
  classical
  dsimp
  let A : Subgroup G := Subgroup.centralizer (X : Set G)
  have hy : IsInvolution y := by simpa [firstCaseJ] using hyJ |>.1
  have hyH : y ∉ c.Hhat := by simpa [firstCaseJ] using hyJ |>.2.1
  have hUcard : Nat.card c.U = 3 :=
    firstCase_klein_U_card_three_pre_b3 hmin c hfirst hklein
  have hAodd : Nat.Coprime 2 (Nat.card A) := by
    simpa [A] using (firstCase_klein_J3_centralizer_odd hmin c hfirst hklein
      hyJ hXne hXle hXcard hXinv hXinf)
  have hXcentU : X ≤ Subgroup.centralizer (c.U : Set G) :=
    firstCase_klein_card_three_subgroup_centralizes_U hmin c hXcard hXle hUcard
  have hUleA : c.U ≤ A := by
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mpr (fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hXcentU hx) u hu).symm))
  have hUleHhat : c.U ≤ c.Hhat := by
    rw [(theorem_2_6 hmin c).1]
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hyNormX : y ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [(hXinv x hx).2]
      exact X.inv_mem hx
    · intro hx
      have hx' := hXinv (y * x * y⁻¹) hx
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have hback : y * (y * x * y⁻¹) * y⁻¹ = x := by
        rw [hyinv]
        calc
          y * (y * x * y) * y = (y * y) * x * (y * y) := by group
          _ = x := by rw [hy2]; simp
      rw [← hback, hx'.2]
      exact X.inv_mem hx
  have hyNormA : y ∈ Subgroup.normalizer (A : Set G) := by
    have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hconjconj : ∀ b : G, y * (y * b * y⁻¹) * y⁻¹ = b := by
      intro b
      rw [hyinv]
      calc
        y * (y * b * y) * y = (y * y) * b * (y * y) := by group
        _ = b := by rw [hy2]; simp
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : y⁻¹ * x * y ∈ X := by
        have h := (Subgroup.mem_normalizer_iff.mp hyNormX) x
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
        simpa [hyinv] using h.mp hx
      have ha' := (Subgroup.mem_centralizer_iff.mp ha) (y⁻¹ * x * y) hx'
      calc
        x * (y * a * y⁻¹) = y * ((y⁻¹ * x * y) * a) * y⁻¹ := by group
        _ = y * (a * (y⁻¹ * x * y)) * y⁻¹ := by rw [ha']
        _ = (y * a * y⁻¹) * x := by group
    · intro ha
      have hback : y * (y * a * y⁻¹) * y⁻¹ = a := by
        exact hconjconj a
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : y * x * y⁻¹ ∈ X := by
        exact (Subgroup.mem_normalizer_iff.mp hyNormX x).mp hx
      have ha' := (Subgroup.mem_centralizer_iff.mp ha) (y * x * y⁻¹) hx'
      calc
        x * a = (y * (y * x * y⁻¹) * y⁻¹) *
            (y * (y * a * y⁻¹) * y⁻¹) := by
              rw [hconjconj x, hconjconj a]
        _ = y * ((y * x * y⁻¹) * (y * a * y⁻¹)) * y⁻¹ := by group
        _ = y * ((y * a * y⁻¹) * (y * x * y⁻¹)) * y⁻¹ := by rw [ha']
        _ = (y * (y * a * y⁻¹) * y⁻¹) *
            (y * (y * x * y⁻¹) * y⁻¹) := by group
        _ = a * x := by
          rw [hconjconj a, hconjconj x]
  intro hbot
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by rw [hUcard]; norm_num
  have hnotInvU : ¬ (∀ u : G, u ∈ c.U → y * u * y⁻¹ = u⁻¹) := by
    intro hUinv
    have hUXdisj : Disjoint c.U X := by
      apply (disjoint_iff_inf_le).2
      intro z hz
      have hbot' : z ∈ X ⊓ (twoCoreOf c.Hhat ⊔ c.U) :=
        ⟨hz.2, (le_sup_right : c.U ≤ twoCoreOf c.Hhat ⊔ c.U) hz.1⟩
      rw [hXinf] at hbot'
      exact hbot'
    have hUcentX : c.U ≤ Subgroup.centralizer (X : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hXcentU hx) u hu).symm
    have hUnormX : c.U ≤ Subgroup.normalizer (X : Set G) :=
      hUcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
    have hUXcard : Nat.card (c.U ⊔ X : Subgroup G) = 9 := by
      rw [sup_comm]
      rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) X c.U
        hUnormX hUXdisj.symm, hXcard, hUcard]
    have hUXinv : ∀ z : G, z ∈ c.U ⊔ X →
        z ∈ invertedElements c.Hhat y := by
      intro z hz
      let K : Subgroup G := c.U ⊔ X
      have hUK : c.U ≤ K := le_sup_left
      have hXK : X ≤ K := le_sup_right
      have hsupK : c.U.subgroupOf K ⊔ X.subgroupOf K = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hUK hXK]
        simp [K]
      let : (X.subgroupOf K).Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := c.U) (N := X) hUnormX
      have hzK : (⟨z, hz⟩ : K) ∈ c.U.subgroupOf K ⊔ X.subgroupOf K := by
        rw [hsupK]
        trivial
      rcases Subgroup.mem_sup_of_normal_right.mp hzK with ⟨u, hu, x, hx, hzx⟩
      have huU : (u : G) ∈ c.U := Subgroup.mem_subgroupOf.mp hu
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hzxG : (u : G) * (x : G) = z := congrArg (fun q : K => (q : G)) hzx
      rw [← hzxG]
      refine ⟨c.Hhat.mul_mem (hUleHhat huU) (hXle hxX), ?_⟩
      have huInv := hUinv (u : G) huU
      have hxInv := (hXinv (x : G) hxX).2
      calc
        y * ((u : G) * (x : G)) * y⁻¹ = (y * (u : G) * y⁻¹) *
            (y * (x : G) * y⁻¹) := by group
        _ = (u : G)⁻¹ * (x : G)⁻¹ := by rw [huInv, hxInv]
        _ = ((u : G) * (x : G))⁻¹ := by
          have hcomm : (u : G) * (x : G) = (x : G) * (u : G) :=
            (Subgroup.mem_centralizer_iff.mp (hXcentU hxX) (u : G) huU)
          rw [mul_inv_rev]
          simpa only [mul_inv_rev] using
            (congrArg (fun q : G => q⁻¹) hcomm).symm
    have hIcard : Nat.card {z : G // z ∈ invertedElements c.Hhat y} = 3 := by
      rw [← firstCase_klein_coset_involution_card_eq c hy hyH]
      simpa [firstCaseJ] using hyJ |>.2.2
    let f : (c.U ⊔ X : Subgroup G) →
        {z : G // z ∈ invertedElements c.Hhat y} := fun z =>
      ⟨z, hUXinv z z.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hval : (f a : G) = (f b : G) :=
        congrArg (fun q : {z : G // z ∈ invertedElements c.Hhat y} => (q : G)) hab
      simpa [f] using hval
    have hle := Nat.card_le_card_of_injective f hf
    rw [hUXcard, hIcard] at hle
    omega
  have hUinvAll : ∀ u : G, u ∈ c.U → y * u * y⁻¹ = u⁻¹ := by
    intro u hu
    obtain ⟨z, hzC, i, hiI, huzi⟩ :=
      fact_1_5_ii_decomposition (X := A) hy hAodd
        (fun a ha => (Subgroup.mem_normalizer_iff.mp hyNormA) a |>.mp ha)
        u (hUleA hu)
    have hzbot : z = 1 := by
      have hzA : z ∈ A := hzC.1
      have hzY : z ∈ Subgroup.centralizer ({y} : Set G) := by
        exact hzC.2
      have hzBoth : z ∈ A ⊓ Subgroup.centralizer ({y} : Set G) := ⟨hzA, hzY⟩
      rw [hbot] at hzBoth
      exact Subgroup.mem_bot.mp hzBoth
    rw [huzi, hzbot]
    simpa using hiI.2
  exact hnotInvU hUinvAll

end CFSG.GorensteinWalter
