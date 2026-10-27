module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPConjCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaFixedPart
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The elementary order-`p²` subgroup in `F ⊔ K₀`

The aligned equation-(11) argument only needs uniqueness for the elementary
abelian subgroup obtained by conjugating `A`.  This is the correct source
interface: an arbitrary subgroup of order `p²` in a product of cyclic groups
need not be elementary when one cyclic factor has order divisible by `p²`.
The p-torsion of the two cyclic factors is nevertheless unique, and their
product is `A`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The elementary abelian subgroup of order `p²` inside `F ⊔ K₀` is the
chosen subgroup `A = P ⊔ P₀`. -/
public theorem secondCase_linear_A_unique_elementary
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    ∀ B : Subgroup G, B ≤ od.F ⊔ od.K0 →
      IsElementaryAbelian od.p B → Nat.card B = od.p ^ 2 → B = od.A := by
  classical
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  let : IsCyclic od.K := od.K_cyclic
  have hK0leE : od.K0 ≤ d.E := by
    rw [od.K0_eq]
    exact inf_le_right.trans od.K_le_E
  have hF0 : od.F ⊓ od.K0 = ⊥ :=
    secondCase_linear_omega_F_cap_K0 c w d od
  have hK0cyc : IsCyclic od.K0 := by
    rw [od.K0_eq]
    exact Subgroup.isCyclic_of_le inf_le_right
  have hP0order : {x : G | x ∈ od.K0 ∧ x ^ od.p = 1} = (od.P0 : Set G) := by
    have hpK0 : od.p ∣ Nat.card od.K0 := by
      simpa [od.P0_card] using (Subgroup.card_dvd_of_le od.P0_le_K0)
    obtain ⟨H0, hH0, hH0uniq⟩ :=
      secondCase_unique_order_p_subgroup_of_cyclic
        (G := G) (T := od.K0) hK0cyc (k := Nat.card od.K0)
        (p := od.p) rfl hpK0
    have hH0eq : H0 = od.P0 :=
      (hH0uniq od.P0 ⟨od.P0_le_K0, od.P0_card⟩).symm
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact od.P0.one_mem
      · have hdiv : orderOf x ∣ od.p :=
          (orderOf_dvd_iff_pow_eq_one (x := x) (n := od.p)).mpr hx.2
        have horder : orderOf x = od.p :=
          (Nat.dvd_prime od.hp_prime).mp hdiv |>.resolve_left
            (fun h => hx1 (orderOf_eq_one_iff.mp h))
        let H : Subgroup G := Subgroup.zpowers x
        have hHle : H ≤ od.K0 := Subgroup.zpowers_le.mpr hx.1
        have hHcard : Nat.card H = od.p := by
          rw [Nat.card_zpowers, horder]
        have hEq : H = H0 := hH0uniq H ⟨hHle, hHcard⟩
        have hxH : x ∈ H := Subgroup.mem_zpowers x
        rw [hH0eq] at hEq
        exact hEq ▸ hxH
    · intro x hx
      refine ⟨od.P0_le_K0 hx, ?_⟩
      have hdiv : orderOf x ∣ od.p := by
        simpa [od.P0_card] using (Subgroup.orderOf_dvd_natCard od.P0 hx)
      rcases (Nat.dvd_prime od.hp_prime).mp hdiv with h | h
      · simp [orderOf_eq_one_iff.mp h]
      · rw [← h]
        exact pow_orderOf_eq_one x
  intro B hBle hB_elem hBcard
  have hBcardpos : 1 < Nat.card B := by
    rw [hBcard]
    nlinarith [od.hp_prime.two_le]
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp hBcardpos
  let : IsElementaryAbelian od.p B := hB_elem
  have hpow : ∀ x : B, (x : G) ^ od.p = 1 := by
    intro x
    have hexp : Monoid.exponent B = od.p := IsElementaryAbelian.exponent_eq_prime
    have hdiv : Monoid.exponent B ∣ od.p := by rw [hexp]
    exact congrArg Subtype.val
      ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdiv) x)
  have hFleP : ∀ f : G, f ∈ od.F → f ^ od.p = 1 → f ∈ od.P := by
    intro f hf hfp
    have hset := secondCase_linear_omega_F_order_p_eq_P c w d od
    exact (Set.ext_iff.mp hset f).mp ⟨hf, hfp⟩
  have hK0leP0 : ∀ k : G, k ∈ od.K0 → k ^ od.p = 1 → k ∈ od.P0 := by
    intro k hk hkp
    have hset := hP0order
    exact (Set.ext_iff.mp hset k).mp ⟨hk, hkp⟩
  have hF_norm_K0 : od.F ≤ Subgroup.normalizer (od.K0 : Set G) := by
    intro f hf
    exact Subgroup.centralizer_le_normalizer (od.K0 : Set G) (by
      intro k hk
      have hfcent : f ∈ Subgroup.centralizer (d.E : Set G) := od.F_centralizes_E hf
      exact (Subgroup.mem_centralizer_iff.mp hfcent) k (hK0leE hk))
  have hcoe : ((od.F ⊔ od.K0 : Subgroup G) : Set G) =
      (od.F : Set G) * (od.K0 : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right od.F od.K0 hF_norm_K0
  have hBleA : B ≤ od.A := by
    intro x hx
    have hxprod : (x : G) ∈ (od.F : Set G) * (od.K0 : Set G) := by
      rw [← hcoe]
      exact hBle hx
    rcases hxprod with ⟨f, hf, k, hk, hfk⟩
    change f * k = x at hfk
    have hcomm : f * k = k * f := by
      have hfcent : f ∈ Subgroup.centralizer (d.E : Set G) := od.F_centralizes_E hf
      exact ((Subgroup.mem_centralizer_iff.mp hfcent) k (hK0leE hk)).symm
    have hxp : (x : G) ^ od.p = 1 := hpow ⟨x, hx⟩
    have hfkpow : (f * k) ^ od.p = f ^ od.p * k ^ od.p :=
      (Commute.mul_pow (show Commute f k from hcomm) od.p)
    have hprod_pow : f ^ od.p * k ^ od.p = 1 := by
      calc
        f ^ od.p * k ^ od.p = (f * k) ^ od.p := hfkpow.symm
        _ = (x : G) ^ od.p := by rw [hfk]
        _ = 1 := hxp
    have hfp_mem : f ^ od.p ∈ od.F := od.F.pow_mem hf od.p
    have hkp_mem : k ^ od.p ∈ od.K0 := od.K0.pow_mem hk od.p
    have hfp_eq : f ^ od.p = 1 := by
      have hmem : f ^ od.p ∈ od.F ⊓ od.K0 := by
        refine ⟨hfp_mem, ?_⟩
        have hEq : f ^ od.p = (k ^ od.p)⁻¹ := by
          calc
            f ^ od.p = f ^ od.p * k ^ od.p * (k ^ od.p)⁻¹ := by simp
            _ = (k ^ od.p)⁻¹ := by rw [hprod_pow]; simp
        rw [hEq]
        exact od.K0.inv_mem hkp_mem
      rw [hF0] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hkp_eq : k ^ od.p = 1 := by
      have hprod_pow' := hprod_pow
      rw [hfp_eq] at hprod_pow'
      simpa using hprod_pow'
    have hfP : f ∈ od.P := hFleP f hf hfp_eq
    have hkP0 : k ∈ od.P0 := hK0leP0 k hk hkp_eq
    rw [od.A_eq]
    rw [← hfk]
    exact (od.P ⊔ od.P0).mul_mem
      ((le_sup_left : od.P ≤ od.P ⊔ od.P0) hfP)
      ((le_sup_right : od.P0 ≤ od.P ⊔ od.P0) hkP0)
  apply Subgroup.eq_of_le_of_card_ge hBleA
  rw [hBcard, od.A_card]

end CFSG.GorensteinWalter
