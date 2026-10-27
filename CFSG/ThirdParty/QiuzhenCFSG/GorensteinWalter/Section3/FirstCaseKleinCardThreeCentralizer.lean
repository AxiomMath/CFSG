module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicOrderThreeAutomorphism
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! A small reusable order-three action lemma for the pending `J₃` route. -/

public theorem firstCase_klein_card_three_subgroup_centralizes_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {X : Subgroup G}
    (hXcard : Nat.card X = 3) (hXle : X ≤ c.Hhat)
    (hUcard : Nat.card c.U = 3) :
    X ≤ Subgroup.centralizer (c.U : Set G) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUnorm : IsNormalIn c.U c.Hhat := by
    rw [(theorem_2_6 hmin c).1]
    refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
    intro h hh u hu
    rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
    exact Subgroup.mem_map.mpr ⟨
      (⟨h, hh⟩ : c.Hhat) * u0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
      (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
        u0 hu0 (⟨h, hh⟩ : c.Hhat), by simp⟩
  have hUcyc : IsCyclic c.U :=
    isCyclic_of_prime_card (α := c.U) (p := 3) (by simpa [hUcard])
  have hAutcard : Nat.card (MulAut c.U) = 2 := by
    rw [IsCyclic.card_mulAut c.U, hUcard, Nat.totient_prime Nat.prime_three]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hxnorm : x ∈ Subgroup.normalizer (c.U : Set G) :=
    (le_normalizer_of_isNormalIn hUnorm) (hXle hx)
  let ι : X →* Subgroup.normalizer (c.U : Set G) :=
    { toFun := fun z => ⟨(z : G), (le_normalizer_of_isNormalIn hUnorm) (hXle z.2)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  let ρ : X →* MulAut c.U := (c.U.normalizerMonoidHom).comp ι
  have hρdvdX : orderOf (ρ ⟨x, hx⟩) ∣ 3 := by
    have hd : orderOf (ρ ⟨x, hx⟩) ∣ orderOf (⟨x, hx⟩ : X) :=
      orderOf_map_dvd ρ ⟨x, hx⟩
    have hd' : orderOf (⟨x, hx⟩ : X) ∣ Nat.card X :=
      by simpa using (Subgroup.orderOf_dvd_natCard X hx)
    rw [hXcard] at hd'
    exact hd.trans hd'
  have hρdvdAut : orderOf (ρ ⟨x, hx⟩) ∣ 2 := by
    rw [← hAutcard]
    exact orderOf_dvd_natCard (ρ ⟨x, hx⟩)
  have hρone : orderOf (ρ ⟨x, hx⟩) = 1 := by
    have hgcd : Nat.gcd 3 2 = 1 := by norm_num
    exact Nat.dvd_one.mp ((Nat.dvd_gcd hρdvdX hρdvdAut).trans (by rw [hgcd]))
  have hρeq : ρ ⟨x, hx⟩ = 1 := orderOf_eq_one_iff.mp hρone
  have hfix : ρ ⟨x, hx⟩ ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hρeq]; simp
  have hfix' := congrArg (fun z : c.U => (z : G)) hfix
  have hconj : x * u * x⁻¹ = u := by
    simpa [ρ, ι, Subgroup.normalizerMonoidHom_apply_apply_coe] using hfix'
  have hcomm : x * u = u * x := by
    calc
      x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [hconj]
  exact hcomm.symm

end CFSG.GorensteinWalter
