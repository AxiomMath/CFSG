module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Order-`p` subgroups in a cyclic centralizer join

If `P` centralizes a cyclic subgroup `C`, and `P₀ ≤ C` is its unique
order-`p` subgroup, then every order-`p` subgroup of `P ⊔ C` lies in
`P ⊔ P₀`.  This is the local reduction used in the in-`M` part of the
equation-(11) region count.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_linear_prime_subgroup_le_sup_of_cyclic_join
    {G : Type u} [Group G] [Finite G]
    {P P0 C Y : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPcard : Nat.card P = p) (hP0card : Nat.card P0 = p)
    (hP0leC : P0 ≤ C) (hCcyc : IsCyclic C)
    (hCcentP : C ≤ Subgroup.centralizer (P : Set G))
    (hPinfC : P ⊓ C = ⊥)
    (hYle : Y ≤ P ⊔ C) (hYcard : Nat.card Y = p) :
    Y ≤ P ⊔ P0 := by
  classical
  obtain ⟨H0, hH0, hH0uniq⟩ :=
    secondCase_unique_order_p_subgroup_of_cyclic
      (G := G) (T := C) hCcyc rfl
      (by simpa [hP0card] using Subgroup.card_dvd_of_le hP0leC)
  have hPnormC : C ≤ Subgroup.normalizer (P : Set G) := by
    intro c hc
    exact Subgroup.centralizer_le_normalizer (P : Set G) (hCcentP hc)
  have hcoe : ((P ⊔ C : Subgroup G) : Set G) = (P : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P C hPnormC
  have hYPow : ∀ y : G, y ∈ Y → y ^ p = 1 := by
    intro y hy
    by_cases hy1 : y = 1
    · simp [hy1]
    · have horder : orderOf y = p := by
        have hdiv : orderOf y ∣ p := by
          simpa [hYcard] using (Subgroup.orderOf_dvd_natCard Y hy)
        rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with h1 | hp
        · exact False.elim (hy1 (orderOf_eq_one_iff.mp h1))
        · exact hp
      simpa [horder] using pow_orderOf_eq_one y
  intro y hy
  have hyPC : y ∈ (P : Set G) * (C : Set G) := by
    rw [← hcoe]
    exact hYle hy
  rcases hyPC with ⟨a, ha, b, hb, hab⟩
  change (a : G) * (b : G) = y at hab
  have habpow : (a : G) ^ p * (b : G) ^ p = 1 := by
    have hcomm : (a : G) * (b : G) = (b : G) * (a : G) :=
      (Subgroup.mem_centralizer_iff.mp (hCcentP hb)) (a : G) ha
    calc
      (a : G) ^ p * (b : G) ^ p = ((a : G) * (b : G)) ^ p :=
        (Commute.mul_pow (show Commute (a : G) (b : G) from hcomm) p).symm
      _ = y ^ p := by rw [hab]
      _ = 1 := hYPow y hy
  have haPow : (a : G) ^ p = 1 := by
    have hmem : (a : G) ^ p ∈ P ⊓ C := by
      refine ⟨P.pow_mem ha p, ?_⟩
      have hbPow : (b : G) ^ p ∈ C := C.pow_mem hb p
      have heq : (a : G) ^ p = ((b : G) ^ p)⁻¹ := by
        calc
          (a : G) ^ p = (a : G) ^ p * (b : G) ^ p * ((b : G) ^ p)⁻¹ := by simp
          _ = ((b : G) ^ p)⁻¹ := by rw [habpow]; simp
      rw [heq]
      exact C.inv_mem hbPow
    rw [hPinfC] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbPow : (b : G) ^ p = 1 := by
    rw [haPow] at habpow
    simpa using habpow
  have hbH0 : (b : G) ∈ H0 := by
    by_cases hb1 : (b : G) = 1
    · simpa [hb1] using H0.one_mem
    · have horderb : orderOf (b : G) = p := by
        have hdiv : orderOf (b : G) ∣ p :=
          (orderOf_dvd_iff_pow_eq_one (x := (b : G)) (n := p)).mpr hbPow
        rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with h1 | hp
        · exfalso
          exact hb1 (orderOf_eq_one_iff.mp h1)
        · exact hp
      let B : Subgroup G := Subgroup.zpowers (b : G)
      have hBle : B ≤ C := Subgroup.zpowers_le.mpr hb
      have hBcard : Nat.card B = p := by
        rw [Nat.card_zpowers, horderb]
      have hEq : B = H0 := hH0uniq B ⟨hBle, hBcard⟩
      have hbB : (b : G) ∈ B := Subgroup.mem_zpowers (b : G)
      rw [hEq] at hbB
      exact hbB
  have hy_sup : y ∈ P ⊔ P0 := by
    rw [← hab]
    exact (P ⊔ P0).mul_mem
      ((le_sup_left : P ≤ P ⊔ P0) ha)
      ((le_sup_right : P0 ≤ P ⊔ P0) (by
        have hP0H0 : P0 = H0 := hH0uniq P0 ⟨hP0leC, hP0card⟩
        rw [hP0H0]
        exact hbH0))
  exact hy_sup

end CFSG.GorensteinWalter
