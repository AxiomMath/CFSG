module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111Action
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Nilpotent

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Proposition 11.1: fixed-point-free product core

If an acting subgroup preserves two disjoint factors and has trivial
centralizer in each factor, then it also has trivial centralizer in their
product.  Thompson's theorem then makes the product nilpotent.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise

universe u

/-- Fixed points in a product of two invariant disjoint factors split into
fixed points in the two factors.  In particular, trivial factor centralizers
give a trivial centralizer in the product. -/
public theorem proposition111_subgroupCentralizerIn_product_eq_bot
    {X : Type u} [Group X]
    {H R B P : Subgroup X}
    (hHmul : (H : Set X) = (R : Set X) * (B : Set X))
    (hdisj : Disjoint R B)
    (hPnormR : P ≤ Subgroup.normalizer (R : Set X))
    (hPnormB : P ≤ Subgroup.normalizer (B : Set X))
    (hCR : subgroupCentralizerIn R P = ⊥)
    (hCB : subgroupCentralizerIn B P = ⊥) :
    subgroupCentralizerIn H P = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxprod : x ∈ (R : Set X) * (B : Set X) := by
    rw [← hHmul]
    exact hx.1
  rcases Set.mem_mul.mp hxprod with ⟨r, hrR, b, hbB, rfl⟩
  have hxC : r * b ∈ Subgroup.centralizer (P : Set X) := hx.2
  have hfactorFixed : ∀ q : X, q ∈ P →
      q * r * q⁻¹ = r ∧ q * b * q⁻¹ = b := by
    intro q hqP
    have hqrR : q * r * q⁻¹ ∈ R :=
      ((Subgroup.mem_normalizer_iff.mp (hPnormR hqP)) r).mp hrR
    have hqbB : q * b * q⁻¹ ∈ B :=
      ((Subgroup.mem_normalizer_iff.mp (hPnormB hqP)) b).mp hbB
    have hxcomm : q * (r * b) = (r * b) * q :=
      (Subgroup.mem_centralizer_iff.mp hxC) q hqP
    have hconj : (q * r * q⁻¹) * (q * b * q⁻¹) = r * b := by
      calc
        (q * r * q⁻¹) * (q * b * q⁻¹) = q * (r * b) * q⁻¹ := by
          group
        _ = r * b := by rw [hxcomm]; group
    have heq : r⁻¹ * (q * r * q⁻¹) =
        b * (q * b * q⁻¹)⁻¹ := by
      calc
        r⁻¹ * (q * r * q⁻¹) =
            r⁻¹ * ((q * r * q⁻¹) * (q * b * q⁻¹)) *
              (q * b * q⁻¹)⁻¹ := by group
        _ = r⁻¹ * (r * b) * (q * b * q⁻¹)⁻¹ := by rw [hconj]
        _ = b * (q * b * q⁻¹)⁻¹ := by group
    have hleftR : r⁻¹ * (q * r * q⁻¹) ∈ R :=
      R.mul_mem (R.inv_mem hrR) hqrR
    have hrightB : b * (q * b * q⁻¹)⁻¹ ∈ B :=
      B.mul_mem hbB (B.inv_mem hqbB)
    have hleftOne : r⁻¹ * (q * r * q⁻¹) = 1 :=
      Subgroup.disjoint_def.mp hdisj hleftR (heq ▸ hrightB)
    have hrightOne : b * (q * b * q⁻¹)⁻¹ = 1 := by
      rw [← heq]
      exact hleftOne
    exact ⟨(inv_mul_eq_one.mp hleftOne).symm,
      (mul_inv_eq_one.mp hrightOne).symm⟩
  have hrC : r ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hqP
    have h := congrArg (fun z : X => z * q) (hfactorFixed q hqP).1
    simpa [mul_assoc] using h
  have hbC : b ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hqP
    have h := congrArg (fun z : X => z * q) (hfactorFixed q hqP).2
    simpa [mul_assoc] using h
  have hrOne : r = 1 := by
    have hr : r ∈ subgroupCentralizerIn R P := ⟨hrR, hrC⟩
    rw [hCR] at hr
    simpa using hr
  have hbOne : b = 1 := by
    have hb : b ∈ subgroupCentralizerIn B P := ⟨hbB, hbC⟩
    rw [hCB] at hb
    simpa using hb
  simp [hrOne, hbOne]

/-- A prime-order subgroup acting fixed-point-freely on two invariant,
disjoint product factors acts fixed-point-freely on the product, which is
therefore nilpotent by Thompson's theorem. -/
public theorem proposition111_fixed_product_nilpotent
    {X : Type u} [Group X] [Finite X]
    {H R B P : Subgroup X}
    (hHmul : (H : Set X) = (R : Set X) * (B : Set X))
    (hdisj : Disjoint R B)
    (hPnormH : P ≤ Subgroup.normalizer (H : Set X))
    (hPnormR : P ≤ Subgroup.normalizer (R : Set X))
    (hPnormB : P ≤ Subgroup.normalizer (B : Set X))
    (hPprime : Nat.Prime (Nat.card P))
    (hCR : subgroupCentralizerIn R P = ⊥)
    (hCB : subgroupCentralizerIn B P = ⊥) :
    Group.IsNilpotent H := by
  apply proposition102_nilpotent_of_prime_fixedPointFree
    H P hPnormH hPprime
  exact proposition111_subgroupCentralizerIn_product_eq_bot
    hHmul hdisj hPnormR hPnormB hCR hCB

end CFSG.BenderSuzuki
