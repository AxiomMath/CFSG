module

public import CFSG.Sporadic.Co1.Module.CoTwoDataInputs
public import CFSG.Sporadic.Co1.Module.OddNativeBase
public import Certificates.Data.CFSGNative.Co1.U6OddCheck

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative Matrix
open CFSG.Sporadic.Co1.U6OddNative
open CFSG.Sporadic.Co1.Module (co1Act)
open CFSG.Sporadic.Co1.Module.CoTwo

attribute [local instance] Odd.vecAct Odd.vecSMul

variable {rr : ℕ → Array ℕ} {reg : ℕ → NativeSporadic.Co1}

theorem card_mul_cent_le {G : Type*} [Group G] [Finite G] (K : Subgroup G) (g : G) (n : ℕ)
    (c : Fin n → G) (hc : ∀ i, c i ∈ K) (hinj : Function.Injective fun i => c i * g * (c i)⁻¹) :
    n * Nat.card ↥(K ⊓ Subgroup.centralizer ({g} : Set G)) ≤ Nat.card K := by
  let φ : Fin n × ↥(K ⊓ Subgroup.centralizer ({g} : Set G)) → K := fun p =>
    ⟨c p.1 * (p.2 : G), Subgroup.mul_mem _ (hc p.1) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have h1 : c i * (x : G) = c j * (y : G) := congrArg Subtype.val hxy
    have hx : g * (x : G) = (x : G) * g :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2).symm
    have hy : g * (y : G) = (y : G) * g :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2).symm
    have hconj : ∀ (z : G), g * z = z * g → ∀ d : G, d * z * g * (d * z)⁻¹ = d * g * d⁻¹ := by
      intro z hz d
      have : z * g * z⁻¹ = g := by rw [← hz]; group
      calc d * z * g * (d * z)⁻¹ = d * (z * g * z⁻¹) * d⁻¹ := by group
        _ = d * g * d⁻¹ := by rw [this]
    have hij : i = j := by
      apply hinj
      show c i * g * (c i)⁻¹ = c j * g * (c j)⁻¹
      rw [← hconj _ hx (c i), ← hconj _ hy (c j), h1]
    subst hij
    have : (x : G) = y := mul_left_cancel h1
    rw [Subtype.ext this]
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this

end CFSG.Sporadic.Co1.Module.U6Odd
