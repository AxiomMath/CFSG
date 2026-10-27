module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Perf
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Cent

public section

namespace CFSG.Quasithin.H13.Sec53F.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem four_le_card_of {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem exists_torus_conj {t t' : K} (ht : t ≠ 0) (ht' : t' ≠ 0) :
    ∃ τ : Kˣ, torusElt Tag.G2 K i0 τ * gX rC t * (torusElt Tag.G2 K i0 τ)⁻¹ = gX rC t' := by
  refine ⟨Units.mk0 (t' / t) (div_ne_zero ht' ht), ?_⟩
  rw [conj_torus i0 isRoot_rC, show (∑ j, Tag.G2.cartan i0 j * rC j) = 1 by decide, zpow_one,
    Units.val_mk0, div_mul_cancel₀ _ ht]

variable [Finite K]

theorem center_zero {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {z : ModGL Tag.G2 K}
    (hz : z ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}))
    (hzc : ∀ y ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}), y * z = z * y) : z = 1 := by
  have hK4 := four_le_card_of hK hf
  have hzQc : z ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i0} : Set (ModGL Tag.G2 K)) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => hzc q (radical_le_perfectCore_zero hK4 hq)
  have hzQ : z ∈ parabolicRadical Tag.G2 K {i0} :=
    (parabolicFacts_zero hK hf).selfCentralizing ⟨perfectCore_le _ hz, hzQc⟩
  obtain ⟨t₄, t₅, rfl⟩ := centerQ0 hzQ hzQc
  obtain ⟨L, hLP, hLL, -, -, htL⟩ := leviL_data (K := K) hK4 i0
  obtain ⟨τ, hτ⟩ := exists_units_ne_one hK4
  have hd := hzc _ (le_perfectCore_of_perfect hLP hLL (htL τ))
  have hcomm : ⁅torusElt Tag.G2 K i0 τ, gX rB t₄ * gX rC t₅⁆ = 1 := by
    rw [commutatorElement_def, hd]
    group
  have e1 : ⁅torusElt Tag.G2 K i0 τ, gX rB t₄⁆ =
      gX rB ((((τ ^ (-1 : ℤ) : Kˣ) : K) + 1) * t₄) := by
    have := torus_comm (K := K) i0 isRoot_rB τ t₄
    rwa [show (∑ j, Tag.G2.cartan i0 j * rB j) = -1 by decide] at this
  have e2 : ⁅torusElt Tag.G2 K i0 τ, gX rC t₅⁆ =
      gX rC ((((τ ^ (1 : ℤ) : Kˣ) : K) + 1) * t₅) := by
    have := torus_comm (K := K) i0 isRoot_rC τ t₅
    rwa [show (∑ j, Tag.G2.cartan i0 j * rC j) = 1 by decide] at this
  rw [comm_mul_right', e1, e2, (comm_bc t₄ _).eq, mul_inv_cancel_right] at hcomm
  obtain ⟨hA, hB⟩ := prod_bc_eq_one hcomm
  have hA' : (((τ ^ (-1 : ℤ) : Kˣ) : K) + 1) ≠ 0 :=
    add_one_ne_zero (zpow_val_ne_one hτ (Or.inr rfl))
  have hB' : (((τ ^ (1 : ℤ) : Kˣ) : K) + 1) ≠ 0 :=
    add_one_ne_zero (zpow_val_ne_one hτ (Or.inl rfl))
  rw [(mul_eq_zero.mp hA).resolve_left hA', (mul_eq_zero.mp hB).resolve_left hB', gX_zero,
    gX_zero, one_mul]

theorem center_one {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {z : ModGL Tag.G2 K}
    (hz : z ∈ perfectCore (parabolicSubgroup Tag.G2 K {i1}))
    (hzc : ∀ y ∈ perfectCore (parabolicSubgroup Tag.G2 K {i1}), y * z = z * y) :
    ∃ t : K, z = gX rC t := by
  have hK4 := four_le_card_of hK hf
  have hzQc : z ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K)) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => hzc q (radical_le_perfectCore_one hK4 hq)
  exact centerQ1 ((parabolicFacts_one hK hf).selfCentralizing ⟨perfectCore_le _ hz, hzQc⟩) hzQc

end CFSG.Quasithin.H13.Sec53F.G2
