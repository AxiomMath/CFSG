module

public import CFSG.LieType.Ree.LargeReeInvolutionCoordinates
import CFSG.LieType.Ree.LargeReeCentralTwoCover

set_option linter.unusedSectionVars false

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover
  CFSG.LieType.Chevalley.RootOps
open scoped commutatorElement

namespace CFSG.Quasithin.H13.NQCore.F4


variable {K : Type} [Field K] [CharP K F4.prime]

theorem heightSeries_six_comm {x y : ModGL F4.tag K} (hx : x ∈ heightSeries F4.tag K 6)
    (hy : y ∈ heightSeries F4.tag K 6) : x * y = y * x := by
  have h := commutator_heightSeries_le (τ := F4.tag) K 6 6
  rw [show (6 : ℤ) + 6 = 12 by norm_num, heightSeries_twelve] at h
  have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup (ModGL F4.tag K)) :=
    h (Subgroup.commutator_mem_commutator hx hy)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem sq_eq_one_of_mem_heightSeries_six (h2 : (2 : K) = 0) {x : ModGL F4.tag K}
    (hx : x ∈ heightSeries F4.tag K 6) : x ^ 2 = 1 := by
  have hcl := heightSeries_eq_closure (K := K) (6 : ℤ)
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, -, c, rfl⟩ := hg
    rw [sq, ← pinnedX_add, ← two_mul, h2, zero_mul, pinnedX_zero]
  | one => rw [one_pow]
  | mul x y hx hy ihx ihy =>
    have hxV : x ∈ heightSeries F4.tag K 6 := hcl ▸ hx
    have hyV : y ∈ heightSeries F4.tag K 6 := hcl ▸ hy
    rw [(show Commute x y from heightSeries_six_comm hxV hyV).mul_pow, ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

theorem mem_heightSet_six {r : ℕ} (hr : 24 ≤ r ∧ r ≤ 47)
    (hh : 6 ≤ height (orbitCertRoot F4.tag r)) : orbitCertRoot F4.tag r ∈ heightSet 6 := by
  have := (isRoot_pos_iff_f4 (orbitCertRoot F4.tag r)).2 ⟨r, hr.1, hr.2, rfl⟩
  exact ⟨this.1, this.2, hh⟩

theorem sylowV_mem_heightSeries_six (a : ℕ) (i l : K) :
    sylowV a K 0 0 0 0 0 0 0 0 i 0 0 l ∈ heightSeries F4.tag K 6 := by
  have h44 : orbitCertRoot F4.tag 44 ∈ heightSet 6 :=
    mem_heightSet_six ⟨by norm_num, by norm_num⟩ (by decide +kernel)
  have h47 : orbitCertRoot F4.tag 47 ∈ heightSet 6 :=
    mem_heightSet_six ⟨by norm_num, by norm_num⟩ (by decide +kernel)
  have h41 : orbitCertRoot F4.tag 41 ∈ heightSet 6 :=
    mem_heightSet_six ⟨by norm_num, by norm_num⟩ (by decide +kernel)
  have h45 : orbitCertRoot F4.tag 45 ∈ heightSet 6 :=
    mem_heightSet_six ⟨by norm_num, by norm_num⟩ (by decide +kernel)
  have hz : (0 : K) ^ (2 * 2 ^ a) = 0 := zero_pow (by positivity)
  simp only [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma, hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    pinnedX_zero, one_mul, mul_one]
  exact mul_mem (mul_mem (pinnedX_mem_heightSeries h44 _) (pinnedX_mem_heightSeries h47 _))
    (mul_mem (pinnedX_mem_heightSeries h41 _) (pinnedX_mem_heightSeries h45 _))

variable [Finite K]

theorem exists_elementaryAbelian_reeFixedPosUnipotent {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ E : Subgroup (ModGL F4.tag K), E ≤ F4.reeFixedPosUnipotent K a ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
      Nat.card K ^ 2 ≤ Nat.card E := by
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K F4.prime
    exact_mod_cast this
  have : Finite (ModGL F4.tag K) := finite_modGL
  refine ⟨heightSeries F4.tag K 6 ⊓ F4.reeFixedPosUnipotent K a, inf_le_right,
    fun x hx => sq_eq_one_of_mem_heightSeries_six h2 hx.1, ?_⟩
  let vec : K × K → Fin 12 → K := fun p => ![0, 0, 0, 0, 0, 0, 0, 0, p.1, 0, 0, p.2]
  have hv : ∀ p, sylowVec a K (vec p) = sylowV a K 0 0 0 0 0 0 0 0 p.1 0 0 p.2 := by
    intro p
    simp [sylowVec, vec]
  have hmem : ∀ p, sylowVec a K (vec p) ∈
      heightSeries F4.tag K 6 ⊓ F4.reeFixedPosUnipotent K a := fun p =>
    ⟨(hv p) ▸ sylowV_mem_heightSeries_six a p.1 p.2, (bijOn_sylowVec hK).1 (Set.mem_univ _)⟩
  let f : K × K → ↥(heightSeries F4.tag K 6 ⊓ F4.reeFixedPosUnipotent K a) :=
    fun p => ⟨sylowVec a K (vec p), hmem p⟩
  have hf : Function.Injective f := by
    intro p q h
    have h1 := Subtype.mk.inj h
    have h3 := (bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) h1
    have e8 := congrFun h3 8
    have e11 := congrFun h3 11
    simp only [vec] at e8 e11
    exact Prod.ext e8 e11
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, ← sq] at this

end CFSG.Quasithin.H13.NQCore.F4
