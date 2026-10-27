module

public import CFSG.RankThree.PartOne.KE8F.HIOuter
public import CFSG.RankThree.PartOne.KE8F.HIInner

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


section Fixed

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem eta_fixes_torsion (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (hC : Subgroup.center (adjointGroup .E8 K) = ⊥) (c : adjointGroup .E8 K)
    (hcard : Nat.card (torsionC p F c) = p ^ 4) {B : Subgroup (MulAut (adjointGroup .E8 K))}
    (hB : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B)
    {x : adjointGroup .E8 K} (hxA : x ∈ torsionC p F c) {η : MulAut (adjointGroup .E8 K)}
    (hη : η ∈ coreR p B x) : ∀ y ∈ torsionC p F c, η y = y := by
  intro y hy
  have hyx : y ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) :=
    Subgroup.mem_centralizer_singleton_iff.2 (torsionC_comm F c hxA hy).symm
  have hdV := eta_mul_inv_mem_coreV hC hB hη hyx
  have hdT := coreV_le_torus F hf hK hp hp10 hpf hC c hcard hxA hB _ hdV
  have hyT := torsionC_torus F c hy
  have hcomm := twistedTorus_comm F hdT hyT
  have hηy : η y = (η y * y⁻¹) * y := by rw [inv_mul_cancel_right]
  have hyp : (psiC F c y) ^ p = 1 := by rw [← map_pow, torsionC_pow F c hy, map_one]
  have hηyp : (η y) ^ p = 1 := by rw [← map_pow, torsionC_pow F c hy, map_one]
  have hdp : (η y * y⁻¹) ^ p = 1 := by
    apply psiC_injective F c
    have h1 : psiC F c ((η y * y⁻¹) * y) ^ p = 1 := by
      rw [← hηy, ← map_pow, hηyp, map_one]
    rw [map_mul, Commute.mul_pow hcomm, hyp, mul_one] at h1
    rw [map_pow, map_one]
    exact h1
  have hd1 : η y * y⁻¹ = 1 := by
    have h1 : orderOf (η y * y⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hdp
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exfalso
      refine coreV_card hp hC B x ?_
      have h2 : orderOf (⟨η y * y⁻¹, hdV⟩ : coreV p B x) ∣ Nat.card (coreV p B x) :=
        orderOf_dvd_natCard _
      have h3 : orderOf (⟨η y * y⁻¹, hdV⟩ : coreV p B x) = orderOf (η y * y⁻¹) :=
        Subgroup.orderOf_mk _ _
      rw [h3, h] at h2
      exact h2
  rw [hηy, hd1, one_mul]

end Fixed

section HI

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem hI_E8 (F : E8P4Frame K L ℓ f p) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (hC : Subgroup.center (adjointGroup .E8 K) = ⊥) :
    ∀ B : Subgroup (MulAut (adjointGroup .E8 K)),
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E8 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
          Odd (Nat.card ↥(autThetaT p B A)) := by
  intro B hB A hAB hA hAcard hAinn
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .E8 K) :=
    A.comap (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hAinn
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← hAcard, ← hA₀map, Subgroup.card_map_of_injective hinj]
  have hA₀p : ∀ x ∈ A₀, x ^ p = 1 := by
    intro x hx
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A)
      (MulAut.conj x : MulAut (adjointGroup .E8 K)) hx
    apply hinj
    rw [map_pow, map_one]
    exact h1
  obtain ⟨c, hc, hcard⟩ := exists_torusData F hf hK hp (by omega) hpf hA₀p
  have key : ∀ η ∈ autThetaT p B A, η ^ 2 = 1 → η = 1 := by
    intro η hη hη2
    have hηx : ∀ x ∈ A₀, x ≠ 1 → η ∈ coreR p B x := by
      intro x hx hx1
      have h1 : (MulAut.conj x : MulAut (adjointGroup .E8 K)) ∈ A := hx
      have h2 : (MulAut.conj x : MulAut (adjointGroup .E8 K)) ≠ 1 := fun h =>
        hx1 (hinj (by rw [h, map_one]))
      have h3 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hη
        (MulAut.conj x : MulAut (adjointGroup .E8 K))) h1) h2
      exact h3
    by_cases hin : η ∈ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range
    · obtain ⟨w, rfl⟩ := hin
      have hw1 := inner_core_trivial F.toE8P4Frame0 hf hK hp hp10 hpf hC c hcard hc hA₀card hB hηx
      rw [hw1, map_one]
    · have hnt : Nontrivial A₀ := by
        rw [← Finite.one_lt_card_iff_nontrivial, hA₀card]
        exact Nat.one_lt_pow (by norm_num) hp.one_lt
      obtain ⟨x, hx1⟩ := exists_ne (1 : A₀)
      have hx1' : (x : adjointGroup .E8 K) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hfixT := eta_fixes_torsion F.toE8P4Frame0 hf hK hp hp10 hpf hC c hcard hB (hc x.2) (hηx x x.2 hx1')
      exact (outer_involution_absurd F.toE8P4Frame0 hf hK hp hp10 hpf c hcard hη2 hin hfixT).elim
  by_contra hodd
  have heven : 2 ∣ Nat.card (autThetaT p B A) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.1 hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have h2 : (x : MulAut (adjointGroup .E8 K)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hx1 : x = 1 := Subtype.ext (key x.1 x.2 h2)
  rw [hx1, orderOf_one] at hx
  omega

end HI

end CFSG.RankThree.PartOne.KE8F
