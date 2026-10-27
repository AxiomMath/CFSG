module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts12c
public import CFSG.Quasithin.Vol2.KGNatSp4N13

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

namespace C11P9B

variable {K : Type} [Field K]

theorem matrix_eq_of_mulVec_sp {A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

theorem sq_eq_one_of_fix_spPlane [CharP K 2] {A : StatedSp 2 K}
    (hfix : ∀ x ∈ spPlane K, mat 2 K A *ᵥ x = x) : A ^ 2 = 1 := by
  have hsub : ∀ y, mat 2 K A *ᵥ y - y ∈ spPlane K := by
    intro y
    have hB : ∀ i : Fin 2,
        Matrix.toBilin' (spJ K) (mat 2 K A *ᵥ y - y) (Pi.single (.inl i) 1) = 0 := by
      intro i
      have he : (Pi.single (.inl i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ spPlane K := ⟨by simp, by simp⟩
      rw [LinearMap.map_sub₂, ← hfix _ he, spB_mat, hfix _ he, sub_self]
    have h0 := hB 0
    have h1 := hB 1
    rw [spB_single_inl, neg_eq_zero] at h0 h1
    exact ⟨h0, h1⟩
  apply mat_injective
  rw [map_pow, map_one]
  refine matrix_eq_of_mulVec_sp fun y => ?_
  rw [sq, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have h1 := hfix _ (hsub y)
  rw [Matrix.mulVec_sub] at h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext i
  have := congrFun h1 i
  simp only [Pi.sub_apply] at this
  linear_combination this + ((mat 2 K A *ᵥ y) i - y i) * h2

end C11P9B

open C11P9B in
theorem factCartanLineSp4_holds : FactCartanLineSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₂ hU₂ D hD
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg (by rw [hK]; exact hU₂)
  rw [(eq_std_of_stable_sp hS).2.1 hc]
  intro d hdD htriv
  obtain ⟨hDle, hDodd, -⟩ := hD
  have hdH : d ∈ H := (hDle hdD).1
  obtain ⟨γ, hγ⟩ : ∃ γ : StatedSp 2 K, π γ = ⟨d, hdH⟩ := hf.onto ⟨d, hdH⟩
  have hdγ : ((π γ : ↥H) : MulAut W) = d := congrArg Subtype.val hγ
  have hfix : ∀ x ∈ spPlane K, mat 2 K (g⁻¹ * γ * g) *ᵥ x = x := by
    intro x hx
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ x)
    have hw2 : w ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup := by
      show f w ∈ gmapSp g (spPlane K)
      rw [mem_gmapSp, hw, mat_inv_mulVec]
      exact hx
    have h1 := htriv w hw2
    rw [← hf.ker, hf.map_mul_inv, ← hdγ, hf.act4, hw, sub_eq_zero] at h1
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, mat_inv_mulVec]
  have hA2 := sq_eq_one_of_fix_spPlane hfix
  have hγ2 : γ ^ 2 = 1 := by
    have e : γ ^ 2 = g * (g⁻¹ * γ * g) ^ 2 * g⁻¹ := by
      rw [sq, sq]
      group
    rw [e, hA2, mul_one, mul_inv_cancel]
  have hd2 : d ^ 2 = 1 := by
    rw [← hdγ, ← Subgroup.coe_pow, ← map_pow, hγ2, map_one, Subgroup.coe_one]
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hDodd h1
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hd2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

end CFSG.Quasithin.Vol2.Ch11.SecA
