module

public import CFSG.RankThree.GF2n.Smith81.S81R213D
public import CFSG.RankThree.GF2n.Smith81.S81R213K4
public import CFSG.RankThree.GF2n.Smith81.S81R213Q
public import CFSG.RankThree.GF2n.Smith81.S81RTransvOrder
public import CFSG.RankThree.GF2n.Smith81.Sec212Lanes

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

section Main

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem lin213_main (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) (hNF : Smith212ENonfusedE3LStatement)
    (IH : Smith1981Below (Nat.card G)) (hSE : SmithECfg M Q Z B) (hc3 : InCaseE3L M Q Z B)
    (hD8 : E3LD8CentreStatement)
    (hRoot : ∀ x' : G, x' ∈ M → x' ∉ Q → IsConj z x' → ∀ X : Subgroup G, IsZConjugate Z X →
      x' ∈ X → (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x'⁆ ⊔ Z)
    {x y : G} (hxc : IsConj z x) (hxM : x ∈ M) (hyc : IsConj z y) (hyM : y ∈ M) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  have hxx : x * x = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hxc
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  by_cases hxQ : x ∈ Q
  · by_cases hyQ : y ∈ Q
    · refine lin213_concl_of H ?_
      rcases sq_eq_one_or_inZClass_of_mem_Q H (Q.mul_mem hxQ hyQ) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact concl_Q_left Dt hxc hxQ hyc hyM hyQ
  by_cases hyQ : y ∈ Q
  · refine lin213_concl_conj x⁻¹ ?_
    have e : x⁻¹ * (x * y) * x⁻¹⁻¹ = y * x := by group
    rw [e]
    exact concl_Q_left Dt hyc hyQ hxc hxM hxQ
  obtain ⟨gx, hgx, hx⟩ := Dt.actsAs hxc hxM hxQ
  obtain ⟨gy, hgy, hy⟩ := Dt.actsAs hyc hyM hyQ
  have hgxx : gx * gx = 1 := isTransvec_mul_self hgx
  have hgyy : gy * gy = 1 := isTransvec_mul_self hgy
  have hgxinv : gx⁻¹ = gx := inv_eq_of_mul_eq_one_right hgxx
  have hgyinv : gy⁻¹ = gy := inv_eq_of_mul_eq_one_right hgyy
  refine lin213_concl_of H ?_
  by_cases hprop : ∃ s : K, (gy : Matrix (Fin 6) (Fin 6) K) - 1 =
      s • ((gx : Matrix (Fin 6) (Fin 6) K) - 1)
  ·
    have hcomm := comm_of_prop Dt hRoot hxc hxM hxQ hyc hyM hyQ hgx hgy hx hy hprop
    left
    rw [pow_two]
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcomm]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  · have hg1 : gx * gy ≠ 1 := by
      intro h
      apply hprop
      refine ⟨1, ?_⟩
      have h1 : gy = gx := by
        have := eq_inv_of_mul_eq_one_right h
        rw [this, hgxinv]
      rw [h1, one_smul]
    rcases orderOf_mul_cases_gl hgx hgy with h4 | hodd
    · have hpos : 0 < orderOf (gx * gy) := orderOf_pos _
      have hle : orderOf (gx * gy) ≤ 4 := Nat.le_of_dvd (by norm_num) h4
      have hne1 : orderOf (gx * gy) ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
      have hne3 : orderOf (gx * gy) ≠ 3 := fun h => by rw [h] at h4; omega
      have hcases : orderOf (gx * gy) = 2 ∨ orderOf (gx * gy) = 4 := by omega
      rcases hcases with h2 | h4'
      ·
        have hcomm : gx * gy = gy * gx := by
          have h : (gx * gy) * (gx * gy) = 1 := by
            rw [← pow_two, ← h2]
            exact pow_orderOf_eq_one _
          have h' := eq_inv_of_mul_eq_one_left h
          rw [mul_inv_rev, hgyinv, hgxinv] at h'
          exact h'
        have hnot : ¬ ∃ s : K, (gy : Matrix (Fin 6) (Fin 6) K) - 1 =
            s • ((gx : Matrix (Fin 6) (Fin 6) K) - 1) := hprop
        rcases two_close_of_comm Dt hxc hxM hxQ hyc hyM hyQ hgx hgy hx hy hcomm hnot with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨-, hconj⟩ := concl_four Dt hNF IH hSE hc3 hD8 hxc hxM hxQ hyc hyM hyQ hgx hgy hx hy
          h4'
        exact Or.inr (Or.inl (inZClass_of_isConj Dt.hz Dt.hz1 hconj))
    · exact Or.inr (Or.inr (odd_orderOf_mul Dt hxc hxM hxQ hyc hyM hyQ hgx hgy hx hy hodd hg1))

end Main

section Final


theorem smith213E3L_of_inputs (hFE1 : Smith24E3LUniformStatement) (hFE2 : E3LRootEltStatement)
    (hNF : Smith212ENonfusedE3LStatement) (hRoot : Smith212E3LRootStatement)
    (hD8 : E3LD8CentreStatement) : Smith213E3LStatement := by
  intro G _ _ M Q Z B IH hSE hc3 z hz hz1
  have hrem : RemCfg M Q Z B := hSE.toRemCfg
  have H : StrothHyp M Q Z := hrem.ctx.hyp
  obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hrem hc3 K γ M₀ hD
  have Dt : E3LDat M Q Z B K γ M₀ ψ φ z :=
    ⟨hrem.ctx, hD, d, hz, hz1,
      fun y hyc hyM hyQ w hw hw1 => hNF G M Q Z B IH hSE hc3 z hz hz1 y hyM hyQ hyc w hw hw1,
      fun y hyc hyM hyQ => hFE2 G M Q Z B IH hrem hc3 K γ M₀ hD ψ φ d z hz hz1 y hyc hyM hyQ⟩
  refine isRootInvolutionSet_of_lin213Prop H hz hz1 ?_
  intro x y hxM hyM hxZ hyZ
  exact lin213_main Dt hNF IH hSE hc3 hD8
    (fun x' hM hQ hc X hX hxX => hRoot G M Q Z B IH hrem hc3 z hz hz1 x' hM hQ hc X hX hxX)
    (isConj_of_inZClass H hz hz1 hxZ) hxM (isConj_of_inZClass H hz hz1 hyZ) hyM

end Final

end CFSG.RankThree.GF2n.Smith81.E3LRoot
