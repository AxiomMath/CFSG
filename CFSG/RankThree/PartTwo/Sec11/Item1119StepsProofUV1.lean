module

import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1119Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1119StepsProof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem g_mem_normalizer_V_of_le (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hgV0 : g ∈ Subgroup.normalizer ((Subgroup.closure {s, a, x ^ 3} : Subgroup G) : Set G))
    (hV1 : ∀ y ∈ sec11P R g, (∀ w ∈ Subgroup.closure ({s, a, x ^ 3} : Set G),
        y * w * y⁻¹ * w⁻¹ ∈ Subgroup.zpowers d) → y ∈ Subgroup.closure ({s, x, a} : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {s, x, a} : Subgroup G) : Set G) := by
  have h := hbig.toSec11Data
  set P := sec11P R g with hPdef
  set V0 := Subgroup.closure ({s, a, x ^ 3} : Set G) with hV0def
  set V := Subgroup.closure ({s, x, a} : Set G) with hVdef
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have hRP : R ≤ P := Item1119Proof.R_le_P R g
  have hgP : g ∈ P := Item1119Proof.g_mem_P R g
  have hsV0 : s ∈ V0 := Subgroup.subset_closure (by simp)
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have haV : a ∈ V := Subgroup.subset_closure (by simp)
  have hV0V : V0 ≤ V := by
    rw [hV0def, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    exacts [hsV, haV, V.pow_mem (Subgroup.subset_closure (by simp)) 3]
  have hV0R : V0 ≤ R := by
    rw [hV0def, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    exacts [hsR, haR, R.pow_mem hxR 3]
  obtain ⟨hz, -⟩ := Item1119Proof.commutator_x_a_facts h45 h
  have hV0d : V0 ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    hV0R.trans (hRP.trans (Item1119Proof.P_le_normalizer_d h113 h117 h))
  have hxC : ∀ w ∈ V0, x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers d := by
    intro w hw
    refine Item1119Proof.commutator_mem_of_mem_closure hV0d ?_ hw
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · rw [← h.commute_s_x, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    · exact hz
    · rw [show x * x ^ 3 * x⁻¹ * (x ^ 3)⁻¹ = 1 by group]
      exact Subgroup.one_mem _
  have hgxV1 : ∀ w ∈ V0, (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹ * w⁻¹ ∈ Subgroup.zpowers d := by
    intro w hw
    have hw' : g⁻¹ * w * g ∈ V0 := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV0) w).mp hw
      rwa [inv_inv] at h1
    have h1 := hxC _ hw'
    have e : (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹ * w⁻¹ =
        g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by group
    rw [e, Item1119Proof.commute_of_mem_zpowers_d h113 h117 h h1 hgP, mul_inv_cancel_right]
    exact h1
  have hgxP : g * x * g⁻¹ ∈ P := P.mul_mem (P.mul_mem hgP (hRP hxR)) (P.inv_mem hgP)
  have hgxV : g * x * g⁻¹ ∈ V := hV1 _ hgxP hgxV1
  have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hle : Subgroup.closure ({s, x, a} : Set G) ≤ V.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change g * y * g⁻¹ ∈ V
    rcases hy with hy | hy | hy <;> rw [hy]
    · exact hV0V ((Subgroup.mem_normalizer_iff.mp hgV0 s).mp hsV0)
    · exact hgxV
    · rw [hga, mul_inv_cancel_right]
      exact haV
  exact hle hy

end Data

end Item1119StepsProof

end CFSG.RankThree.PartTwo.Sec11
