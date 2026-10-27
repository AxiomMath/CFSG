module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9AGen3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin6

public section

namespace CFSG.Quasithin

open Equiv CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

namespace S35.N9

open S35.Fin

theorem cj_top' (g : Perm (Fin 5)) : cj g (⊤ : Subgroup (Perm (Fin 5))) = ⊤ := by
  ext x
  rw [mem_cj]
  simp

theorem exists_three_cosets {D W : Subgroup (Perm (Fin 5))} (h : 3 ≤ D.relIndex W) :
    ∃ y ∈ W, ∃ z ∈ W, y ∉ D ∧ z ∉ D ∧ y⁻¹ * z ∉ D := by
  classical
  have hfin : Finite (W ⧸ D.subgroupOf W) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (W ⧸ D.subgroupOf W)
  have h2 : 2 < Fintype.card (W ⧸ D.subgroupOf W) := by
    have : D.relIndex W = Nat.card (W ⧸ D.subgroupOf W) := rfl
    rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
  induction a using Quotient.inductionOn' with | _ a => ?_
  induction b using Quotient.inductionOn' with | _ b => ?_
  induction c using Quotient.inductionOn' with | _ c => ?_
  have key : ∀ u v : W, (QuotientGroup.mk u : W ⧸ D.subgroupOf W) ≠ QuotientGroup.mk v →
      (u : Perm (Fin 5))⁻¹ * v ∉ D := by
    intro u v huv hD
    apply huv
    rw [QuotientGroup.eq]
    exact hD
  exact ⟨a⁻¹ * b, (a⁻¹ * b).2, a⁻¹ * c, (a⁻¹ * c).2, key a b hab, key a c hac,
    by simpa [mul_assoc] using key b c hbc⟩

theorem card_sylow_two (Q : Sylow 2 (Perm (Fin 5))) : Nat.card Q = 8 := by
  rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have h : Nat.factorial 5 = 120 := by decide
  rw [h, Nat.factorization_def _ Nat.prime_two]
  have h3 : padicValNat 2 120 = 3 := by decide +kernel
  rw [h3]
  norm_num

theorem hat_mul (g0 g1 y : Perm (Fin 5)) :
    g0⁻¹ * g1 * (g1⁻¹ * y * g1) * (g0⁻¹ * g1)⁻¹ = g0⁻¹ * y * g0 := by group

theorem gen_of_two_group {D W : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hW : IsPGroup 2 W) (hidx : 3 ≤ D.relIndex W) : That D ⊔ W = ⊤ := by
  obtain ⟨g0, rfl⟩ := exists_cj hD
  obtain ⟨y, hyW, z, hzW, hyD, hzD, hyzD⟩ := exists_three_cosets hidx
  obtain ⟨Q, hQ⟩ := hW.exists_le_sylow
  obtain ⟨g1, hg1⟩ := exists_cj (card_sylow_two Q)
  have hmem : ∀ x ∈ W, g0⁻¹ * g1 * (g1⁻¹ * x * g1) * (g0⁻¹ * g1)⁻¹ = g0⁻¹ * x * g0 ∧
      g1⁻¹ * x * g1 ∈ S5SylF := by
    intro x hx
    refine ⟨hat_mul _ _ _, ?_⟩
    have h1 : x ∈ cj g1 S5Syl := hg1 ▸ hQ hx
    exact (mem_S5Syl_iff _).mp (mem_cj.mp h1)
  have hnot : ∀ x : Perm (Fin 5), x ∉ cj g0 S5Syl → g0⁻¹ * x * g0 ∉ S5SylF := by
    intro x hx h
    exact hx (mem_cj.mpr ((mem_S5Syl_iff _).mpr h))
  set X := That (cj g0 S5Syl) ⊔ W with hX
  have hT : cj g0⁻¹ (That (cj g0 S5Syl)) = S5That := by
    have h := cj_cj_inv g0⁻¹ (That S5Syl)
    rw [inv_inv] at h
    rw [← cj_That, h, That_std]
  have hXtop : cj g0⁻¹ X = ⊤ → X = ⊤ := by
    intro h
    have := congrArg (cj g0) h
    rwa [cj_cj_inv, cj_top'] at this
  have hWmem : ∀ x ∈ W, g0⁻¹ * x * g0 ∈ cj g0⁻¹ X := by
    intro x hx
    rw [mem_cj, show (g0⁻¹)⁻¹ * (g0⁻¹ * x * g0) * g0⁻¹ = x by group]
    exact (le_sup_right : W ≤ X) hx
  have hTmem : ∀ x ∈ S5That, x ∈ cj g0⁻¹ X := by
    intro x hx
    rw [← hT] at hx
    exact (Subgroup.map_mono (le_sup_left : That (cj g0 S5Syl) ≤ X)) hx
  have hs02 : swap (0 : Fin 5) 2 ∈ S5That := Subgroup.subset_closure (by simp)
  have hs13 : swap (1 : Fin 5) 3 ∈ S5That := Subgroup.subset_closure (by simp)
  obtain ⟨ey, hy1⟩ := hmem y hyW
  obtain ⟨ez, hz1⟩ := hmem z hzW
  have hy2 := hnot y hyD
  have hz2 := hnot z hzD
  have hyz2 : g0⁻¹ * (y⁻¹ * z) * g0 ∉ S5SylF := hnot _ hyzD
  have hyz3 : (g0⁻¹ * g1 * (g1⁻¹ * y * g1) * (g0⁻¹ * g1)⁻¹)⁻¹ *
      (g0⁻¹ * g1 * (g1⁻¹ * z * g1) * (g0⁻¹ * g1)⁻¹) = g0⁻¹ * (y⁻¹ * z) * g0 := by
    rw [ey, ez]; group
  by_cases hall : ∀ x ∈ W, (g0⁻¹ * x * g0) 4 = 4
  · exfalso
    refine coreA (g0⁻¹ * g1) _ hy1 _ hz1 ?_ ?_ ?_ ?_ ?_
    · rw [ey]; exact hall y hyW
    · rw [ez]; exact hall z hzW
    · rw [ey]; exact hy2
    · rw [ez]; exact hz2
    · rw [hyz3]; exact hyz2
  · push Not at hall
    obtain ⟨w, hwW, hw4⟩ := hall
    obtain ⟨ew, hw1⟩ := hmem w hwW
    have hr := coreB (g0⁻¹ * g1) _ hy1 _ hz1 _ hw1 (by rw [ey]; exact hy2) (by rw [ez]; exact hz2)
      (by rw [hyz3]; exact hyz2) (by rw [ew]; exact hw4)
    rw [ey, ez, ew] at hr
    apply hXtop
    refine eq_top_of_reach (gens := [swap 0 2, swap 1 3, g0⁻¹ * y * g0, g0⁻¹ * z * g0,
      g0⁻¹ * w * g0]) ?_ hr (a := 0) (b := 2) (by decide) (hTmem _ hs02)
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hTmem _ hs02
    · exact hTmem _ hs13
    · exact hWmem _ hyW
    · exact hWmem _ hzW
    · exact hWmem _ hwW

end S35.N9

end F53.Stellmacher

end CFSG.Quasithin
