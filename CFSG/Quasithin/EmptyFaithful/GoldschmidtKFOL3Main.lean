module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOL3Graph
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOL3Inner
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdDisp

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.QuasithinUnique.Ch1 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

theorem eq_seven_of_fixed_involution {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hZ : Subgroup.center (projectiveSL 3 (ZMod p)) = ⊥)
    {β : MulAut (projectiveSL 3 (ZMod p))} (hβ : β * β = 1) (hβ1 : β ≠ 1)
    {K : Subgroup (projectiveSL 3 (ZMod p))} [Group.IsPerfect K] (hcard : Nat.card K = 168)
    (hK : ∀ x ∈ K, β x = x) : p = 7 := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP_ge_three (p := p) (by omega)
  rcases classify_involution (F := ZMod p) (Nat.card_zmod p) h2 β hβ with ⟨g, hg⟩ | ⟨A, hA, rfl⟩
  · exfalso
    have hg1 : g ≠ 1 := by
      rintro rfl
      apply hβ1
      ext x
      simp [hg]
    have hgc : g * g ∈ Subgroup.center (projectiveSL 3 (ZMod p)) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun f : MulAut (projectiveSL 3 (ZMod p)) => f x) hβ
      simp only [MulAut.mul_apply, hg, MulAut.one_apply] at h1
      have h1' : (g * g)⁻¹ * x * (g * g) = x :=
        calc (g * g)⁻¹ * x * (g * g) = g⁻¹ * (g⁻¹ * x * g) * g := by group
          _ = x := h1
      calc x * (g * g) = (g * g) * ((g * g)⁻¹ * x * (g * g)) := by group
        _ = (g * g) * x := by rw [h1']
    have hg2 : g ^ 2 = 1 := by
      rw [sq]
      simpa [hZ] using hgc
    refine false_of_perfect_card_168_centralizer hp2 hg2 hg1 hcard fun x hx => ?_
    have h1 := hg x
    rw [hK x hx] at h1
    calc x * g = g * (g⁻¹ * x * g) := by group
      _ = g * x := by rw [← h1]
  · exact eq_seven_of_fixed_graph hp5 hA hcard hK

theorem identOddL3_holds : IdentOddL3 := by
  intro S _ _ p hp hp5 hS hnab hQ hmod ⟨w, hw2, K, hK, hKL⟩
  have : Fact p.Prime := ⟨hp⟩
  by_cases hw1 : w = 1
  · subst hw1
    exact (false_of_fixedSub_one hQ hK hKL).elim
  · obtain ⟨ψ⟩ := exists_mulEquiv_projectiveSL_zmod hmod
    have hKperf : Group.IsPerfect ↥K := (isQuasisimple_of_isPSL_three_two hKL).1
    have hKcard : Nat.card ↥K = 168 := SBc11.card_of_isPSL_three_two hKL
    have hperf : Group.IsPerfect ↥(K.map ψ.toMonoidHom) := Group.IsPerfect.map _
    have hcard : Nat.card ↥(K.map ψ.toMonoidHom) = 168 := by
      rw [← hKcard]
      exact Nat.card_congr (K.equivMapOfInjective ψ.toMonoidHom ψ.injective).toEquiv.symm
    have hw2' : ∀ x, w (w x) = x := fun x => by
      simpa using congrArg (fun f : MulAut S => f x) hw2
    exact eq_seven_of_fixed_involution hp5 (center_eq_bot_of_equiv ψ.symm hnab)
      (transAut_mul_self ψ w hw2') (transAut_ne_one ψ hw1) hcard
      (fixed_transAut_map ψ w (CFSG.Quasithin.A3.subnormal_le hK))

end CFSG.Quasithin.SBd19F
