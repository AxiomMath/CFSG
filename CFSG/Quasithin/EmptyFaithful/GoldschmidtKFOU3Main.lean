module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdDisp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Inn
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Gr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Syl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AutTransport

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.QuasithinUnique.Ch1

theorem identOddU3_holds : IdentOddU3 := by
  intro S _ _ p hp hp5 hS hnab hQ hU3 hL32
  have := hS
  obtain ⟨w, hw2, K, hK, hKL⟩ := hL32
  by_cases hw1 : w = 1
  · subst hw1
    exact false_of_fixedSub_one hQ hK hKL
  have hKfix : K ≤ SBd18.fixedSub w := CFSG.Quasithin.A3.subnormal_le hK
  have hKperf : Group.IsPerfect K := (isQuasisimple_of_isPSL_three_two hKL).1
  have hKcard : Nat.card K = 168 := SBc11.card_of_isPSL_three_two hKL
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hU3
  have hU : UnitaryFieldData p 1 F := ⟨hp, le_rfl, by rw [hcard]; ring⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hU
  let ψ : S ≃* hypPSU hU 1 1 := e.trans (hypPSUEquivStatedProj hU hR (by norm_num)).symm
  have hw2' : ∀ x, w (w x) = x := fun x => by
    have := congrArg (fun f : MulAut S => f x) hw2
    simpa using this
  have hα1 : transAut ψ w ≠ 1 := by
    intro h1
    apply hw1
    ext x
    apply ψ.injective
    rw [← transAut_apply, h1]
    rfl
  have hord : orderOf (transAut ψ w) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact transAut_mul_self ψ w hw2') hα1
  obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation hU (by omega) (le_refl 1) (le_refl 1)
      (by norm_num)).2.2.2 _ hord
  rcases hσ with rfl | hσ
  · have hin := inner_of_sigma_id hU hA hx (hid rfl)
    rw [hΦ] at hin
    obtain ⟨t, ht, htc⟩ := exists_involution_of_isInnerAut hnab hw2 hw1
      (isInnerAut_of_transAut_mem_inner ψ w hin)
    exact false_of_perfect_card_168_centralizer_psu3 hp hp5 hcard e ht hKperf hKcard
      (hKfix.trans htc)
  · obtain ⟨c, hc0, hAc⟩ := hbar hσ
    have := hKperf
    have h7 : p = 7 := eq_seven_of_perfect_card_168_fixed hU hp5 hA hc0 hAc hσ hx
      (Q := K.map ψ.toMonoidHom) (Group.IsPerfect.map _)
      (by rw [Subgroup.card_map_of_injective ψ.injective, hKcard]) (by
        rintro _ ⟨s, hs, rfl⟩
        rw [hΦ]
        change transAut ψ w (ψ s) = ψ s
        rw [transAut_apply, SBd18.mem_fixedSub.mp (hKfix hs)])
    exact mod_three_ne_one_of_noncyclic hp hcard e hQ (by omega)

end CFSG.Quasithin.SBd19F
