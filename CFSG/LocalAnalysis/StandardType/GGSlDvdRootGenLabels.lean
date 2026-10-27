module

public import CFSG.LocalAnalysis.StandardType.GGSlDvdRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem recipeLinear_rootGenAvoidKG_tableB_dvd {d N p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N - 1) (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  haveI : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  rcases (show d = 2 ∨ d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h2 | h3 | h4 | h5
  · subst h2
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd) hp2
  · subst h3
    exact ⟨0, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num))),
      ggTorusRootGenAvoidKG_of_mulEquiv (TypeA.recipeEquiv 3 K) hI
        (ggTorusRootGenAvoidKG_linearDvd hp hpK (by norm_num) hpd (r := 0) (by norm_num))⟩
  · subst h4
    have h1 : p ∣ 2 ^ 2 := by
      rw [show 2 ^ 2 = 4 by norm_num]
      exact hpd
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h1)) hp2
  · have hsec : TypeA.SLHasSections d K := TypeA.slHasSections_of_five_le h5
    exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_sub_two hp hpK hd hsec),
      ggTorusRootGenAvoidKG_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (ggTorusRootGenAvoidKG_linearDvd hp hpK (by omega) hpd (r := d - 2)
          (le_max_left _ _))⟩

theorem ggRootGenKGAvoidOn_typeADvd : GGRootGenKGAvoidOn GGTypeALabelDvd := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨h, hpn, hpl⟩
  dsimp only at h hpn hpl
  subst h
  intro Q hQ
  have hl1 : 1 ≤ l := hlab.2.1
  exact recipeLinear_rootGenAvoidKG_tableB_dvd hp hpn ⟨n, rfl⟩ (by omega) hpl hQ

end CFSG.StandardType

end
