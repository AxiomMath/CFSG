module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProductComponents
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213t_two_le_pRank {X K K' L : Subgroup G} (hK : K ∈ calC X) (hK' : K' ∈ calC X)
    (hne : K ≠ K') (hKL : K ≤ L) (hK'L : K' ≤ L) (hLX : L ≤ X) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrK : r ∣ (center (Bar2 K)).index) (hrK' : r ∣ (center (Bar2 K')).index) :
    2 ≤ CFSG.Open.pRank r L := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv hK'
  obtain ⟨SA⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X K)))
  obtain ⟨SB⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X K')))
  obtain ⟨hpg, hnc⟩ := uc22p22u_noncyclic_of_commuting (uc22p22l_barImage_commute hK hK' hne)
    SA SB (uc22p22u_sylow_not_le_center SA (by rwa [← uc22p22u_index_center_eq eA]))
    (uc22p22u_sylow_not_le_center SB (by rwa [← uc22p22u_index_center_eq eB]))
  exact uc22p22u_two_le_pRank_of_bar hLX hr hr2 hpg hnc
    (sup_le ((map_subtype_le _).trans (uc22p22u_barImage_mono hKL))
      ((map_subtype_le _).trans (uc22p22u_barImage_mono hK'L)))

theorem uc22p2213t_exists_not_le_centralizer (D : Data G) (Ch : Choice2011 G) (hV : S22_V D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) {n : ℕ} (hpn : p ∣ 2 ^ n + 1)
    {A B : Type} [Group A] [Group B] (e : Bar2 (Hinf D.M) ≃* A × B)
    (hA : IsL2 A n ∨ IsU3 A n) (hB : IsL2 B n) :
    ∃ K ∈ calC D.M, ¬ K ≤ centralizer (c.V : Set G) ∧ (IsU3 (Bar2 K) n ∨ IsL2 (Bar2 K) n) := by
  obtain ⟨hpr, hp2⟩ := D.sig_prime p hp
  haveI : Finite (A × B) := Finite.of_injective e.toEquiv.symm e.toEquiv.symm.injective
  haveI : Finite A := Finite.prod_left B
  haveI : Finite B := Finite.prod_right A
  have hsq : p ∣ (2 ^ n) ^ 2 - 1 := by
    rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact dvd_mul_of_dvd_left hpn _
  have hL2 : ∀ {X : Type} [Group X] [Finite X], IsL2 X n → p ∣ Nat.card X := fun h => by
    rw [uc22p22r_L2_card h]
    exact dvd_mul_of_dvd_right hsq _
  have hpA : p ∣ Nat.card A := by
    rcases hA with h | h
    · exact hL2 h
    · by_cases hp3 : p = 3
      · subst hp3
        exact CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel_PSU3 h
      · have h3 : p ∣ Nat.card A * Nat.gcd 3 (2 ^ n + 1) := by
          rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_mul_gcd_of_lieModel_PSU3 h]
          exact dvd_mul_of_dvd_right hsq _
        refine (hpr.dvd_mul.1 h3).resolve_right fun h3' => hp3 ?_
        exact (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).1
          (h3'.trans (Nat.gcd_dvd_left 3 _))
  haveI hAs : IsSimpleGroup A := hA.elim CFSG.Blueprint.LieModel.isSimpleGroup_psl_two
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3
  haveI hBs : IsSimpleGroup B := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hB
  have hAab : ¬ ∀ x y : A, x * y = y * x := by
    intro h
    obtain ⟨a, b, hab⟩ := hA.elim CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2
      CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3
    exact hab (h a b)
  have hBab : ¬ ∀ x y : B, x * y = y * x := by
    intro h
    obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hB
    exact hab (h a b)
  obtain ⟨KA, KB, hKA, hKB, ⟨eA⟩, ⟨eB⟩, hne⟩ := exists_two_calC_of_bar2_hinf_prod hAab hBab e
  haveI : IsSimpleGroup (Bar2 KA) := eA.isSimpleGroup
  haveI : IsSimpleGroup (Bar2 KB) := eB.isSimpleGroup
  have hiA : p ∣ (center (Bar2 KA)).index := by
    rw [P22w.center_eq_bot_of_isSimpleGroup hKA.2.2, index_bot, Nat.card_congr eA.toEquiv]
    exact hpA
  have hiB : p ∣ (center (Bar2 KB)).index := by
    rw [P22w.center_eq_bot_of_isSimpleGroup hKB.2.2, index_bot, Nat.card_congr eB.toEquiv]
    exact hL2 hB
  by_cases hAV : KA ≤ centralizer (c.V : Set G)
  · by_cases hBV : KB ≤ centralizer (c.V : Set G)
    · refine absurd ((hV h1930 c).2 p hp).2 (not_le.2 ?_)
      exact uc22p2213t_two_le_pRank hKA hKB (fun h => hne (h ▸ rfl))
        (le_inf (uc22p22a_le_of_isSubnormal hKA.1) hAV)
        (le_inf (uc22p22a_le_of_isSubnormal hKB.1) hBV) inf_le_left hpr hp2 hiA hiB
    · exact ⟨KB, hKB, hBV, Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eB.symm hB)⟩
  · refine ⟨KA, hKA, hAV, ?_⟩
    rcases hA with h | h
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eA.symm h)
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eA.symm h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
