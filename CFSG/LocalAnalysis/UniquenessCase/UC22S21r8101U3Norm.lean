module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Fr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Bar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Cnt
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101USyl
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UNorm
import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem U4P.u81_exists_mem_bar {D : Data G} {L K : Subgroup G} {n p : ℕ} (u : U4P D L K n p) :
    ∃ z ∈ barImage D.M L, orderOf z = p := by
  haveI : Fact p.Prime := ⟨u.prime_p⟩
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv u.hL
  have hdvd : p ∣ Nat.card ↥(barImage D.M L) := by
    rw [← Nat.card_congr e.toEquiv]
    exact u.p_dvd_card
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz]⟩

namespace U81BasisR

variable {D : Data G} {L K B : Subgroup G} {r n p : ℕ} {b : Fin 3 → G}

theorem normalizer_zpowers_le (hb : U81BasisR D L K r B b) (u : U4P D L K n p) (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) (hBM : B ≤ D.M) (h847 : F08.R847 D) (he : 3 < CFSG.Open.evenRank G)
    (h869 : F08.R869NS5 D) (i : Fin 3) : normalizer (zpowers (b i) : Set G) ≤ D.M := by
  have hr2 := u.r_ne_two hr hrp
  have hcard : ∀ j, Nat.card (zpowers (b j)) = r := fun j => by
    rw [Nat.card_zpowers, hb.orderOf_eq hr j]
  fin_cases i
  · exact r847Four_of_r847 D h847 he L u.hL _ (zpowers_le.2 hb.mem_L) _ hr hr2 (hcard 0) p u.hσ
      (uc22s13a_thin8_of_isL2_or_isSz u.shape)
  · exact r847Four_of_r847 D h847 he K u.hK _ (zpowers_le.2 hb.mem_K) _ hr hr2 (hcard 1) p u.hσ
      (uc22s13a_thin8_of_isL2_or_isSz u.symm.shape)
  · obtain ⟨-, -, -, -, hX, -, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
    have h2M : b 2 ∈ D.M := hBM (hb.frame.mem 2)
    exact u4p_normalizer_le h869 u.hL u.pX h2M hr hr2 (hb.orderOf_eq hr 2)
      (by rw [hX]; exact hb.bar_C h2M)

theorem exists_commute (hb : U81BasisR D L K r B b) (u : U4P D L K n p)
    (hsp : IsStronglyPEmbedded p D.M) (hfour : 4 ≤ CFSG.Open.pRank p D.M) (k : Fin 3) :
    ∃ z : Bar2 D.M, orderOf z = p ∧ ∀ i (h : b i ∈ D.M), i ≠ k →
      uc22p21cPi D.M ⟨b i, h⟩ * z = z * uc22p21cPi D.M ⟨b i, h⟩ := by
  obtain ⟨hcomm, -, -, -, -, -, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have h0 : ∀ h : b 0 ∈ D.M, uc22p21cPi D.M ⟨b 0, h⟩ ∈ barImage D.M L := fun h =>
    uc22p21c_mem_barImage.2 ⟨_, hb.mem_L, rfl⟩
  have h1 : ∀ h : b 1 ∈ D.M, uc22p21cPi D.M ⟨b 1, h⟩ ∈ barImage D.M K := fun h =>
    uc22p21c_mem_barImage.2 ⟨_, hb.mem_K, rfl⟩
  fin_cases k
  · obtain ⟨z, hz, hzo⟩ := u.u81_exists_mem_bar
    refine ⟨z, hzo, fun i h hi => ?_⟩
    fin_cases i
    · exact absurd rfl hi
    · exact (hcomm z hz _ (h1 h)).symm
    · exact (mem_centralizer_iff.1 (hb.bar_C h) z (mem_sup_left hz)).symm
  · obtain ⟨z, hz, hzo⟩ := u.symm.u81_exists_mem_bar
    refine ⟨z, hzo, fun i h hi => ?_⟩
    fin_cases i
    · exact hcomm _ (h0 h) z hz
    · exact absurd rfl hi
    · exact (mem_centralizer_iff.1 (hb.bar_C h) z (mem_sup_right hz)).symm
  · obtain ⟨z, hz, hzo⟩ := u.u81_exists_mem_centralizer hsp hfour
    refine ⟨z, hzo, fun i h hi => ?_⟩
    fin_cases i
    · exact mem_centralizer_iff.1 hz _ (mem_sup_left (h0 h))
    · exact mem_centralizer_iff.1 hz _ (mem_sup_right (h1 h))
    · exact absurd rfl hi

theorem normalizer_pair_le (hb : U81BasisR D L K r B b) (u : U4P D L K n p) (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) (hBM : B ≤ D.M) (h847 : F08.R847 D) (he : 3 < CFSG.Open.evenRank G)
    (h869 : F08.R869NS5 D) (hsp : IsStronglyPEmbedded p D.M)
    (hfour : 4 ≤ CFSG.Open.pRank p D.M) (i j : Fin 3) :
    normalizer ((closure {b i, b j} : Subgroup G) : Set G) ≤ D.M := by
  haveI : Fact p.Prime := ⟨u.prime_p⟩
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    revert i j
    decide
  obtain ⟨z, hzo, hz⟩ := hb.exists_commute u hsp hfour k
  have hsB : ({b i, b j} : Set G) ⊆ B :=
    Set.insert_subset_iff.2 ⟨hb.frame.mem i, Set.singleton_subset_iff.2 (hb.frame.mem j)⟩
  have hcl : closure {b i, b j} ≤ B := (closure_le _).2 hsB
  have hsM : ({b i, b j} : Set G) ⊆ D.M := fun x hx => hBM (hsB hx)
  have hdvd := u81_dvd_card_centralizer (hcl.trans hBM) hr (u.r_ne_two hr hrp)
    (hb.frame.elem.isPGroup.to_le hcl) u.prime_p u.p_ne_two hzo
    (u81_mem_centralizer_barImage_closure hsM fun g hg => by
      rcases hg with rfl | rfl
      exacts [hz i _ hki.symm, hz j _ hkj.symm])
  refine hsp.normalizer_le_of_centralizer_le ?_ hdvd
  exact (Subgroup.centralizer_le
    (Set.singleton_subset_iff.2 (Subgroup.subset_closure (Set.mem_insert _ _)))).trans
    ((CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers _).trans
      (hb.normalizer_zpowers_le u hr hrp hBM h847 he h869 i))

theorem normalizer_closure_le (hb : U81BasisR D L K r B b) (u : U4P D L K n p) (hr : r.Prime)
    (hrp : r ∣ 2 ^ p - 1) (hBM : B ≤ D.M) (h847 : F08.R847 D) (he : 3 < CFSG.Open.evenRank G)
    (h869 : F08.R869NS5 D) (hsp : IsStronglyPEmbedded p D.M)
    (hfour : 4 ≤ CFSG.Open.pRank p D.M) {I : Finset (Fin 3)} (hI : I.Nonempty)
    (hIu : I ≠ Finset.univ) :
    normalizer ((closure (b '' (I : Set (Fin 3))) : Subgroup G) : Set G) ≤ D.M := by
  obtain ⟨i, j, rfl⟩ : ∃ i j : Fin 3, I = {i, j} := by
    revert I
    decide
  rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  exact hb.normalizer_pair_le u hr hrp hBM h847 he h869 hsp hfour i j

end U81BasisR

end CFSG.LocalAnalysis.UniquenessCase.UC22
