module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.Adapters.Involutions
public import CFSG.Quasithin.H13.GoldschmidtU43EIdx1

public section

namespace CFSG.Quasithin.H13.U43

theorem u43_noncyclic_sylow_two {J : Type} [Group J] [Finite J]
    (hNC : ¬ CFSG.HasNormalPComplement 2 J) (h2 : 2 ∣ Nat.card J) (P : Sylow 2 J) :
    ¬ IsCyclic ↥P := by
  intro hcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card J).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hnorm : Subgroup.normalizer (P : Set J) ≤ Subgroup.centralizer (P : Set J) :=
    IsCyclic.normalizer_le_centralizer hmin hcyc
  have hS : (P : Subgroup J) ≤ CFSG.centerIn (G := J) (Subgroup.normalizer (P : Subgroup J)) := by
    intro s hs
    refine ⟨Subgroup.le_normalizer hs, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hnorm hh) s hs).symm
  exact hNC (CFSG.hasNormalPComplement_of_sylow_le_center_normalizer 2 P hS)

theorem u43_hasDihedralSylowTwo_of_index_two {J : Type} [Group J] [Finite J] {m : ℕ}
    (hm : Odd m) (hJ : Nat.card J = 4 * m) (hNC : ¬ CFSG.HasNormalPComplement 2 J) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo J := by
  intro P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP4 : Nat.card ↥P = 4 := u43_card_sylow_two hm hJ P
  have hcyc : ¬ IsCyclic ↥P := u43_noncyclic_sylow_two hNC ⟨2 * m, by omega⟩ P
  have hexp : Monoid.exponent ↥P = 2 := by
    have : Nontrivial ↥P := by
      rw [← Finite.one_lt_card_iff_nontrivial, hP4]
      norm_num
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    have hdvd : orderOf g ∣ 4 := by rw [← hP4]; exact orderOf_dvd_natCard g
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf g ∣ 2 ^ 2 by simpa using hdvd) with
      ⟨k, hk, hgk⟩
    interval_cases k
    · exfalso
      exact hg (orderOf_eq_one_iff.mp (by simpa using hgk))
    · simpa using hgk
    · exfalso
      exact hcyc (isCyclic_of_orderOf_eq_card g (by rw [hP4]; simpa using hgk))
  have : IsKleinFour ↥P := ⟨hP4, hexp⟩
  obtain ⟨e⟩ := (IsKleinFour.nonempty_mulEquiv (G₁ := ↥P) (G₂ := DihedralGroup 2))
  exact ⟨1, le_refl 1, ⟨e⟩⟩

theorem oddCore_normal_subgroup {K : Type} [Group K] [Finite K] (hO : CFSG.oddCore K = ⊥)
    (J : Subgroup K) [J.Normal] : CFSG.oddCore ↥J = ⊥ := by
  have hoddJ : Odd (Nat.card (CFSG.oddCore ↥J)) := by
    rw [CFSG.BrauerSuzuki.Helpers.odd_natCard_iff_no_involution]
    intro x hx
    have := CFSG.Adapters.odd_orderOf_of_mem_oddCore x.2
    rw [Subgroup.orderOf_coe, hx] at this
    exact absurd this (by decide)
  set L : Subgroup K := (CFSG.oddCore ↥J).map J.subtype with hL
  have hLodd : Odd (Nat.card L) := by
    rw [hL, Subgroup.card_map_of_injective J.subtype_injective]
    exact hoddJ
  have hLnormal : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨l, hl, rfl⟩ := hn
    have hmap : (CFSG.oddCore ↥J).map (MulAut.conjNormal g).toMonoidHom ≤ CFSG.oddCore ↥J := by
      refine CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore _ ?_ ?_
      · exact (inferInstance : (CFSG.oddCore ↥J).Normal).map _ (MulAut.conjNormal g).surjective
      · rw [Subgroup.card_map_of_injective (f := (MulAut.conjNormal g).toMonoidHom)
          (MulAut.conjNormal g).injective]
        exact hoddJ
    exact ⟨_, hmap ⟨l, hl, rfl⟩, by simp⟩
  have hle : L ≤ CFSG.oddCore K :=
    CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore _ hLnormal hLodd
  rw [hO] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp (le_bot_iff.mp hle)

end CFSG.Quasithin.H13.U43
