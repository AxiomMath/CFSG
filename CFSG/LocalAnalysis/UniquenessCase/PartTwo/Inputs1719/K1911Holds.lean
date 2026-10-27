module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenElevenTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911Sp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911L2U3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911SzSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem dvd_two_pow_add_one_of_int_modEq {n p : ℕ}
    (h : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : p ∣ 2 ^ n + 1 := by
  have hdvd : (p : ℤ) ∣ (2 : ℤ) ^ n + 1 := by
    have h1 : (p : ℤ) ∣ (-1 : ℤ) - (2 : ℤ) ^ n := h.dvd
    have h2 : (-1 : ℤ) - (2 : ℤ) ^ n = -((2 : ℤ) ^ n + 1) := by ring
    rw [h2] at h1
    exact dvd_neg.mp h1
  have hcast : ((2 ^ n + 1 : ℕ) : ℤ) = (2 : ℤ) ^ n + 1 := by norm_num
  rw [← hcast] at hdvd
  exact Int.natCast_dvd_natCast.mp hdvd

theorem k_19_11_torusFixed_holds : K_19_11_torusFixed := by
  unfold K_19_11_torusFixed
  intro X _ _ n p hp hshape A t hA ht hinv Q hQ hQN
  rcases hshape with hSp4 | hProd | hSz
  · obtain ⟨hX, hodd, hn1, hmod⟩ := hSp4
    have hn : 3 ≤ n := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    have hpd : p ∣ 2 ^ n + 1 := dvd_two_pow_add_one_of_int_modEq hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour.exists_mulEquiv_statedSp_of_lieModel
        hX
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (by omega) hK
    exact TorusFixedConcl.of_mulEquiv e (torusFixedConcl_sp4 hK hn hodd hp hpd)
      A t hA ht hinv Q hQ hQN
  · obtain ⟨hshape, h2n, hmod⟩ := hProd
    have hn : 3 ≤ n := by omega
    have hpd : p ∣ 2 ^ n + 1 := dvd_two_pow_add_one_of_int_modEq hmod
    rcases hshape with hsq | hu3
    · obtain ⟨A', B', _, _, ⟨e⟩, hA', hB'⟩ := hsq
      haveI : Finite (A' × B') := Finite.of_injective (⇑e.symm) e.symm.injective
      haveI : Finite A' := Finite.of_injective (fun a : A' => (a, (1 : B'))) (by
        intro a b h
        simpa using h)
      haveI : Finite B' := Finite.of_injective (fun b : B' => ((1 : A'), b)) (by
        intro a b h
        simpa using h)
      exact TorusFixedConcl.of_mulEquiv e (torusFixedConcl_l2_prod hA' hB' hn hp hpd)
        A t hA ht hinv Q hQ hQN
    · obtain ⟨hu3, hpow⟩ := hu3
      obtain ⟨A', B', _, _, ⟨e⟩, hA', hB'⟩ := hu3
      haveI : Finite (A' × B') := Finite.of_injective (⇑e.symm) e.symm.injective
      haveI : Finite A' := Finite.of_injective (fun a : A' => (a, (1 : B'))) (by
        intro a b h
        simpa using h)
      haveI : Finite B' := Finite.of_injective (fun b : B' => ((1 : A'), b)) (by
        intro a b h
        simpa using h)
      have heven : Even n := by
        obtain ⟨k, rfl⟩ := hpow
        have hk : k ≠ 0 := by
          intro hk
          rw [hk] at h2n
          norm_num at h2n
        exact (even_two : Even (2 : ℕ)).pow_of_ne_zero hk
      exact TorusFixedConcl.of_mulEquiv e
        (torusFixedConcl_l2_u3_prod hA' hB' hn heven hp hpd)
        A t hA ht hinv Q hQ hQN
  · obtain ⟨hsz, h2n, hmod⟩ := hSz
    have hpd : p ∣ 2 ^ (2 * n) + 1 := dvd_two_pow_add_one_of_int_modEq hmod
    obtain ⟨A', B', _, _, ⟨e⟩, hA', hB'⟩ := hsz
    haveI : Finite (A' × B') := Finite.of_injective (⇑e.symm) e.symm.injective
    haveI : Finite A' := Finite.of_injective (fun a : A' => (a, (1 : B'))) (by
      intro a b h
      simpa using h)
    haveI : Finite B' := Finite.of_injective (fun b : B' => ((1 : A'), b)) (by
      intro a b h
      simpa using h)
    exact TorusFixedConcl.of_mulEquiv e (torusFixedConcl_sz_prod hA' hB' hp hpd)
      A t hA ht hinv Q hQ hQN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
