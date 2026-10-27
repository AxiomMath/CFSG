module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLattice
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthNs OrthExc OrthExcEven

private theorem ggKGOe_two_dvd_card_of_char_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card K := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self 2 f.pos.ne'

theorem ggKGOrth_two_dvd_card_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 4 ≤ m) : 2 ∣ Nat.card (OrthRest.RPlus K m) := by
  have h2K : (2 : ℤ) ∣ (Nat.card K : ℤ) := by
    exact_mod_cast ggKGOe_two_dvd_card_of_char_two (K := K)
  have hqpow : (2 : ℤ) ∣ (Nat.card K : ℤ) ^ (m * (m - 1)) :=
    h2K.trans (dvd_pow_self (Nat.card K : ℤ)
      (Nat.mul_ne_zero (by omega) (by omega)))
  have hdvd : (2 : ℤ) ∣ (Nat.card (OrthRest.RPlus K m) : ℤ) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus
      (K := K) (n := m) hm]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hqpow _) _
  exact_mod_cast hdvd

theorem ggKGOrth_two_dvd_card_minus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) (b c : K) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    2 ∣ Nat.card (OrthRest.RMinus K m b c) := by
  have hQ : ∀ v : LargeEvenMinusIdx m → K,
      LargeEvenQMinus m b c v =
        CFSG.Open.StatedQuadMinus (m + 1) K b c
          (v ∘ (Equiv.sumAssoc (Fin m) (Fin m) (Fin 2)).symm) := by
    intro v
    rw [show LargeEvenQMinus m b c =
      CFSG.Assembly.ComponentType.quadMinus (m + 1) (K := K) b c from rfl]
    exact CFSG.ComponentClassification.ClassicalModelStatedBridge.quadMinus_eq_comp
      (m + 1) (K := K) b c v
  let e := Equiv.sumAssoc (Fin m) (Fin m) (Fin 2)
  have hiso : CFSG.Open.StatedProj (CFSG.Open.StatedOmega (LargeEvenQMinus m b c)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadMinus (m + 1) K b c)) :=
    (CFSG.Open.StatedAPI.mapMkEquivStatedProj
      (CFSG.Open.StatedOmega (LargeEvenQMinus m b c))).symm.trans
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.omegaModelEquivOfReindex e hQ)
  have hcard : Nat.card (OrthRest.RMinus K m b c) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadMinus (m + 1) K b c))) :=
    Nat.card_congr hiso.toEquiv
  have h2K : (2 : ℤ) ∣ (Nat.card K : ℤ) := by
    exact_mod_cast ggKGOe_two_dvd_card_of_char_two (K := K)
  have hqpow : (2 : ℤ) ∣ (Nat.card K : ℤ) ^ ((m + 1) * ((m + 1) - 1)) :=
    h2K.trans (dvd_pow_self (Nat.card K : ℤ)
      (Nat.mul_ne_zero (by omega) (by omega)))
  have hcardStated := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
    (K := K) (n := m + 1) (b := b) (c := c) (by omega) hbc
  have hdvd : (2 : ℤ) ∣
      (Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadMinus (m + 1) K b c))) : ℤ) := by
    rw [hcardStated]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hqpow _) _
  rw [hcard]
  exact_mod_cast hdvd

theorem ggKGTwoOn_orth :
    GGKGTwoOn fun _ lab => (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  have hdvd := ggKG_dvd_of_lattice hp hl
  have hp2 : p ≠ 2 := by
    rcases hdvd with h | h
    · exact ne_two_of_dvd_two_pow_sub_one hn h
    · exact TableBU.ne_two_of_dvd_two_pow_add_one hn h
  obtain ⟨htag, hl4⟩ := hs
  dsimp only at htag hl4 hdvd
  rcases htag with rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have := charP_two_of_card hK
      obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
      refine ⟨K, inferInstance, inferInstance, hK, hQ', 0,
        TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus (by omega)), ?_⟩
      rcases hdvd with h | h
      · exact ggTorusLattice_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
          (ggOrthEvenTorusInput_holds.1 K l p hl4 hp (Or.inl (by rw [hK]; exact h)))
      · by_cases hev : Even l
        · exact ggTorusLattice_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
            (ggOrthEvenTorusInput_holds.1 K l p hl4 hp (Or.inr ⟨hev, by rw [hK]; exact h⟩))
        · have hlo : Odd l := Nat.not_even_iff_odd.mp hev
          have h5 : 5 ≤ l := by
            obtain ⟨j, hj⟩ := hlo
            omega
          exact ggTorusLattice_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp
            (ggOrthSignedTorusInput_holds.1 K l p h5 hlo hp (by rw [hK]; exact h))
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
      have := charP_two_of_card hK
      obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ l - 1) hbc
      refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0,
        TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus (by omega) b c hbc), ?_⟩
      rcases hdvd with h | h
      · exact ggTorusLattice_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp
          (ggOrthSignedTorusInput_holds.2 K (l - 1) p b c (by omega) hbc hp
            (Or.inl (by rw [hK]; exact h)))
      · by_cases hev : Even (l - 1)
        · have hm4 : 4 ≤ l - 1 := by
            obtain ⟨j, hj⟩ := hev
            omega
          exact ggTorusLattice_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
            (ggOrthEvenTorusInput_holds.2 K (l - 1) p b c hm4 hev hbc hp (by rw [hK]; exact h))
        · exact ggTorusLattice_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp
            (ggOrthSignedTorusInput_holds.2 K (l - 1) p b c (by omega) hbc hp
              (Or.inr ⟨Nat.not_even_iff_odd.mp hev, by rw [hK]; exact h⟩))

end CFSG.StandardType
