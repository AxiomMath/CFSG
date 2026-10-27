module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.Vol2.Ch10SecKITu

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven
open CFSG.Quasithin.H13.L34 (ListOrd pslOrd psuOrd slOrd suOrd pslOrd_listOrd psuOrd_not_listOrd
  slOrd_not_listOrd suOrd_listOrd card_of_isPSLEps3q card_of_isSLEps3)

section Alt7

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem center_eq_bot_of_isAlt (hY : IsAlt 7 Y) : Subgroup.center Y = ⊥ := by
  obtain ⟨e⟩ := hY
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center ↥A7s := Subgroup.map_center_le_center e.surjective ⟨z, hz, rfl⟩
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
    map_eq_one_iff _ e.injective] at h1
  exact (Subgroup.mem_bot).mpr h1

omit [Finite Y] in
theorem card_A7 (hY : IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) :
    Nat.card Y = 2520 ∨ Nat.card Y = 7560 := by
  rcases hY with hA | ⟨-, hc, ⟨e⟩⟩
  · obtain ⟨e⟩ := hA
    left
    rw [Nat.card_congr e.toEquiv]
    exact card_A7s
  · right
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), hc,
      Nat.card_congr e.toEquiv, card_A7s]

omit [Finite Y] in
theorem isQuasisimple_A7 (hY : IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) :
    CFSG.IsQuasisimple Y := by
  rcases hY with hA | h
  · obtain ⟨e⟩ := hA
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm C10KH.a7s_quasisimple
  · exact h.1

theorem threeRank2_A7 (hY : IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) :
    FFC.ThreeRank2 Y := by
  rcases hY with hA | ⟨-, hc, ⟨e⟩⟩
  · obtain ⟨e⟩ := hA
    exact (FFC.threeRank2_alt (by norm_num)).of_mulEquiv e.symm
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 (QuotientGroup.mk' (Subgroup.center Y)).ker := by
      rw [QuotientGroup.ker_mk']
      exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
    exact FFC.ThreeRank2.of_surjective_pgroup_ker (QuotientGroup.mk' (Subgroup.center Y))
      (QuotientGroup.mk'_surjective _) hp ((FFC.threeRank2_alt (by norm_num)).of_mulEquiv e.symm)

omit [Finite Y] in
theorem card_quot_A7 (hY : IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) {Q : Type} [Group Q]
    (π : Y →* Q) (hπ : Function.Surjective π) (hQ : ¬ Subsingleton Q) :
    Nat.card Q = 2520 ∨ Nat.card Q = 7560 := by
  have hne : π.ker ≠ ⊤ := by
    intro ht
    refine hQ ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    rw [MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top a'),
      MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top b')]
  have hle := Ch11.SecA.le_center_of_normal_ne_top (isQuasisimple_A7 hY) hne
  have hprod : Nat.card Q * Nat.card π.ker = Nat.card Y := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  rcases hY with hA | hH
  · have hk : Nat.card π.ker = 1 := by
      have h1 := Subgroup.card_dvd_of_le hle
      rw [center_eq_bot_of_isAlt hA, Subgroup.card_bot] at h1
      exact Nat.dvd_one.mp h1
    have hY' : Nat.card Y = 2520 := by
      obtain ⟨e⟩ := hA
      rw [Nat.card_congr e.toEquiv]
      exact card_A7s
    left
    rw [hk, mul_one, hY'] at hprod
    exact hprod
  · have hdvd : Nat.card π.ker ∣ 3 := by
      rw [← hH.2.1]
      exact Subgroup.card_dvd_of_le hle
    have hY' : Nat.card Y = 7560 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), hH.2.1,
        Nat.card_congr hH.2.2.some.toEquiv, card_A7s]
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · right
      rw [h1, hY'] at hprod
      omega
    · left
      rw [h3, hY'] at hprod
      omega

end Alt7

theorem not_case2_of_card {Q : Type} [Group Q] (h : Nat.card Q = 2520 ∨ Nat.card Q = 7560)
    (s : Bool) (q : ℕ) (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1)) (hQ : IsPSLEps3q s q Q) :
    False := by
  have hL : ListOrd (Nat.card Q) := by unfold ListOrd; omega
  obtain ⟨hq2, hcard⟩ := card_of_isPSLEps3q hQ
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hL h
    have h4 := pslOrd_listOrd hq2 hL
    subst h4
    simp [pslOrd] at h
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hL
    have hq3 : q % 3 = 2 := by
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      have := Int.emod_emod_of_dvd (q : ℤ) (dvd_refl (3 : ℤ))
      unfold Int.ModEq at hq
      omega
    exact psuOrd_not_listOrd hq2 hq3 hL

theorem not_isSLEps3_of_card {Q : Type} [Group Q] (h : Nat.card Q = 2520 ∨ Nat.card Q = 7560)
    (s : Bool) (q : ℕ) (hQ : IsSLEps3 s q Q) : False := by
  have hL : ListOrd (Nat.card Q) := by unfold ListOrd; omega
  obtain ⟨hq2, hcard⟩ := card_of_isSLEps3 hQ
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hL
    exact slOrd_not_listOrd hq2 hL
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hL h
    have h3 := suOrd_listOrd hq2 hL
    subst h3
    simp [suOrd] at h

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K7
