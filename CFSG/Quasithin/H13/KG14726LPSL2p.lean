module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726L2p
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Simplicity.Classical
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank

theorem two_dvd_card_psl2_of_odd {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num)]
  obtain ⟨r, hr⟩ := hK
  have hg : Nat.gcd 2 (Nat.card K - 1) = 2 := Nat.gcd_eq_left ⟨r, by omega⟩
  have hprod : ∏ index ∈ Finset.Icc 2 2, (Nat.card K ^ index - 1) = Nat.card K ^ 2 - 1 := by
    simp
  rw [hg, hprod, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one]
  apply Nat.dvd_div_of_mul_dvd
  refine Dvd.dvd.mul_left ⟨r * (r + 1), ?_⟩ _
  rw [hr]
  apply Nat.sub_eq_of_eq_add
  ring

theorem kg115L2pInput_holds :
    KG115L2pInput := by
  intro p X _ hp h
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
  obtain ⟨⟨hpp, -, -, -, h23⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  rw [pow_one] at hK
  have hp3 : p ≠ 3 := fun h3 => h23 (by rw [h3, pow_one])
  obtain ⟨ε, j, hε, hε1, hpj⟩ := exists_two_pow_of_fermatOrMersenne hp hp3
  have hpo : Odd p := hpp.odd_of_ne_two (ne_two_of_fermatOrMersenne hp)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hpp, hpo, le_rfl, by rw [hK, pow_one]⟩
  have hεK : (Nat.card K : ℤ) ≡ ε [ZMOD 4] := by rw [hK]; exact hε
  let e : X ≃* CFSG.GorensteinWalter.PSL2 K :=
    eT.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  refine kg115Excluded_of_involution ?_ fun t y ht hy => ?_
  · rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_psl2_of_odd (by rw [hK]; exact hpo)
  · have ht' : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
    obtain ⟨m, hm, ⟨eD⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hodd hεK hε1 ht'
    have hcard : Nat.card (centralizer ({e t} : Set (CFSG.GorensteinWalter.PSL2 K))) = 2 ^ j := by
      rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
      have : ((2 * m : ℕ) : ℤ) = 2 ^ j := by
        push_cast
        rw [hm, hK]
        exact hpj
      exact_mod_cast this
    have hy' : e y ∈ centralizer ({e t} : Set (CFSG.GorensteinWalter.PSL2 K)) :=
      mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hy])
    have hdvd := (centralizer ({e t} : Set (CFSG.GorensteinWalter.PSL2 K))).orderOf_dvd_natCard hy'
    rw [hcard, MulEquiv.orderOf_eq] at hdvd
    intro h3
    rw [h3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

end CFSG.Quasithin.H13.KG14726

end
