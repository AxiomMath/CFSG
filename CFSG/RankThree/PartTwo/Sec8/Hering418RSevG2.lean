module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RCrit
public import CFSG.RankThree.Chevalley.G2CyclotomicTori

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem noCommute37_g2Three
    {Y : Type} [Group Y] (hY : Blueprint.ChevalleyExceptionalModel Y .G2 3 1) : NoCommute37 Y := by
  intro y z hy hz hyz
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 hY
  rw [pow_one] at hK
  have hodd : Odd (Nat.card K) := ⟨1, by omega⟩
  have hd : ((7 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1 := by
    norm_num [hK]
  obtain ⟨T, -, -, -, -, hx⟩ :=
    CFSG.RankThree.Chevalley.odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hodd
      (-1) (Or.inl rfl) 7 hd (by norm_num : Nat.Prime 7) (by norm_num : 3 < 7) (dvd_refl 7)
  have hxo : orderOf (e z) = 7 := (MulEquiv.orderOf_eq e z).trans hz
  have hcent := (hx (e z) hxo).2.2.2.1
  have hcomm : e y * e z = e z * e y := by
    rw [← map_mul, ← map_mul, hyz]
  have hmem : e y ∈ Subgroup.centralizer ({e z} : Set _) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have h3 : orderOf (e y) = 3 := (MulEquiv.orderOf_eq e y).trans hy
  have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({e z} : Set _)) hmem
  rw [h3, hcent] at hdvd
  omega

end CFSG.RankThree.PartTwo.Sec8.Hering418
