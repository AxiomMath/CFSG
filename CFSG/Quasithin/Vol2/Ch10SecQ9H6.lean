module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H3
public import CFSG.Quasithin.Vol2.Ch10SecQ9H5
public import CFSG.Quasithin.Vol2.Ch10SecQ9H1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Quasithin.Vol2.Ch11.SecA.C11P9B CFSG.Assembly.LowTwoRank

theorem card_SL_four_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_four]

noncomputable def sylow64 (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hQ : Nat.card Q = 64) : Sylow 2 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (IsPGroup.of_card (n := 6) (by rw [hQ]; norm_num)).toSylow (by
    have h := Q.card_mul_index
    rw [hQ, card_SL_four_two] at h
    have hi : Q.index = 315 := by omega
    rw [hi]
    decide)

theorem false_of_PSL34 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (F : StatedProj (StatedSL 3 K) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (ut3Proj K).map F.toMonoidHom with hQ
  have eP : ↥(ut3Proj K) ≃* ↥Q := (ut3Proj K).equivMapOfInjective F.toMonoidHom F.injective
  have hcard : Nat.card Q = 64 := by
    rw [← Nat.card_congr eP.toEquiv, card_ut3Proj, hK]
    norm_num
  have eU : ↥(uniSL 4) ≃* ↥Q := Sylow.equiv (sylow64 (uniSL 4) card_uniSL_four) (sylow64 Q hcard)
  have h1 := card_center_ut3Proj (K := K)
  rw [hK, Nat.card_congr (Subgroup.centerCongr eP).toEquiv] at h1
  have h2 : Nat.card (Subgroup.center ↥Q) ≤ 2 := by
    have := card_center_uniSL_le
    rwa [Nat.card_congr (Subgroup.centerCongr eU).toEquiv] at this
  omega

theorem factK7L4_holds : FactK7L4 := by
  intro X _ s r e hX f hf
  have := isSimpleGroup_of_isPSLEps3 hX
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_SL_four_two]; norm_num)
  have hinj := injective_of_simple f hf
  have hN : Nat.card X = 20160 := by
    rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩), card_SL_four_two]
  cases s
  · have h := card_mul_gcd_of_isPSU3 hX
    generalize r ^ e = q at h
    have hd1 : 1 ≤ Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rw [hN] at h
    obtain ⟨h1, h2⟩ := window_U hd1 hd3 h (a := 3) (b := 3) (by norm_num) (by norm_num)
    omega
  · have h := card_mul_gcd_of_isPSL3' hX
    have hd1 : 1 ≤ Nat.gcd 3 (r ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hd3 : Nat.gcd 3 (r ^ e - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rw [hN] at h
    obtain ⟨h1, h2⟩ := window_L hd1 hd3 h (a := 3) (b := 4) (by norm_num) (by norm_num)
    have hq : r ^ e = 4 := by omega
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
    exact false_of_PSL34 (hK.trans hq) (φ.symm.trans (MulEquiv.ofBijective f ⟨hinj, hf⟩))

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
