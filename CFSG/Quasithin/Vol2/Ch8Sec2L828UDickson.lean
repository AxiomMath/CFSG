module

public import CFSG.Quasithin.Background.DicksonPerfectBasic
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
public import CFSG.Quasithin.Vol2.Ch8Sec2L828USL2Card

public section

namespace CFSG.Quasithin.H13

open scoped MatrixGroups

theorem ob5_perfect_card_six_false {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (h6 : Nat.card G = 6) : False := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hdvd : 3 ∣ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, h6]
    norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  set N : Subgroup G := Subgroup.zpowers g with hN
  have hNcard : Nat.card N = 3 := by
    rw [hN, Nat.card_zpowers, hg]
  have hidx : N.index = 2 := by
    have := Subgroup.card_mul_index (H := N)
    rw [hNcard, h6] at this
    omega
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hidx
  haveI : Group.IsPerfect (G ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hQ : Nat.card (G ⧸ N) = 2 := hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (G ⧸ N) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQ]
    norm_num
  have hcyc : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (p := 2) hQ
  have hcomm : IsMulCommutative (G ⧸ N) := inferInstance
  have hsolv : Group.IsSolvable (G ⧸ N) :=
    Group.isSolvable_of_comm (fun a b => hcomm.is_comm.comm a b)
  exact Group.IsPerfect.not_isSolvable (G ⧸ N) hsolv

theorem ob5_false_of_solvable_perfect (K : Type) [Group K] [Nontrivial K] [Group.IsPerfect K]
    (hs : Group.IsSolvable K) : False :=
  Group.IsPerfect.not_isSolvable K hs

theorem ob5_perfect_SL_card (H : Subgroup ob5SL)
    [Group.IsPerfect H] (hne : H ≠ ⊥) : Nat.card H = 60 ∨ Nat.card H = 4080 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hp : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
    H.map ob5Proj with hHp
  have hinj : Function.Injective (ob5Proj : ob5SL → _) := ob5_proj_injective
  let e : H ≃* Hp := Subgroup.equivMapOfInjective H ob5Proj hinj
  have hcard : Nat.card Hp = Nat.card H := (Nat.card_congr e.toEquiv).symm
  haveI : Group.IsPerfect Hp := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  haveI : Nontrivial Hp := Function.Surjective.nontrivial (f := e.symm) e.symm.surjective
  have hD := CFSG.Quasithin.F6.dicksonPSL2_holds 2 4 (by norm_num) Hp
  rw [← hcard]
  rcases hD with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  ·
    obtain ⟨hab, -⟩ := h1
    haveI : IsMulCommutative Hp := hab.1
    exact (ob5_false_of_solvable_perfect Hp (Group.isSolvable_of_comm
      (fun a b => (inferInstance : IsMulCommutative Hp).is_comm.comm a b))).elim
  · obtain ⟨hcyc, -⟩ := h2
    haveI := hcyc
    exact (ob5_false_of_solvable_perfect Hp (Group.isSolvable_of_comm
      (fun a b => (inferInstance : IsMulCommutative Hp).is_comm.comm a b))).elim
  · obtain ⟨z, -, ⟨f⟩⟩ := h3
    haveI := CFSG.Quasithin.Dickson.isSolvable_dihedral z
    exact (ob5_false_of_solvable_perfect Hp
      (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)).elim
  · obtain ⟨-, ⟨f⟩⟩ := h4
    haveI : Group.IsSolvable (alternatingGroup (Fin 4)) :=
      alternatingGroup.isSolvable (by simp)
    exact (ob5_false_of_solvable_perfect Hp
      (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)).elim
  · obtain ⟨h16, -⟩ := h5
    norm_num at h16
  · obtain ⟨-, ⟨f⟩⟩ := h6
    left
    rw [Nat.card_congr f.toEquiv, CFSG.Quasithin.H13.NQCore.card_alternating_five']
  · obtain ⟨m, t, P, hPn, hPab, -, hPcyc, -⟩ := h7
    haveI : P.Normal := hPn
    have hPs : Group.IsSolvable P := Group.isSolvable_of_comm
      (fun a b => hPab.1.is_comm.comm a b)
    haveI := hPcyc
    have hQs : Group.IsSolvable (Hp ⧸ P) := Group.isSolvable_of_comm
      (fun a b => (inferInstance : IsMulCommutative (Hp ⧸ P)).is_comm.comm a b)
    exact (ob5_false_of_solvable_perfect Hp
      ((Group.isSolvable_iff_subgroup_quotient P).mpr ⟨hPs, hQs⟩)).elim
  · obtain ⟨m, hm, ⟨f⟩⟩ := h8
    have hm4 : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      norm_num at hm
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    rw [Nat.card_congr f.toEquiv]
    interval_cases m
    · exact (ob5_perfect_card_six_false (G := Hp) (by
        rw [Nat.card_congr f.toEquiv, CFSG.Quasithin.H13.NQCore.card_psl2_two_pow
          (by norm_num : (1 : ℕ) ≠ 0)]
        norm_num)).elim
    · rw [CFSG.Quasithin.H13.NQCore.card_psl2_two_pow (by norm_num : (2 : ℕ) ≠ 0)]
      norm_num
    · exact absurd hm (by norm_num)
    · rw [CFSG.Quasithin.H13.NQCore.card_psl2_two_pow (by norm_num : (4 : ℕ) ≠ 0)]
      norm_num
  · obtain ⟨m, hm, ⟨f⟩⟩ := h9
    have hm2 : m ≤ 2 := by
      have := Nat.le_of_dvd (by norm_num) hm
      omega
    have hm0 : m ≠ 0 := by
      rintro rfl
      norm_num at hm
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    rw [Nat.card_congr f.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
      GaloisField.card 2 m hm0]
    interval_cases m
    · exact (ob5_perfect_card_six_false (G := Hp) (by
        rw [Nat.card_congr f.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
          GaloisField.card 2 1 (by norm_num)]
        norm_num)).elim
    · norm_num

end CFSG.Quasithin.H13
