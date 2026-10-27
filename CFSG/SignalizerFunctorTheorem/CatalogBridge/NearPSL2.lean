module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearCriterion
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
import CFSG.CharacterTheory.Burnside
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Arithmetic

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem isSolvable_of_natCard_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])

theorem isSolvable_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    [Group.IsSolvable Y] : Group.IsSolvable X :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem proper_subgroup_solvable_psl2_aux
    {r e : ℕ} [Fact r.Prime] (he : e.Prime) (he2 : e ≠ 2)
    (h5 : r ≠ 5 ∧ ¬ 5 ∣ r ^ (2 * e) - 1)
    (hm1 : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField r 1)))
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField r e)))
    (hH : H ≠ ⊤) : Group.IsSolvable H := by
  have hK : Nat.card (GaloisField r e) = r ^ e := GaloisField.card r e he.ne_zero
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hHz, ⟨eD⟩⟩ | ⟨-, ⟨e4⟩⟩ | ⟨-, ⟨eS⟩⟩ | ⟨hA5, -⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, hmp, ⟨eP⟩⟩ |
      ⟨m, -, hmp, -⟩
  · exact Group.isSolvable_of_comm fun a b => hEl.toIsMulCommutative.is_comm.comm a b
  · have : CommGroup H := IsCyclic.commGroup
    infer_instance
  · have hz : NeZero z := ⟨fun h0 => by
      have hpos : 0 < Nat.card H := Nat.card_pos
      rw [hHz, h0] at hpos
      omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact isSolvable_of_mulEquiv' eD
  · have : Nat.card (alternatingGroup (Fin 4)) = 2 ^ 2 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have := isSolvable_of_natCard_two_three this
    exact isSolvable_of_mulEquiv' e4
  · have : Nat.card (Equiv.Perm (Fin 4)) = 2 ^ 3 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    have := isSolvable_of_natCard_two_three this
    exact isSolvable_of_mulEquiv' eS
  · exfalso
    rcases hA5 with h | h
    · exact h5.1 h
    · exact h5.2 h
  · have : IsMulCommutative N := hNel.toIsMulCommutative
    have hNs : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => this.is_comm.comm a b
    have : N.Normal := hN
    have : CommGroup C := IsCyclic.commGroup
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
      have hx : x ∈ N ⊔ C := hsup ▸ Subgroup.mem_top x
      have hx' : x ∈ (N : Set H) * (C : Set H) := by
        rw [← Subgroup.normal_mul]
        exact hx
      obtain ⟨n, hn, c, hc, rfl⟩ := hx'
      refine ⟨⟨c, hc⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have hQs : Group.IsSolvable (H ⧸ N) := Group.isSolvable_of_surjective hsurj
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  · rcases (Nat.dvd_prime he).mp hmp with rfl | rfl
    · have : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField r 1)) :=
        hm1
      exact isSolvable_of_mulEquiv' eP
    · exfalso
      apply hH
      refine Subgroup.eq_top_of_card_eq H ?_
      rw [Nat.card_congr eP.toEquiv]
  · exfalso
    have h2 : 2 ∣ e := (dvd_mul_right 2 m).trans hmp
    exact he2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two he).mp h2).symm

theorem three_le_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have := hp.two_le
  obtain ⟨k, hk⟩ := hodd
  omega

theorem isSolvable_psl2_galoisField_two_one :
    Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1)) := by
  have h := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even (p := 1)
    one_ne_zero
  exact isSolvable_of_natCard_two_three (a := 1) (b := 1) (by rw [h]; norm_num)

theorem isSolvable_psl2_galoisField_three_one :
    Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 1)) := by
  have h := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_three (p := 1)
    one_ne_zero
  exact isSolvable_of_natCard_two_three (a := 2) (b := 1) (by rw [h]; norm_num)

theorem proper_subgroup_solvable_psl2_even
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)))
    (hH : H ≠ ⊤) : Group.IsSolvable H :=
  proper_subgroup_solvable_psl2_aux (r := 2) hp (by rintro rfl; exact absurd hodd (by decide))
    ⟨by norm_num, CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_five_dvd hodd⟩
    isSolvable_psl2_galoisField_two_one H hH

theorem proper_subgroup_solvable_psl2_three
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)))
    (hH : H ≠ ⊤) : Group.IsSolvable H :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  proper_subgroup_solvable_psl2_aux (r := 3) hp (by rintro rfl; exact absurd hodd (by decide))
    ⟨by norm_num, CFSG.SignalizerFunctorTheorem.McBride.PSL2Three.not_five_dvd hodd⟩
    isSolvable_psl2_galoisField_three_one H hH

theorem nearPSolvable_psl2_even {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hcop : Nat.Coprime p
      (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)))) :
    signalizerNearPSolvable p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)) := by
  have h3 := three_le_of_odd_prime hp hodd
  have hK : Nat.card (GaloisField 2 p) = 2 ^ p := GaloisField.card 2 p hp.ne_zero
  have h8 : 8 ≤ 2 ^ p := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h3
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hK]; omega))
      (Or.inr (by rw [hK]; omega))
  exact nearPSolvable_of_proper_solvable hcop (Or.inl ⟨MulEquiv.refl _⟩)
    fun H hH => proper_subgroup_solvable_psl2_even hp hodd H hH

theorem nearPSolvable_psl2_three {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hcop : Nat.Coprime p
      (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)))) :
    signalizerNearPSolvable p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := three_le_of_odd_prime hp hodd
  have hK : Nat.card (GaloisField 3 p) = 3 ^ p := GaloisField.card 3 p hp.ne_zero
  have h27 : 27 ≤ 3 ^ p := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ p := Nat.pow_le_pow_right (by norm_num) h3
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hK]; omega))
      (Or.inr (by rw [hK]; omega))
  exact nearPSolvable_of_proper_solvable hcop (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))
    fun H hH => proper_subgroup_solvable_psl2_three hp hodd H hH

end CFSG.SignalizerFunctorTheorem.CatalogBridge
