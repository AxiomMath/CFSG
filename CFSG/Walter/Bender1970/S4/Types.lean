module

public import CFSG.Walter.Bender1970.S38.Component

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

theorem not_isTypeL2Odd_of_isTypeJR {X : Type} [Group X] [Finite X] (hX : IsTypeJR X) :
    ¬ IsTypeL2Odd X := by
  rintro ⟨p, f, hp, hpodd, hf, -, h8, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S'⟩ : Nonempty (Sylow 2 PSL(2, GaloisField p f)) := inferInstance
  have h4 : Nat.card (S' : Subgroup PSL(2, GaloisField p f)) = 4 :=
    (psl2_odd_sylow_two_isKleinFour hpodd hf h8 S').card_four
  have hcard : Nat.card X = Nat.card PSL(2, GaloisField p f) := Nat.card_congr e.toEquiv
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hS : Nat.card (S : Subgroup X) = Nat.card (S' : Subgroup PSL(2, GaloisField p f)) := by
    rw [S.card_eq_multiplicity, S'.card_eq_multiplicity, hcard]
  have h2 : 2 ∣ Nat.card X := by
    rw [hcard]
    exact (show 2 ∣ 4 by norm_num).trans (h4 ▸ Subgroup.card_subgroup_dvd_card _)
  have h8' := (hX.sylow_two h2 S).2
  omega

theorem not_isTypeL2Even_of_isTypeJR {X : Type} [Group X] [Finite X] (hX : IsTypeJR X) :
    ¬ IsTypeL2Even X := by
  rintro ⟨f, hf, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U⟩ : Nonempty (Sylow 2 PSL(2, GaloisField 2 f)) := inferInstance
  obtain ⟨hUel, hUcard⟩ := psl2_even_sylow_two hf U
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ (U : Subgroup PSL(2, GaloisField 2 f)), u ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : (U : Subgroup PSL(2, GaloisField 2 f)) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at hUcard
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hu : orderOf u = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := (U : Subgroup PSL(2, GaloisField 2 f))) u huU) hu1
  set t := e.symm u with htdef
  have ht : orderOf t = 2 := by rw [htdef, MulEquiv.orderOf_eq, hu]
  have hCU := psl2_even_centralizer_involution hf U huU hu1
  have hC : ∀ a ∈ Subgroup.centralizer ({t} : Set X), ∀ b ∈ Subgroup.centralizer ({t} : Set X),
      a * b = b * a := by
    have hmem : ∀ a ∈ Subgroup.centralizer ({t} : Set X), e a ∈ (U : Subgroup _) := by
      intro a ha
      rw [← hCU, Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp ha
      have h2 := congrArg e h1
      rwa [map_mul, map_mul, htdef, MulEquiv.apply_symm_apply] at h2
    intro a ha b hb
    apply e.injective
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨e a, hmem a ha⟩
      ⟨e b, hmem b hb⟩)
  obtain ⟨-, p, f', hp, L, -, hf', h5, hLC, -, ⟨eL⟩, -⟩ := hX.2.2 t ht
  obtain ⟨a, b, hab⟩ :=
    exists_mul_ne_mul_of_mulEquiv_psl2 (by rw [GaloisField.card p f' hf'.ne']; omega) eL
  exact hab (Subtype.ext (hC _ (hLC a.2) _ (hLC b.2)))

section Conj

variable {G : Type} [Group G]

theorem IsTypeL2Odd.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsTypeL2Odd A) : IsTypeL2Odd B := by
  obtain ⟨p, f, hp, hpodd, hf, h5, h8, ⟨φ⟩⟩ := h
  exact ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e.symm.trans φ⟩⟩

theorem IsTypeL2Even.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsTypeL2Even A) : IsTypeL2Even B := by
  obtain ⟨f, hf, ⟨φ⟩⟩ := h
  exact ⟨f, hf, ⟨e.symm.trans φ⟩⟩

theorem nonempty_quotientCenter_map_conj (K : Subgroup G) (g : G) :
    Nonempty (K ⧸ Subgroup.center K ≃* (K.map (MulAut.conj g).toMonoidHom) ⧸
      Subgroup.center (K.map (MulAut.conj g).toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (K.equivMapOfInjective _ (MulAut.conj g).injective)
    (Subgroup.map_center_eq _)⟩

theorem isTypeL2Odd_map_conj_iff (K : Subgroup G) (g : G) :
    IsTypeL2Odd ((K.map (MulAut.conj g).toMonoidHom) ⧸
      Subgroup.center (K.map (MulAut.conj g).toMonoidHom)) ↔
      IsTypeL2Odd (K ⧸ Subgroup.center K) := by
  obtain ⟨e⟩ := nonempty_quotientCenter_map_conj K g
  exact ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTypeL2Even_map_conj_iff (K : Subgroup G) (g : G) :
    IsTypeL2Even ((K.map (MulAut.conj g).toMonoidHom) ⧸
      Subgroup.center (K.map (MulAut.conj g).toMonoidHom)) ↔
      IsTypeL2Even (K ⧸ Subgroup.center K) := by
  obtain ⟨e⟩ := nonempty_quotientCenter_map_conj K g
  exact ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTypeJR_map_conj_iff [Finite G] (K : Subgroup G) (g : G) :
    IsTypeJR ((K.map (MulAut.conj g).toMonoidHom) ⧸
      Subgroup.center (K.map (MulAut.conj g).toMonoidHom)) ↔
      IsTypeJR (K ⧸ Subgroup.center K) := by
  obtain ⟨e⟩ := nonempty_quotientCenter_map_conj K g
  exact ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end Conj

variable {G : Type} [Group G] [Finite G]

theorem card_inf_eq_eight_of_isTypeJR
    {H K : Subgroup G} (hHA : IsAStar H)
    (hK : IsComponentOf K H) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (hTab : IsMulCommutative (T : Subgroup G)) (hJR : IsTypeJR (K ⧸ Subgroup.center K)) :
    Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKQ := bender38Component hHA hK T hTH hTab
  rw [hKQ.card_eq]
  have h2 : 2 ∣ Nat.card (K ⧸ Subgroup.center K) :=
    hJR.two_dvd_card (IsQuasisimple.exists_mul_ne_mul hK.2.2)
  obtain ⟨S⟩ : Nonempty (Sylow 2 (K ⧸ Subgroup.center K)) := inferInstance
  have h8 := (hJR.sylow_two h2 S).2
  rw [S.card_eq_multiplicity] at h8
  have hZ : (Nat.card (Subgroup.center K)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h =>
      (Nat.not_even_iff_odd.mpr hKQ.odd_center) (even_iff_two_dvd.mpr h)
  have hK' : (Nat.card K).factorization 2 =
      (Nat.card (K ⧸ Subgroup.center K)).factorization 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K),
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hZ, add_zero]
  rw [hK', h8]

end CFSG.Walter
