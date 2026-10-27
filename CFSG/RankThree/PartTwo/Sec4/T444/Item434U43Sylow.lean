module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Model
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank Matrix

abbrev SUg : Type := ↥(StatedSU 4 3 F9)

abbrev UX : Type := StatedProj (StatedSU 4 3 F9)

@[expose] noncomputable def piU : StatedSU 4 3 F9 →* UX :=
  QuotientGroup.mk' ((StatedScalars (Fin 4) F9).subgroupOf (StatedSU 4 3 F9))

theorem card_UX : Nat.card UX = 3265920 := by
  have hK : Nat.card F9 = (3 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, F9.card_eq]
    norm_num
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F9) (p := 3) (f := 1)
    (n := 4) Nat.prime_three le_rfl hK (by norm_num)
  simp only [pow_one] at h
  rw [h]
  decide

theorem factorization_three_card_UX : (3265920 : ℕ).factorization 3 = 6 := by
  have h : (3265920 : ℕ) = 3 ^ 6 * 4480 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 4480 by norm_num)]

theorem piU_eq_one_iff {g : StatedSU 4 3 F9} :
    piU g = 1 ↔ ∃ c : F9ˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F9) := by
  rw [piU, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 4) : F9ˣ →* GL (Fin 4) F9) := by
  intro c c' h
  have h1 := congrArg Units.val h
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_ofClass,
    RingHom.toMonoidHom_eq_coe] at h1
  exact Units.ext (Matrix.scalar_inj.mp h1)

theorem eq_one_of_scalar_pow {c : F9ˣ} (h : c ^ 729 = 1) : c = 1 := by
  have h8 : c ^ 8 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (c : F9) c.ne_zero
    rw [F9.card_eq] at this
    exact Units.ext (by simpa using this)
  calc c = (c ^ 8) ^ 91 * c := by rw [h8, one_pow, one_mul]
    _ = c ^ 729 := by rw [← pow_mul, ← pow_succ]
    _ = 1 := h

theorem piU_injOn_sylS (hsyl : uSylCheck = true) {x y : StatedSU 4 3 F9} (hx : x ∈ sylS)
    (hy : y ∈ sylS) (h : piU x = piU y) : x = y := by
  have hw : x⁻¹ * y ∈ sylS := sylS.mul_mem (sylS.inv_mem hx) hy
  have h1 : piU (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := piU_eq_one_iff.mp h1
  have hord : orderOf (x⁻¹ * y) ∣ 729 := by
    have := Subgroup.orderOf_dvd_natCard sylS hw
    rwa [card_sylS hsyl] at this
  have h729 : (x⁻¹ * y) ^ 729 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  have hc729 : c ^ 729 = 1 := by
    have h2 : (Matrix.GeneralLinearGroup.scalar (Fin 4) c) ^ 729 = 1 := by
      rw [hc]
      have := congrArg Subtype.val h729
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← map_pow] at h2
    exact scalar_injective (by rw [h2, map_one])
  have hc1 := eq_one_of_scalar_pow hc729
  rw [hc1, map_one] at hc
  have : x⁻¹ * y = 1 := Subtype.ext hc.symm
  exact inv_mul_eq_one.mp this

@[expose] noncomputable def sylX : Subgroup UX := sylS.map piU

theorem card_sylX (hsyl : uSylCheck = true) :
    Nat.card sylX = 3 ^ (Nat.card UX).factorization 3 := by
  have h : Nat.card sylX = Nat.card sylS := by
    have hinj : Function.Injective (piU.comp sylS.subtype) := fun a b hab =>
      Subtype.ext (piU_injOn_sylS hsyl a.2 b.2 hab)
    have hmap : sylX = (piU.comp sylS.subtype).range := by
      rw [sylX, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hmap]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h, card_sylS hsyl, card_UX, factorization_three_card_UX]
  norm_num

theorem card_map_piU_of_le (hsyl : uSylCheck = true) {H : Subgroup (StatedSU 4 3 F9)}
    (hH : H ≤ sylS) : Nat.card (H.map piU) = Nat.card H := by
  have hinj : Function.Injective (piU.comp H.subtype) := fun a b hab =>
    Subtype.ext (piU_injOn_sylS hsyl (hH a.2) (hH b.2) hab)
  have hmap : H.map piU = (piU.comp H.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem exists_conj_sylS (hsyl : uSylCheck = true) {P : Subgroup UX} (hP : IsPGroup 3 P) :
    ∃ (g : UX) (Pt : Subgroup (StatedSU 4 3 F9)), Pt ≤ sylS ∧
      P.map (MulAut.conj g).toMonoidHom = Pt.map piU := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hh⟩ := Item434AltPerm.exists_le_map_conj_of_card (card_sylX hsyl) hP
  have hle : P.map (MulAut.conj h⁻¹).toMonoidHom ≤ sylX := Item434AltPerm.map_conj_inv_le hh
  refine ⟨h⁻¹, sylS ⊓ (P.map (MulAut.conj h⁻¹).toMonoidHom).comap piU, inf_le_left, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := hle hy
    refine ⟨s, ⟨hs, ?_⟩, hsy⟩
    show piU s ∈ P.map (MulAut.conj h⁻¹).toMonoidHom
    rw [hsy]
    exact hy
  · rintro ⟨s, ⟨hs, hs'⟩, rfl⟩
    exact hs'

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
