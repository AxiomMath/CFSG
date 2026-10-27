module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A7Aut
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.E6.Alt.A7

open Equiv Equiv.Perm CFSG.Quasithin.E6.Bar

theorem mem_fixedSub_cj (σ : Perm (Fin 7)) (g : G7) :
    g ∈ fixedSub (cj σ) ↔ σ * (g : Perm (Fin 7)) = (g : Perm (Fin 7)) * σ := by
  rw [mem_fixedSub]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rw [cj_apply, mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro h
    apply Subtype.ext
    rw [cj_apply, h, mul_inv_cancel_right]

theorem pa_eq_swaps : pa = swap 0 2 * swap 1 3 :=
  toT_injective (by rw [toT_pa]; decide +kernel)

theorem pab_eq_swaps : pa * pb = swap 0 2 * swap 1 3 * swap 4 5 :=
  toT_injective (by rw [toT_mul, toT_pa, toT_pb]; decide +kernel)

theorem cycleType_pa : pa.cycleType = {2, 2} := by
  rw [pa_eq_swaps, Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)]

theorem cycleType_pab : (pa * pb).cycleType = {2, 2, 2} := by
  rw [pab_eq_swaps]
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 7) 2 * swap 1 3) (swap 4 5) :=
    Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
  rw [hd.cycleType_mul, Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide),
    Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))]
  rfl

theorem card_centralizer_pa :
    Nat.card ↥(Subgroup.centralizer ({pa} : Set (Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_pa]
  simp
  decide

theorem card_centralizer_pab :
    Nat.card ↥(Subgroup.centralizer ({pa * pb} : Set (Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_pab]
  simp
  decide

theorem card_fixedSub_dvd (σ : Perm (Fin 7)) :
    Nat.card ↥(fixedSub (cj σ)) ∣ Nat.card ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin 7)))) := by
  let f : ↥(fixedSub (cj σ)) →* ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin 7)))) :=
    ((alternatingGroup (Fin 7)).subtype.comp (fixedSub (cj σ)).subtype).codRestrict _ (fun g => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((mem_fixedSub_cj σ g.1).1 g.2).symm)
  refine Subgroup.card_dvd_of_injective f fun a b hab => ?_
  have : ((a : G7) : Perm (Fin 7)) = ((b : G7) : Perm (Fin 7)) :=
    congrArg (fun x : ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin 7)))) => (x : Perm (Fin 7))) hab
  exact Subtype.ext (Subtype.ext this)

theorem exists_pow_two_pow_three_of_dvd_48 {d : ℕ} (h : d ∣ 48) :
    ∃ a b : ℕ, d = 2 ^ a * 3 ^ b := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.1 (show d ∣ 2 ^ 4 * 3 ^ 1 from h)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  exact ⟨a, b, rfl⟩

theorem isSolvable_of_card_dvd_48 {X : Type} [Group X] [Finite X] (h : Nat.card X ∣ 48) :
    Group.IsSolvable X := by
  obtain ⟨a, b, hab⟩ := exists_pow_two_pow_three_of_dvd_48 h
  have := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hab])

theorem isSolvable_fixedSub_pa : Group.IsSolvable ↥(fixedSub (cj pa)) :=
  isSolvable_of_card_dvd_48 (card_centralizer_pa ▸ card_fixedSub_dvd pa)

theorem isSolvable_fixedSub_pab : Group.IsSolvable ↥(fixedSub (cj (pa * pb))) :=
  isSolvable_of_card_dvd_48 (card_centralizer_pab ▸ card_fixedSub_dvd (pa * pb))

end CFSG.Quasithin.E6.Alt.A7
