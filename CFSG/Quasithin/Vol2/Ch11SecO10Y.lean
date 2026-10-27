module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7PrimeOrderCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup

theorem eq_bot_of_two_of_five {P : Subgroup (Perm (Fin 7))}
    (hPA : P ≤ alternatingGroup (Fin 7)) (hP : IsPGroup 2 P) {x : Perm (Fin 7)}
    (hxA : x ∈ alternatingGroup (Fin 7)) (hx5 : orderOf x = 5)
    (hxP : x ∈ normalizer (P : Set (Perm (Fin 7)))) : P = ⊥ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZP : zpowers x ≤ normalizer (P : Set (Perm (Fin 7))) := zpowers_le.2 hxP
  let _inst : MulDistribMulAction (zpowers x) P :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (zpowers x) P hZP
  have hZ5 : IsPGroup 5 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx5,
    pow_one])
  have hmod := hZ5.card_modEq_card_fixedPoints P
  set C := FixedPoints.subgroup (zpowers x) P with hC
  have hCcard : Nat.card (MulAction.fixedPoints (zpowers x) P) = Nat.card C :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk3 : k ≤ 3 := by
    by_contra h
    have h1 : 2 ^ 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have h2 : Nat.card P ∣ 2520 := by
      have := Subgroup.card_dvd_of_le hPA
      rwa [nat_card_alternatingGroup, Nat.card_fin] at this
    rw [hk] at h2
    have := h1.trans h2
    norm_num at this
  have hCd : Nat.card C ∣ 2 ^ k := hk ▸ Subgroup.card_subgroup_dvd_card C
  obtain ⟨j, hj, hjC⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hCd
  rw [hk, hCcard, hjC] at hmod
  have hjk : j = k := by
    interval_cases k <;> interval_cases j <;> first | rfl | exact absurd hmod (by decide)
  have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hjC, hjk, hk])
  have hcomm : ∀ p ∈ P, x * p = p * x := by
    intro p hp
    have h1 : (⟨p, hp⟩ : P) ∈ C := hCtop ▸ Subgroup.mem_top _
    have h2 := (FixedPoints.mem_subgroup _ _ _).1 h1 ⟨x, mem_zpowers x⟩
    have h3 : x * p * x⁻¹ = p := congrArg Subtype.val h2
    calc x * p = x * p * x⁻¹ * x := by group
      _ = p * x := by rw [h3]
  by_contra hne
  have h2P : 2 ∣ Nat.card P := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (Subgroup.eq_bot_of_card_eq P (by rw [hk, pow_zero])) hne
    · rw [hk]
      exact dvd_pow_self 2 (by omega)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 h2P
  set t' : alternatingGroup (Fin 7) := ⟨(t : Perm (Fin 7)), hPA t.2⟩ with ht'
  set x' : alternatingGroup (Fin 7) := ⟨x, hxA⟩ with hx'
  have hord : ∀ {g : alternatingGroup (Fin 7)}, orderOf g = orderOf (g : Perm (Fin 7)) :=
    fun {g} => (orderOf_injective (alternatingGroup (Fin 7)).subtype Subtype.val_injective g).symm
  have htinv : GorensteinWalter.IsInvolution t' := by
    have h1 : orderOf t' = 2 :=
      hord.trans ((orderOf_injective P.subtype Subtype.val_injective t).trans ht)
    refine ⟨fun h => ?_, by rw [← h1]; exact pow_orderOf_eq_one t'⟩
    rw [h, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hx'5 : orderOf x' = 5 := by rw [hord]; exact hx5
  refine GorensteinWalter.aSeven_no_involution_centralizes_oddP_five_seven (p := 5)
    Nat.prime_five (Or.inl rfl) (zpowers x')
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'5, pow_one])) ?_ htinv ?_
  · intro h
    have : x' = 1 := by
      have h1 : x' ∈ zpowers x' := mem_zpowers x'
      rw [h] at h1
      exact Subgroup.mem_bot.1 h1
    rw [this, orderOf_one] at hx'5
    exact absurd hx'5 (by norm_num)
  · rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hcomm t t.2)

theorem eq_bot_of_two_of_five_iso {Y : Type*} [Group Y] (e : Y ≃* alternatingGroup (Fin 7))
    {P : Subgroup Y} (hP : IsPGroup 2 P) {x : Y} (hx5 : orderOf x = 5)
    (hxP : x ∈ normalizer (P : Set Y)) : P = ⊥ := by
  set f : Y →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom with hf
  have hfi : Function.Injective f := Subtype.val_injective.comp e.injective
  have h := eq_bot_of_two_of_five (P := P.map f) (fun y ⟨p, _, hp⟩ => hp ▸ (e p).2)
    (hP.map f) (x := f x) (e x).2 (by rw [orderOf_injective f hfi]; exact hx5)
    (le_normalizer_map f ⟨x, hxP, rfl⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective P hfi).1 h

end CFSG.Quasithin.Vol2.Ch11.O10
