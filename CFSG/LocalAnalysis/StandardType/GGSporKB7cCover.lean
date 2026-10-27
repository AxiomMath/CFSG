module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCover

public section

namespace CFSG.StandardType.SporadicShape

open Subgroup CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

theorem gk7c_exists_not_dvd_nine_of_cover {Y R : Type*} [Group Y] [Finite Y] [Group R]
    {Z Y' : Subgroup Y} [(Z.subgroupOf Y').Normal] (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (hZ2 : Nat.card Z = 2) (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ P : Subgroup R, Nat.card P = 49 →
      ∃ s ∈ P, s ≠ 1 ∧ ¬ 9 ∣ Nat.card (Subgroup.centralizer ({s} : Set R)))
    {E : Subgroup Y} (hE : Nat.card E = 49) :
    ∃ y ∈ E, y ≠ 1 ∧ ¬ 9 ∣ Nat.card (Subgroup.centralizer ({y} : Set Y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q : Y' →* R := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Y'))
  have hker : ∀ g : Y', q g = 1 ↔ (g : Y) ∈ Z := by
    intro g
    show φ (QuotientGroup.mk' _ g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hEY' : ∀ e ∈ E, e ∈ Y' := fun e he =>
    mem_of_index_two_of_odd hY'
      (Odd.of_dvd_nat (by decide) (hE ▸ Subgroup.orderOf_dvd_natCard E he))
  have hEZ : ∀ g ∈ E, g ∈ Z → g = 1 := by
    intro g hgE hgZ
    have h2 : orderOf g ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard Z hgZ
    have h49 : orderOf g ∣ 49 := hE ▸ Subgroup.orderOf_dvd_natCard E hgE
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h49)
  have hEcard : Nat.card (E.subgroupOf Y' : Set Y') = 49 := by
    calc Nat.card (E.subgroupOf Y' : Set Y')
        = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY').toEquiv
      _ = 49 := hE
  have hinj : Set.InjOn q (E.subgroupOf Y' : Set Y') := by
    intro a ha b hb hab
    have h1 : q (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hZ' := (hker _).1 h1
    have hE1 : ((a * b⁻¹ : Y') : Y) ∈ E :=
      Subgroup.mem_subgroupOf.1 (mul_mem (SetLike.mem_coe.1 ha) (inv_mem (SetLike.mem_coe.1 hb)))
    have := hEZ _ hE1 hZ'
    exact mul_inv_eq_one.1 (Subtype.ext this)
  have hPcard : Nat.card ((E.subgroupOf Y').map q) = 49 := by
    have e1 : Nat.card ((E.subgroupOf Y').map q) =
        Nat.card (q '' (E.subgroupOf Y' : Set Y')) := by
      rw [← Subgroup.coe_map]
      rfl
    rw [e1, Nat.card_image_of_injOn hinj, hEcard]
  obtain ⟨s, hsP, hsne, hs9⟩ := hR ((E.subgroupOf Y').map q) hPcard
  obtain ⟨e, heE', hqes⟩ := hsP
  have hyE : (e : Y) ∈ E := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 heE')
  refine ⟨(e : Y), hyE, ?_, ?_⟩
  · intro hy1
    have he1 : e = 1 := Subtype.ext hy1
    rw [he1, map_one] at hqes
    exact hsne hqes.symm
  · intro h9
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime
      (G := centralizer ({(e : Y)} : Set Y)) 3 (n := 2) (by norm_num; exact h9)
    set T : Subgroup Y := K.map (centralizer ({(e : Y)} : Set Y)).subtype with hTdef
    have hT : Nat.card T = 9 := by
      rw [hTdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
      norm_num
    have hTC : T ≤ centralizer ({(e : Y)} : Set Y) := Subgroup.map_subtype_le K
    have hodd : ∀ t ∈ T, Odd (orderOf t) := fun t ht =>
      Odd.of_dvd_nat (by decide) (hT ▸ Subgroup.orderOf_dvd_natCard T ht)
    have hord : ∀ g : Y, g ∈ Z → g ∈ T → g = 1 := by
      intro g hgZ hgT
      have h2 : orderOf g ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard Z hgZ
      have h9' : orderOf g ∣ 9 := hT ▸ Subgroup.orderOf_dvd_natCard T hgT
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num) h2 h9')
    set T' : Subgroup R := (T.subgroupOf Y').map q with hT'def
    have hT'C : T' ≤ centralizer ({s} : Set R) := by
      rintro _ ⟨t, ht, rfl⟩
      have ht' : (t : Y) ∈ T := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 ht)
      have htc : (t : Y) * (e : Y) = (e : Y) * t :=
        (mem_centralizer_singleton_iff (G := Y)).1 (hTC ht')
      refine (mem_centralizer_singleton_iff (G := R)).2 ?_
      rw [← hqes, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext htc
    have hinjT : Set.InjOn q (T.subgroupOf Y' : Set Y') := by
      intro a ha b hb hab
      have h1 : q (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      have hZ' := (hker _).1 h1
      have hT1 : ((a * b⁻¹ : Y') : Y) ∈ T :=
        Subgroup.mem_subgroupOf.1
          (mul_mem (SetLike.mem_coe.1 ha) (inv_mem (SetLike.mem_coe.1 hb)))
      have := hord _ hZ' hT1
      exact mul_inv_eq_one.1 (Subtype.ext this)
    have hT'card : Nat.card T' = 9 := by
      have e1 : Nat.card T' = Nat.card (q '' (T.subgroupOf Y' : Set Y')) := by
        rw [hT'def, ← Subgroup.coe_map]
        rfl
      rw [e1, Nat.card_image_of_injOn hinjT, ← hT]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (fun t ht => mem_of_index_two_of_odd hY' (hodd t ht))).toEquiv
    apply hs9
    rw [← hT'card]
    exact Subgroup.card_dvd_of_le hT'C

end CFSG.StandardType.SporadicShape
