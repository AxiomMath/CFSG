module

public import CFSG.RankThree.PartOne.FIS.WRelation
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity

private theorem not_mem_of_orderOf_eq_two_of_odd_card {X : Type*} [Group X] {R : Subgroup X}
    (hRo : Odd (Nat.card R)) {x : X} (hx : orderOf x = 2) : x ∉ R := fun hxR => by
  have h := R.orderOf_dvd_natCard hxR
  rw [hx] at h
  obtain ⟨k, hk⟩ := hRo
  omega

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions) in
private theorem isThreeTranspositions_mk_image {X : Type*} [Group X] {Θ : Set X}
    (hS : Setup X Θ) {R : Subgroup X} [R.Normal] (hΘR : ∀ x ∈ Θ, x ∉ R)
    (h3 : ∀ x ∈ Θ, ∀ y ∈ Θ, orderOf ((x : X ⧸ R) * (y : X ⧸ R)) ∈ ({1, 2, 3} : Set ℕ)) :
    IsThreeTranspositions (QuotientGroup.mk' R '' Θ) := by
  have hle : ∀ x ∈ QuotientGroup.mk' R '' Θ, ∀ y ∈ QuotientGroup.mk' R '' Θ,
      orderOf (x * y) ≤ 3 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := h3 x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    omega
  refine ⟨⟨?_, (hS.oddT.image _ fun x hx h => hΘR x hx ((QuotientGroup.eq_one_iff x).mp h)).1,
    ?_, fun x hx y hy => (hle x hx y hy).trans (by norm_num), fun x hx y hy h4 => ?_⟩, hle⟩
  · rintro g _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R g
    exact ⟨g * x * g⁻¹, hS.conj_mem g hx, by simp only [map_mul, map_inv]⟩
  · rw [← MonoidHom.map_closure, hS.gen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)]
  · exfalso
    have := hle x hx y hy
    omega

open CFSG.RankThree.PartTwo.Sec7 in
private theorem localSet_mk_subset_of_commSet_subset {X : Type*} [Group X] {Θ : Set X}
    (hΘ : IsOddTransp Θ) {R : Subgroup X} [R.Normal] (hRo : Odd (Nat.card R)) {c v : X}
    (hc : c ∈ Θ) (hv : v ∈ Θ) (hcv : commSet Θ c ⊆ commSet Θ v) :
    localSet (QuotientGroup.mk' R '' Θ) (QuotientGroup.mk' R c) ⊆
      localSet (QuotientGroup.mk' R '' Θ) (QuotientGroup.mk' R v) := by
  rintro _ ⟨⟨a, ha, rfl⟩, hac, hne⟩
  have hcomm : Commute a c := by
    refine (hΘ.commute_or_odd ha hc).resolve_right fun hodd => hne ?_
    have h2 : orderOf (QuotientGroup.mk' R (a * c)) ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [map_mul, ← CFSG.Timmesfeld.commute_iff_mul_sq_eq_one]
      · exact hac
      · rw [← map_mul, hΘ.mul_self_eq_one ha, map_one]
      · rw [← map_mul, hΘ.mul_self_eq_one hc, map_one]
    have h1 : orderOf (QuotientGroup.mk' R (a * c)) = 1 :=
      (Nat.coprime_two_right.mpr
        (Odd.of_dvd_nat hodd (orderOf_map_dvd (QuotientGroup.mk' R) (a * c)))).eq_one_of_dvd h2
    rwa [orderOf_eq_one_iff, map_mul, mul_eq_one_iff_eq_inv, ← map_inv, hΘ.inv_eq hc] at h1
  obtain ⟨-, hav, hne'⟩ := hcv ⟨ha, hcomm, fun h => hne (by rw [h])⟩
  refine ⟨⟨a, ha, rfl⟩, (hav.map (QuotientGroup.mk' R)).eq, fun h => ?_⟩
  refine not_mem_of_orderOf_eq_two_of_odd_card hRo (hΘ.orderOf_mul_eq_two ha hv hne' hav) ?_
  have h' : QuotientGroup.mk' R (a * v) = 1 := by
    rw [map_mul, h, ← map_mul, hΘ.mul_self_eq_one hv, map_one]
  exact (QuotientGroup.eq_one_iff (a * v)).mp h'

theorem exists_conj_of_commSet_eq {X : Type} [Group X] [Finite X] {Θ : Set X} (hS : Setup X Θ)
    {R : Subgroup X} [R.Normal] (hRo : Odd (Nat.card R)) (hO : CFSG.oddCore (X ⧸ R) = ⊥)
    (h3 : ∀ x ∈ Θ, ∀ y ∈ Θ, orderOf ((x : X ⧸ R) * (y : X ⧸ R)) ∈ ({1, 2, 3} : Set ℕ))
    {c v : X} (hc : c ∈ Θ) (hv : v ∈ Θ) (hcv : commSet Θ c = commSet Θ v) :
    ∃ r ∈ R, r * v * r⁻¹ = c := by
  have hT := isThreeTranspositions_mk_image hS
    (fun x hx => not_mem_of_orderOf_eq_two_of_odd_card hRo (hS.oddT.orderOf_eq_two hx)) h3
  have hmem := CFSG.RankThree.PartOne.FIS.wSet_mul_mem_pCore hT ⟨v, hv, rfl⟩
    ⟨⟨c, hc, rfl⟩, (localSet_mk_subset_of_commSet_subset hS.oddT hRo hc hv hcv.subset).antisymm
      (localSet_mk_subset_of_commSet_subset hS.oddT hRo hv hc hcv.symm.subset)⟩
  have hle : CFSG.pCore 3 (X ⧸ R) ≤ CFSG.oddCore (X ⧸ R) := by
    refine le_sSup ⟨inferInstance, ?_⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 3) (G := X ⧸ R))
    rw [hn]
    exact Odd.pow ⟨1, rfl⟩
  have h1 := hle hmem
  rw [hO, Subgroup.mem_bot, ← map_mul] at h1
  have hcvR : c * v ∈ R := (QuotientGroup.eq_one_iff (c * v)).mp h1
  have hvcR : v * c ∈ R := by
    have h := R.inv_mem hcvR
    rwa [mul_inv_rev, hS.oddT.inv_eq hc, hS.oddT.inv_eq hv] at h
  obtain ⟨k, hk⟩ := Odd.of_dvd_nat hRo (R.orderOf_dvd_natCard hvcR)
  exact ⟨(v * c) ^ k, R.pow_mem hvcR k,
    conj_eq_of_odd (hS.oddT.mul_self_eq_one hv) (hS.oddT.mul_self_eq_one hc) hk⟩

end CFSG.OddTranspositions

end
