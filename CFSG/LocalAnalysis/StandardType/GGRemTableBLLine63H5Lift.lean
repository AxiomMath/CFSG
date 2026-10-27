module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryLift

public section

namespace CFSG.StandardType.Line63.H5

open CFSG.Assembly TableB

theorem exists_lift_of_ker_two {H P : Type*} [Group H] [Finite H] [Group P] (π : H →* P)
    (hN : IsPGroup 2 π.ker) {E₀ U₀ : Subgroup P} (hE₀ : CFSG.Open.IsElemAbelian 3 E₀)
    (hE₀r : E₀ ≤ π.range) (hU₀ : IsPGroup 2 U₀) (hU₀r : U₀ ≤ π.range) (hU₀1 : U₀ ≠ ⊥)
    (hEU : E₀ ≤ Subgroup.normalizer (U₀ : Set P)) :
    ∃ U E : Subgroup H, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set H) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = Nat.card E₀ := by
  classical
  set H' : Subgroup H := E₀.comap π with hH'
  have hNH' : π.ker ≤ H' := by
    intro n hn
    show π n ∈ E₀
    rw [show π n = 1 from hn]
    exact E₀.one_mem
  set f' : H' →* P := π.comp H'.subtype with hf'
  have hkerf' : f'.ker = π.ker.subgroupOf H' := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hrangef' : f'.range = E₀ := by
    ext y
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hy
      obtain ⟨l, rfl⟩ := hE₀r hy
      exact ⟨⟨l, hy⟩, rfl⟩
  have hindex : (π.ker.subgroupOf H').index = Nat.card E₀ := by
    rw [← hkerf', Subgroup.index_ker, hrangef']
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hN
  haveI : Finite π.range := Finite.of_surjective (π.rangeRestrict) π.rangeRestrict_surjective
  haveI : Finite E₀ := Finite.of_injective (Subgroup.inclusion hE₀r)
    (Subgroup.inclusion_injective hE₀r)
  have h3 : IsPGroup 3 E₀ := fun g => ⟨1, Subtype.ext (by simpa using hE₀.2 g g.2)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h3
  have hcardN' : Nat.card (π.ker.subgroupOf H') = 2 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH').toEquiv]
    exact ha
  have hcop : Nat.Coprime (Nat.card (π.ker.subgroupOf H')) (π.ker.subgroupOf H').index := by
    rw [hcardN', hindex, hm]
    exact Nat.Coprime.pow a m (by norm_num)
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hCcard : Nat.card C = Nat.card E₀ := by
    have h1 := hC.card_mul_card
    have h2 := Subgroup.card_mul_index (π.ker.subgroupOf H')
    rw [← hindex]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  set E : Subgroup H := C.map H'.subtype with hEdef
  have hEN : ∀ e ∈ E, π e = 1 → e = 1 := by
    rintro _ ⟨c, hc, rfl⟩ hce
    have hcN : c ∈ π.ker.subgroupOf H' := by
      rw [← hkerf']
      exact hce
    have hc1 : c ∈ π.ker.subgroupOf H' ⊓ C := ⟨hcN, hc⟩
    rw [hC.disjoint.eq_bot, Subgroup.mem_bot] at hc1
    rw [hc1]
    rfl
  have hEE' : ∀ e ∈ E, π e ∈ E₀ := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hEab : CFSG.Open.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · have hc : (x : H) * y * (x : H)⁻¹ * (y : H)⁻¹ = 1 := by
        refine hEN _ (E.mul_mem (E.mul_mem (E.mul_mem x.2 y.2) (E.inv_mem x.2)) (E.inv_mem y.2)) ?_
        have hxy := CFSG.StandardType.TableB.IsElemAbelian.comm hE₀ (hEE' _ x.2) (hEE' _ y.2)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
        group
      show (x : H) * y = y * x
      calc (x : H) * y = (x : H) * y * (x : H)⁻¹ * (y : H)⁻¹ * (y * x) := by group
        _ = y * x := by rw [hc, one_mul]
    · refine hEN _ (E.pow_mem he 3) ?_
      rw [map_pow]
      exact hE₀.2 _ (hEE' e he)
  have hEcard : Nat.card E = Nat.card E₀ := by
    rw [hEdef, Subgroup.card_map_of_injective H'.subtype_injective, hCcard]
  set U : Subgroup H := U₀.comap π with hUdef
  have hU2 : IsPGroup 2 U := hU₀.comap_of_ker_isPGroup π hN
  have hUne : U ≠ ⊥ := by
    obtain ⟨⟨u, huU⟩, hu1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU₀1
    have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
    obtain ⟨l, hl⟩ := hU₀r huU
    have hlU : l ∈ U := by
      show π l ∈ U₀
      rw [hl]
      exact huU
    have hl1 : l ≠ 1 := by
      rintro rfl
      apply hu1
      rw [← hl, map_one]
    intro h
    rw [h, Subgroup.mem_bot] at hlU
    exact hl1 hlU
  have hEU' : E ≤ Subgroup.normalizer (U : Set H) := by
    intro e he
    have hπe : π e ∈ Subgroup.normalizer (U₀ : Set P) := hEU (hEE' e he)
    rw [Subgroup.mem_normalizer_iff]
    intro l
    rw [hUdef, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hπe (π l)
  exact ⟨U, E, hUne, hU2, hEU', hEab, hEcard⟩

end CFSG.StandardType.Line63.H5

end
