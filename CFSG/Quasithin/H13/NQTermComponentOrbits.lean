module

public import CFSG.Quasithin.SteinbergBTCommutingFactorsPrimeRank
public import CFSG.Quasithin.H13.NQTermComponentPair

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup

theorem exists_odd_prime_dvd_card_of_isSimpleGroup {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hS2 : IsPGroup 2 S := by
    refine IsPGroup.of_card (n := (Nat.card S).primeFactorsList.length) ?_
    exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdS => by
      by_contra hd2
      exact hno d hd hd2 hdS
  have : Nontrivial S := IsSimpleGroup.toNontrivial
  have hZ : Nontrivial (center S) := hS2.center_nontrivial
  have hZtop : center S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
    · exfalso
      rw [h] at hZ
      exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hZ
    · exact h
  obtain ⟨a, b, hab⟩ := hnab
  apply hab
  have ha : a ∈ center S := by rw [hZtop]; exact Subgroup.mem_top a
  exact ((Subgroup.mem_center_iff.mp ha) b).symm

variable {H : Type*} [Group H] [Finite H]

theorem odd_rank_two_component_orbits_and_normalization
    (hH : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r H ≤ 2) :
    (∀ K : Subgroup H, CFSG.IsComponent K → (Set.range (CFSG.conjugate K)).ncard ≤ 2) ∧
    ∀ X : Subgroup H, (∀ D : Subgroup X, D.Normal → D.index ≠ 2) →
      ∀ K : Subgroup H, CFSG.IsComponent K → X ≤ normalizer (K : Set H) := by
  classical
  have part1 : ∀ K : Subgroup H, CFSG.IsComponent K →
      (Set.range (CFSG.conjugate K)).ncard ≤ 2 := by
    intro K hK
    have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
    obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_card_of_isSimpleGroup hK.1.2.2
    have hdvd : ∀ g : H, r ∣ Nat.card (CFSG.conjugate K g ⧸ center (CFSG.conjugate K g)) := by
      intro g
      let e : K ≃* CFSG.conjugate K g := K.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
      have hc : Nat.card (K ⧸ center K) =
          Nat.card (CFSG.conjugate K g ⧸ center (CFSG.conjugate K g)) :=
        Nat.card_congr (QuotientGroup.congr (center K) (center (CFSG.conjugate K g)) e
          (Subgroup.map_center_eq e)).toEquiv
      rw [← hc]
      exact hrd
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff).mp hlt
    obtain ⟨ga, rfl⟩ := ha
    obtain ⟨gb, rfl⟩ := hb
    obtain ⟨gc, rfl⟩ := hc
    let L : Fin 3 → Subgroup H :=
      ![CFSG.conjugate K ga, CFSG.conjugate K gb, CFSG.conjugate K gc]
    have hLc : ∀ i, ∃ g, L i = CFSG.conjugate K g := by
      intro i
      fin_cases i
      · exact ⟨ga, rfl⟩
      · exact ⟨gb, rfl⟩
      · exact ⟨gc, rfl⟩
    have hLne : ∀ i j, i ≠ j → L i ≠ L j := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [L, Ne.symm]
    have hcomm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥ := by
      intro i j hij
      obtain ⟨gi, hgi⟩ := hLc i
      obtain ⟨gj, hgj⟩ := hLc j
      rcases CFSG.LocalCores.distinct_components_commute (hgi ▸ isComponent_conjugate hK gi)
          (hgj ▸ isComponent_conjugate hK gj) with h | h
      · exact absurd h (hLne i j hij)
      · exact h
    have h3 := CFSG.Quasithin.SteinbergBT.commuting_central_quotient_factors_force_prime_rank hr
      3 L hcomm fun i => by
        obtain ⟨g, hg⟩ := hLc i
        rw [hg]
        exact hdvd g
    have := hH r hr hr2
    omega
  refine ⟨part1, fun X hX K hK => ?_⟩
  set D : Subgroup X := (normalizer (K : Set H)).subgroupOf X with hD
  have hconj : ∀ x : H, CFSG.conjugate K x⁻¹ = K.map (MulAut.conj x).toMonoidHom := by
    intro x
    rw [CFSG.conjugate, inv_inv]
  have hmapmul : ∀ a b : H, K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map, map_mul]
    rfl
  have hmemD : ∀ a b : X, a⁻¹ * b ∈ D ↔
      K.map (MulAut.conj (a : H)).toMonoidHom = K.map (MulAut.conj (b : H)).toMonoidHom := by
    intro a b
    have h1 : a⁻¹ * b ∈ D ↔ K.map (MulAut.conj ((a : H)⁻¹ * b)).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq
    rw [h1]
    constructor
    · intro h
      rw [show (b : H) = a * ((a : H)⁻¹ * b) by group, hmapmul, h]
    · intro h
      rw [hmapmul, ← h, ← hmapmul, inv_mul_cancel, map_one]
      exact Subgroup.map_id K
  let g : X ⧸ D → Set.range (CFSG.conjugate K) :=
    Quotient.lift (fun x : X => (⟨CFSG.conjugate K (x : H)⁻¹, ⟨_, rfl⟩⟩ :
      Set.range (CFSG.conjugate K))) fun a b hab => by
        apply Subtype.ext
        change CFSG.conjugate K (a : H)⁻¹ = CFSG.conjugate K (b : H)⁻¹
        rw [hconj, hconj]
        exact (hmemD a b).mp (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro u v huv
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
    rw [QuotientGroup.eq, hmemD]
    have h1 := congrArg Subtype.val huv
    change CFSG.conjugate K (a : H)⁻¹ = CFSG.conjugate K (b : H)⁻¹ at h1
    rwa [hconj, hconj] at h1
  have hidx : D.index ≤ 2 := by
    rw [Subgroup.index_eq_card]
    calc Nat.card (X ⧸ D) ≤ Nat.card (Set.range (CFSG.conjugate K)) :=
          Nat.card_le_card_of_injective g hg
      _ = (Set.range (CFSG.conjugate K)).ncard := Nat.card_coe_set_eq _
      _ ≤ 2 := part1 K hK
  have hD1 : D.index = 1 := by
    have hpos : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : D.index ≠ 2 := fun h2 => hX D (Subgroup.normal_of_index_eq_two h2) h2
    omega
  have hDtop : D = ⊤ := Subgroup.index_eq_one.mp hD1
  intro x hx
  have hxD : (⟨x, hx⟩ : X) ∈ D := by
    rw [hDtop]
    exact Subgroup.mem_top _
  exact hxD

end CFSG.Quasithin.H13.NQTerm
