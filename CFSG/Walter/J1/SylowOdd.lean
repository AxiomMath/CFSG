module

public import CFSG.Walter.J1.Bender41

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

omit [Finite G] in
theorem commute_of_pow_of_normalizer {p : ℕ} [Fact p.Prime] {U : Subgroup G}
    (hUp : Nat.card U = p) {g : G} {k : ℕ} (hgk : g ^ p ^ k = 1)
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) : ∀ u ∈ U, g * u = u * g := by
  classical
  set V := Subgroup.zpowers g
  have hVU : V ≤ Subgroup.normalizer (U : Set G) := (Subgroup.zpowers_le).mpr hgU
  let := conjAct V U hVU
  have hVp : IsPGroup p V := by
    have hdvd : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hgk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hUp]; exact (Fact.out : p.Prime).ne_zero)
  have hmod := hVp.card_modEq_card_fixedPoints U
  rw [hUp] at hmod
  have h1 : (1 : U) ∈ MulAction.fixedPoints V U := fun v => by
    apply Subtype.ext
    change (v : G) * 1 * (v : G)⁻¹ = 1
    group
  have hle : Nat.card (MulAction.fixedPoints V U) ≤ p := by
    rw [← hUp]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hpos : 0 < Nat.card (MulAction.fixedPoints V U) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, Set.toFinite _ |>.to_subtype⟩
  have hfix : Nat.card (MulAction.fixedPoints V U) = p := by
    have hmod' := hmod
    unfold Nat.ModEq at hmod'
    rw [Nat.mod_self] at hmod'
    have hdvd : p ∣ Nat.card (MulAction.fixedPoints V U) := Nat.dvd_of_mod_eq_zero hmod'.symm
    obtain ⟨m, hm⟩ := hdvd
    rcases m with _ | _ | m
    · omega
    · omega
    · have := (Fact.out : p.Prime).pos
      nlinarith
  have hall : MulAction.fixedPoints V U = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    · rw [Set.ncard_univ, hUp, ← Nat.card_coe_set_eq, hfix]
  intro u hu
  have hu' : (⟨u, hu⟩ : U) ∈ MulAction.fixedPoints V U := hall ▸ Set.mem_univ _
  have := congrArg Subtype.val (hu' ⟨g, Subgroup.mem_zpowers g⟩)
  change g * u * g⁻¹ = u at this
  calc g * u = (g * u * g⁻¹) * g := by group
    _ = u * g := by rw [this]

include h in
theorem card_sylow_odd {p : ℕ} (hp : p = 3 ∨ p = 5) (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p := by
  have hpp := prime_of_three_or_five hp
  have : Fact p.Prime := ⟨hpp⟩
  have hpodd := odd_of_three_or_five hp
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := h.F) p (by
    rw [h.card_F]; rcases hp with rfl | rfl <;> norm_num)
  set U := (Subgroup.zpowers u).map h.F.subtype
  have hUF : U ≤ h.F := Subgroup.map_subtype_le _
  have hUp : Nat.card U = p := by
    rw [Subgroup.card_map_of_injective h.F.subtype_injective, Nat.card_zpowers, hu]
  obtain ⟨-, -, A, -, -, -, hAC, hUA, -, -, hAodd, -, hAcard⟩ := h.bender_4_1 hUF hp hUp
  have hUP2 : IsPGroup p U := IsPGroup.of_card (n := 1) (by rw [hUp, pow_one])
  obtain ⟨P', hUP'⟩ := hUP2.exists_le_sylow
  have hUeq : (P' : Subgroup G) = U := by
    refine eq_of_isPGroup_of_normalizer P'.isPGroup' hUP' fun g hgN ⟨k, hk⟩ => ?_
    by_contra hgU
    have hgC : g ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (commute_of_pow_of_normalizer hUp hk hgN v hv).symm
    have hgA : g ∈ A := hAodd g hgC (odd_orderOf_of_pow hpodd hk)
    have hZp : IsPGroup p (Subgroup.zpowers g) := by
      have hdvd : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpp).mp hdvd
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hR := IsPGroup.to_sup_of_normal_left' hUP2 hZp ((Subgroup.zpowers_le).mpr hgN)
    have hRA : U ⊔ Subgroup.zpowers g ≤ A := sup_le hUA ((Subgroup.zpowers_le).mpr hgA)
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    have hlt : p < Nat.card (U ⊔ Subgroup.zpowers g : Subgroup G) := by
      have hle : U ≤ U ⊔ Subgroup.zpowers g := le_sup_left
      have hne : U ≠ U ⊔ Subgroup.zpowers g := fun h0 =>
        hgU (h0 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
      have := Subgroup.card_le_of_le hle
      rw [hUp] at this
      refine lt_of_le_of_ne this fun h0 => hne ?_
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [← h0, hUp])
    have hp2 : p ^ 2 ∣ Nat.card A := by
      have h2 : 2 ≤ n := by
        by_contra h0
        push Not at h0
        interval_cases n
        · rw [hn, pow_zero] at hlt; exact absurd hlt (by omega)
        · rw [hn, pow_one] at hlt; exact absurd hlt (lt_irrefl _)
      exact (pow_dvd_pow p h2).trans (hn ▸ Subgroup.card_dvd_of_le hRA)
    rcases hAcard with h0 | h0 <;> rw [h0] at hp2 <;> rcases hp with rfl | rfl <;> revert hp2 <;>
      decide
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P', hUeq, hUp]

include h in
theorem exists_involution_of_card {p : ℕ} (hp : p = 3 ∨ p = 5) {X : Subgroup G}
    (hX : Nat.card X = p) : ∃ x : G, orderOf x = 2 ∧ X ≤ Subgroup.centralizer ({x} : Set G) := by
  have hpp := prime_of_three_or_five hp
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := h.F) p (by
    rw [h.card_F]; rcases hp with rfl | rfl <;> norm_num)
  set U := (Subgroup.zpowers u).map h.F.subtype
  have hUF : U ≤ h.F := Subgroup.map_subtype_le _
  have hUp : Nat.card U = p := by
    rw [Subgroup.card_map_of_injective h.F.subtype_injective, Nat.card_zpowers, hu]
  have hXS : IsPGroup p X := IsPGroup.of_card (n := 1) (by rw [hX, pow_one])
  have hUS : IsPGroup p U := IsPGroup.of_card (n := 1) (by rw [hUp, pow_one])
  obtain ⟨P, hXP⟩ := hXS.exists_le_sylow
  obtain ⟨Q, hUQ⟩ := hUS.exists_le_sylow
  have hPX : (P : Subgroup G) = X := (Subgroup.eq_of_le_of_card_ge hXP (by
    rw [h.card_sylow_odd hp P, hX])).symm
  have hQU : (Q : Subgroup G) = U := (Subgroup.eq_of_le_of_card_ge hUQ (by
    rw [h.card_sylow_odd hp Q, hUp])).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g * h.t * g⁻¹, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_t], ?_⟩
  intro x hx
  rw [← hPX, ← hg, Sylow.coe_subgroup_smul, hQU] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzt : z * h.t = h.t * z := h.commute_of_mem_F (hUF hz)
  change g * z * g⁻¹ * (g * h.t * g⁻¹) = g * h.t * g⁻¹ * (g * z * g⁻¹)
  calc g * z * g⁻¹ * (g * h.t * g⁻¹) = g * (z * h.t) * g⁻¹ := by group
    _ = g * (h.t * z) * g⁻¹ := by rw [hzt]
    _ = g * h.t * g⁻¹ * (g * z * g⁻¹) := by group

end JankoHyp

end CFSG.Walter.J1
