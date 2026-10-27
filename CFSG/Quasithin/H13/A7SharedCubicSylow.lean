module

public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.SectionRank CFSG.Open CFSG.ShultStronglyClosedTI.MiscAlgebra

@[expose] def sixInv : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 4 5

theorem sixInv_sign : Equiv.Perm.sign sixInv = 1 := by decide +kernel

theorem sixInv_conj : ∀ v : Fin 2 → ZMod 3, sixInv * sixParam v * sixInv⁻¹ = (sixParam v)⁻¹ := by
  decide +kernel

theorem exists_inverter_sylowThreeAlt {n : ℕ} (hn : 6 ≤ n) :
    ∃ τ : alternatingGroup (Fin n), ∀ q ∈ sylowThreeAlt hn, τ * q * τ⁻¹ = q⁻¹ := by
  refine ⟨altEmbed hn ⟨sixInv, sixInv_sign⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  rw [MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  exact Subtype.ext (sixInv_conj (Multiplicative.toAdd v))

theorem card_sylow_eq_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (S : Sylow p G) {a m : ℕ} (hG : Nat.card G = p ^ a * m) (hm : ¬ p ∣ m) :
    Nat.card S = p ^ a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Sylow.card_eq_multiplicity, hG,
    Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem A7_alternating_six_seven_odd_cover_cubic_Sylow {n : ℕ} (hn : n = 6 ∨ n = 7) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (π : E →* alternatingGroup (Fin n))
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (hodd : Odd (Nat.card π.ker))
    (hC1 : π.ker ≠ ⊥) :
    Nat.card π.ker = 3 ∧ ∀ P : Sylow 3 E, Nat.card P = 27 ∧ Monoid.exponent P = 3 ∧
      (center P).map (P : Subgroup E).subtype = π.ker ∧
      ⁅(P : Subgroup E), (P : Subgroup E)⁆ = π.ker := by
  classical
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn6 : 6 ≤ n := by omega
  have hn8 : n ≤ 8 := by omega
  have hC3 : Nat.card π.ker = 3 := by
    rcases (alternating_small_odd_cover_bound (by omega) hn8 π hπ hC hodd).2 hn with h | h
    · exact absurd ((card_eq_one).1 h) hC1
    · exact h
  refine ⟨hC3, fun P => ?_⟩
  set C := π.ker with hCdef
  have hC3grp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by rw [hC3, pow_one])
  have hcentral : ∀ c ∈ C, ∀ g : E, g * c = c * g := fun c hc g =>
    (mem_center_iff.1 (hC hc) g)
  have hcube : ∀ c ∈ C, c ^ 3 = 1 := by
    intro c hc
    have h : (⟨c, hc⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
    rw [hC3] at h
    simpa using congrArg Subtype.val h
  have hE : Nat.card E = 3 * Nat.card (alternatingGroup (Fin n)) := by
    rw [card_eq_card_quotient_mul_card_subgroup C, hC3, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have hP27 : Nat.card P = 27 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin] at hE
    rcases hn with rfl | rfl
    · exact card_sylow_eq_of_card P (a := 3) (m := 40) (by rw [hE]; rfl) (by norm_num)
    · exact card_sylow_eq_of_card P (a := 3) (m := 280) (by rw [hE]; rfl) (by norm_num)
  have hCP : C ≤ (P : Subgroup E) := hC3grp.le_sylow_of_normal P
  obtain ⟨Q0, hQ0⟩ := exists_sylow_eq_sylowThreeAlt hn6 hn8
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) Q0 (P.mapSurjective hπ)
  have himage : ∀ x ∈ (P : Subgroup E), ∃ q ∈ sylowThreeAlt hn6, π x = g * q * g⁻¹ := by
    intro x hx
    have h1 : π x ∈ ((g • Q0 : Sylow 3 _) : Subgroup (alternatingGroup (Fin n))) := by
      rw [hg]
      exact ⟨x, hx, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨q, hq, hqx⟩ := h1
    refine ⟨q, hQ0 ▸ hq, ?_⟩
    rw [← hqx]
    rfl
  have hQcomm := (isElemAbelian_sylowThreeAlt hn6).1
  have hQpow := (isElemAbelian_sylowThreeAlt hn6).2
  have hder_le : ⁅(P : Subgroup E), (P : Subgroup E)⁆ ≤ C := by
    rw [commutator_le]
    intro a ha b hb
    obtain ⟨q₁, hq₁, h₁⟩ := himage a ha
    obtain ⟨q₂, hq₂, h₂⟩ := himage b hb
    rw [hCdef, MonoidHom.mem_ker, map_commutatorElement, h₁, h₂,
      commutatorElement_eq_one_iff_mul_comm]
    have hc : q₁ * q₂ = q₂ * q₁ :=
      congrArg Subtype.val (hQcomm.is_comm.comm ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩)
    calc g * q₁ * g⁻¹ * (g * q₂ * g⁻¹) = g * (q₁ * q₂) * g⁻¹ := by group
      _ = g * (q₂ * q₁) * g⁻¹ := by rw [hc]
      _ = g * q₂ * g⁻¹ * (g * q₁ * g⁻¹) := by group
  have hder : ⁅(P : Subgroup E), (P : Subgroup E)⁆ = C :=
    le_antisymm hder_le (central_sylow_transfer_derived P C hC hC3grp).1
  obtain ⟨τ0, hτ0⟩ := exists_inverter_sylowThreeAlt hn6
  have hexp : ∀ x ∈ (P : Subgroup E), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := himage x hx
    have hx3 : x ^ 3 ∈ C := by
      rw [hCdef, MonoidHom.mem_ker, map_pow, hqx, conj_pow, hQpow q hq, mul_one,
        mul_inv_cancel]
    obtain ⟨t, ht⟩ := hπ (g * τ0 * g⁻¹)
    have hc : t * x * t⁻¹ * x ∈ C := by
      rw [hCdef, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, ht, hqx]
      have h1 := hτ0 q hq
      calc g * τ0 * g⁻¹ * (g * q * g⁻¹) * (g * τ0 * g⁻¹)⁻¹ * (g * q * g⁻¹)
          = g * (τ0 * q * τ0⁻¹) * q * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    set c := t * x * t⁻¹ * x with hcdef
    have h2 : t * x * t⁻¹ = c * x⁻¹ := by rw [hcdef]; group
    have h3 : t * x ^ 3 * t⁻¹ = x ^ 3 := by
      rw [hcentral _ hx3 t, mul_inv_cancel_right]
    have h4 : x ^ 3 = (x⁻¹) ^ 3 := by
      rw [← h3, ← conj_pow, h2, (Commute.mul_pow (hcentral c hc x⁻¹).symm 3), hcube c hc,
        one_mul]
    have h4' : x ^ 3 = (x ^ 3)⁻¹ := h4.trans (inv_pow x 3)
    have h6 : x ^ 6 = 1 := by
      calc x ^ 6 = x ^ 3 * x ^ 3 := by group
        _ = x ^ 3 * (x ^ 3)⁻¹ := congrArg (x ^ 3 * ·) h4'
        _ = 1 := mul_inv_cancel _
    have h9 : x ^ 9 = 1 := by
      rw [show x ^ 9 = (x ^ 3) ^ 3 by group, hcube _ hx3]
    calc x ^ 3 = x ^ 9 * (x ^ 6)⁻¹ := by group
      _ = 1 := by rw [h9, h6, inv_one, one_mul]
  have hPexp : Monoid.exponent P = 3 := by
    have hdvd : Monoid.exponent P ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hexp x x.2)
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exfalso
      have : Subsingleton P := Monoid.exp_eq_one_iff.1 h
      have h1 := Finite.card_le_one_iff_subsingleton.2 this
      rw [hP27] at h1
      omega
    · exact h
  have hCZ : C ≤ (center P).map (P : Subgroup E).subtype := by
    intro c hc
    refine ⟨⟨c, hCP hc⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro y
    exact Subtype.ext (hcentral c hc y)
  have hnotcomm : ¬ ∀ a b : P, a * b = b * a := by
    intro h
    apply hC1
    rw [← hder, eq_bot_iff, commutator_le]
    intro a ha b hb
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)
  have hZcard : Nat.card ((center P).map (P : Subgroup E).subtype) ≤ 3 := by
    rw [card_map_of_injective (P : Subgroup E).subtype_injective]
    have hdvd : Nat.card (center P) ∣ 27 := hP27 ▸ card_subgroup_dvd_card (center P)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (P.isPGroup'.to_subgroup (center P))
    rw [hk] at hdvd ⊢
    have hk3 : k ≤ 3 := by
      rw [show (27 : ℕ) = 3 ^ 3 by norm_num] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    by_contra hlt
    push Not at hlt
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k ≤ 1 := by omega
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    apply hnotcomm
    rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
    ·
      have hq : Nat.card (P ⧸ center P) = 3 := by
        have h := card_eq_card_quotient_mul_card_subgroup (center P)
        rw [hP27, hk] at h
        omega
      have : Fact (Nat.card (P ⧸ center P)).Prime := ⟨by rw [hq]; exact Nat.prime_three⟩
      have : IsCyclic (P ⧸ center P) := isCyclic_of_prime_card rfl
      have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (center P)) (by rw [QuotientGroup.ker_mk'])
      exact fun a b => hcomm.is_comm.comm a b
    · have htop : center P = ⊤ := (card_eq_iff_eq_top _).1 (by rw [hk, hP27]; norm_num)
      intro a b
      have ha : a ∈ center P := htop ▸ mem_top a
      exact (mem_center_iff.1 ha b).symm
  have hZ : (center P).map (P : Subgroup E).subtype = C :=
    (eq_of_le_of_card_ge hCZ (by rw [hC3]; exact hZcard)).symm
  exact ⟨hP27, hPexp, hZ, hder⟩

end CFSG.Quasithin.H13.A7
