module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591S
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem card_V_inf_H_le_two (h67 : R6_7 Dat) :
    Nat.card ↥(m.V ⊓ centralizer (m.Z : Set G)) ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : m.V ⊓ centralizer (m.Z : Set G) ≤ pCoreOf 2 (m.H ⊓ m.M) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact fun y hy => ⟨hy.2, CFSG.LieType.BorelTits.pCoreOf_le 2 m.M hy.1⟩
    · intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 m.M hg.2, Subgroup.le_normalizer hg.1⟩
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 m.M).to_le inf_le_left
  exact (Subgroup.card_le_of_le hle).trans (m.six15 h67).1

theorem eq_of_mem_V_inf_H (h67 : R6_7 Dat) {a b : G}
    (ha : a ∈ m.V ⊓ centralizer (m.Z : Set G)) (hb : b ∈ m.V ⊓ centralizer (m.Z : Set G))
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  have hcard := m.card_V_inf_H_le_two h67
  haveI : Fintype ↥(m.V ⊓ centralizer (m.Z : Set G)) := Fintype.ofFinite _
  have h3 : 2 < Finset.card (Finset.univ : Finset ↥(m.V ⊓ centralizer (m.Z : Set G))) := by
    rw [Finset.two_lt_card_iff]
    refine ⟨1, ⟨a, ha⟩, ⟨b, hb⟩, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro h
      exact ha1 (congrArg Subtype.val h).symm
    · intro h
      exact hb1 (congrArg Subtype.val h).symm
    · intro h
      exact hab (congrArg Subtype.val h)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h3
  omega

theorem conj_eq_of_mem_V_inf_H (h67 : R6_7 Dat) {g s : G} (hgM : g ∈ m.M)
    (hgZ : g ∈ normalizer (m.Z : Set G)) (hs : s ∈ m.V ⊓ centralizer (m.Z : Set G)) (hs1 : s ≠ 1) :
    g * s * g⁻¹ = s := by
  have hgN : g ∈ normalizer ((m.V ⊓ centralizer (m.Z : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 m.M hgM, mem_normalizer_centralizer_uc6 hgZ⟩
  have h1 : g * s * g⁻¹ ∈ m.V ⊓ centralizer (m.Z : Set G) := (mem_normalizer_iff.1 hgN s).1 hs
  have h2 : g * s * g⁻¹ ≠ 1 := by
    intro h
    apply hs1
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  exact m.eq_of_mem_V_inf_H h67 h1 hs h2 hs1

theorem false_of_inverts_and_centralizes (hr3 : m.r = 3) {u : G}
    (hinv : ∀ z ∈ m.Z, u * z * u⁻¹ = z⁻¹) (hcomm : ∀ z ∈ m.Z, u * z * u⁻¹ = z) : False := by
  have hne : m.Z ≠ ⊥ := by
    intro h
    have := m.card_Z
    rw [h, Subgroup.card_bot] at this
    have h3 : 1 < m.r := m.hr.one_lt
    omega
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
  have hzz : (z : G) * (z : G) = 1 := by
    have h1 : (z : G)⁻¹ = (z : G) := by rw [← hinv z z.2, hcomm z z.2]
    calc (z : G) * z = (z : G) * (z : G)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  have hdvd3 : orderOf (z : G) ∣ 3 := by
    rw [← hr3, ← m.card_Z]
    exact Subgroup.orderOf_dvd_natCard m.Z z.2
  have hdvd2 : orderOf (z : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hzz)
  have h1' : orderOf (z : G) = 1 := Nat.dvd_one.1 (by simpa using Nat.dvd_gcd hdvd3 hdvd2)
  exact hz1 (orderOf_eq_one_iff.1 h1')

theorem pow_odd_inverts {t : G} (ht : ∀ z ∈ m.Z, t * z * t⁻¹ = z⁻¹) {n : ℕ} (hn : Odd n) :
    ∀ z ∈ m.Z, t ^ n * z * (t ^ n)⁻¹ = z⁻¹ := by
  obtain ⟨j, rfl⟩ := hn
  intro z hz
  have hsq : ∀ w ∈ m.Z, t ^ 2 * w * (t ^ 2)⁻¹ = w := fun w hw => by
    have h2 := ht w⁻¹ (m.Z.inv_mem hw)
    rw [inv_inv] at h2
    calc t ^ 2 * w * (t ^ 2)⁻¹ = t * (t * w * t⁻¹) * t⁻¹ := by rw [pow_two]; group
      _ = t * w⁻¹ * t⁻¹ := by rw [ht w hw]
      _ = w := h2
  have hcomm : ∀ w ∈ m.Z, (t ^ 2) ^ j * w * ((t ^ 2) ^ j)⁻¹ = w := fun w hw =>
    ((show Commute (t ^ 2) w from mul_inv_eq_iff_eq_mul.1 (hsq w hw)).pow_left j).mul_inv_cancel
  calc t ^ (2 * j + 1) * z * (t ^ (2 * j + 1))⁻¹
      = (t ^ 2) ^ j * (t * z * t⁻¹) * ((t ^ 2) ^ j)⁻¹ := by group
    _ = (t ^ 2) ^ j * z⁻¹ * ((t ^ 2) ^ j)⁻¹ := by rw [ht z hz]
    _ = z⁻¹ := hcomm z⁻¹ (m.Z.inv_mem hz)

theorem exists_two_element_inverting (hr3 : m.r = 3) {t : G} (htK : t ∈ m.K)
    (ht : ∀ z ∈ m.Z, t * z * t⁻¹ = z⁻¹) :
    ∃ u ∈ m.K, (∃ k : ℕ, orderOf u = 2 ^ k) ∧ u ≠ 1 ∧ ∀ z ∈ m.Z, u * z * u⁻¹ = z⁻¹ := by
  obtain ⟨a, n, hn, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
  have hinv := m.pow_odd_inverts ht hn
  refine ⟨t ^ n, m.K.pow_mem htK n, ⟨a, ?_⟩, ?_, hinv⟩
  · rw [orderOf_pow_of_dvd hn.pos.ne' ⟨2 ^ a, by rw [hord]; ring⟩, hord]
    exact Nat.mul_div_cancel _ hn.pos
  · intro h1
    refine m.false_of_inverts_and_centralizes hr3 (u := t ^ n) hinv fun z _ => ?_
    rw [h1]
    group

theorem vtrivial_of_inverts' (hr3 : m.r = 3) (h63 : R6_3 Dat)
    (h67 : R6_7 Dat) (h69 : R6_9 Dat)
    (h619 : m.C619) (h620 : m.C620) (h621 : m.C621) (h625 : m.C625) (h632 : m.C632)
    (hKC : m.KC633) (hKN : m.KN633) (hInv : m.KInv633)
    (hex : ∃ t ∈ m.K, ∀ z ∈ m.Z, t * z * t⁻¹ = z⁻¹) : m.V ⊓ centralizer (m.Z : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨t, htK, ht⟩ := hex
  obtain ⟨t₂, ht₂K, ⟨a, ha⟩, ht₂1, ht₂⟩ := m.exists_two_element_inverting hr3 htK ht
  obtain ⟨s, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hsW : (s : G) ∈ m.V ⊓ centralizer (m.Z : Set G) := s.2
  have hs1' : (s : G) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have ht₂Z : t₂ ∈ normalizer (m.Z : Set G) :=
    mem_normalizer_of_forward_uc6 fun w hw => by rw [ht₂ w hw]; exact m.Z.inv_mem hw
  have ht₂L : t₂ ∈ normalizer (m.L : Set G) := m.normalizer_Z_le_normalizer_L ht₂Z
  have ht₂M : t₂ ∈ m.M := m.K_le_M ht₂K
  have hsN : (s : G) ∈ normalizer (m.L : Set G) := m.H_le_normalizer_L hsW.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf (s : G) = 2 ^ k := by
    have hV : IsPGroup 2 ↥(pCoreOf 2 m.M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 m.M
    have hsV : (s : G) ∈ pCoreOf 2 m.M := hsW.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hV) ⟨(s : G), hsV⟩
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  have hEfix : ∀ e ∈ m.EL, (s : G) * e * (s : G)⁻¹ * e⁻¹ ∈ m.OL := by
    intro e he
    have heM : e ∈ m.M := m.R_le_M (m.EL_le_R he)
    have heZ : e ∈ normalizer (m.Z : Set G) :=
      Subgroup.centralizer_le_normalizer (m.Z : Set G) (m.L_le_H he.2)
    have h1 := m.conj_eq_of_mem_V_inf_H h67 heM heZ hsW hs1'
    have : (s : G) * e * (s : G)⁻¹ * e⁻¹ = 1 := by
      have h2 : (s : G) * e = e * (s : G) := by
        calc (s : G) * e = (e * (s : G) * e⁻¹) * e := by rw [h1]
          _ = e * (s : G) := by group
      rw [h2]
      group
    rw [this]
    exact one_mem _
  have hR3 := m.rElt_trivial_on_Lbar h69 h619 h620 h621 h625 h632 hKC
  have ht₂E : ∀ e ∈ m.EL, t₂ * e * t₂⁻¹ * e⁻¹ ∈ m.OL :=
    fun e he => (hKN (m.K ⊓ normalizer (m.L : Set G)) inf_le_right m.EL_le_normalizer_K_inf hR3).1
      t₂ ⟨ht₂K, ht₂L⟩ e he
  have hgs := m.gl h63 h619 h620 h632 hsN ⟨k, hk⟩ hs1'
  have hgt := m.gl h63 h619 h620 h632 ht₂L ⟨a, ha⟩ ht₂1
  have hcomm := hInv (s : G) hsN t₂ ht₂L ⟨k, hk⟩ ⟨a, ha⟩ hEfix ht₂E hgs hgt
  have hst : (s : G) * t₂ = t₂ * (s : G) := by
    have h1 := m.conj_eq_of_mem_V_inf_H h67 ht₂M ht₂Z hsW hs1'
    calc (s : G) * t₂ = (t₂ * (s : G) * t₂⁻¹) * t₂ := by rw [h1]
      _ = t₂ * (s : G) := by group
  have hcm : Commute (s : G)⁻¹ t₂ := (Commute.inv_left (show Commute (s : G) t₂ from hst))
  have hu2 : ∃ j : ℕ, orderOf ((s : G)⁻¹ * t₂) = 2 ^ j := by
    have hs_pow : (s : G) ^ (2 ^ (k + a)) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hk]; exact pow_dvd_pow 2 (Nat.le_add_right k a))
    have ht_pow : t₂ ^ (2 ^ (k + a)) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [ha]; exact pow_dvd_pow 2 (Nat.le_add_left a k))
    have hpow : ((s : G)⁻¹ * t₂) ^ (2 ^ (k + a)) = 1 := by
      rw [hcm.mul_pow, inv_pow, hs_pow, ht_pow]
      simp
    have hdvd : orderOf ((s : G)⁻¹ * t₂) ∣ 2 ^ (k + a) := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  have hu1 : (s : G)⁻¹ * t₂ = 1 := by
    by_contra hu1
    exact m.gl h63 h619 h620 h632 (mul_mem (inv_mem hsN) ht₂L) hu2 hu1 hcomm
  have hteq : t₂ = (s : G) := by
    have := congrArg (fun x => (s : G) * x) hu1
    simpa using this
  refine m.false_of_inverts_and_centralizes hr3 (u := t₂) ht₂ fun z hz => ?_
  rw [hteq]
  have := mem_centralizer_iff.1 hsW.2 z hz
  calc (s : G) * z * (s : G)⁻¹ = (z * (s : G)) * (s : G)⁻¹ := by rw [← this]
    _ = z := by group

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
