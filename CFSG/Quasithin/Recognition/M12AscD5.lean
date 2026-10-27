module

public import CFSG.Quasithin.Recognition.M12AscD4
public import Certificates.Certificate1950
public import CFSG.Quasithin.Recognition.M12AscD1
public import CFSG.Quasithin.Recognition.M12AscD3

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem conj_comm_of_comm {g q b : G} (hgb : g * b = b * g) (hqb : q * b = b * q) :
    (g * q * g⁻¹) * b = b * (g * q * g⁻¹) := by
  have h1 : g⁻¹ * b = b * g⁻¹ := by
    calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * b) * g⁻¹ := by rw [hgb]
      _ = b * g⁻¹ := by group
  calc g * q * g⁻¹ * b = g * q * (g⁻¹ * b) := by group
    _ = g * q * (b * g⁻¹) := by rw [h1]
    _ = g * (q * b) * g⁻¹ := by group
    _ = g * (b * q) * g⁻¹ := by rw [hqb]
    _ = (g * b) * q * g⁻¹ := by group
    _ = (b * g) * q * g⁻¹ := by rw [hgb]
    _ = b * (g * q * g⁻¹) := by group

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem mem_C {g : G} :
    g ∈ Subgroup.centralizer (c.D : Set G) ↔ ∀ d ∈ c.D, g * d = d * g := by
  rw [Subgroup.mem_centralizer_iff]
  exact ⟨fun h d hd => (h d hd).symm, fun h d hd => (h d hd).symm⟩

theorem z_mem_N : z ∈ Subgroup.normalizer (c.D : Set G) := by
  have h := (c.rho_mem_normalizer (swap 0 1)).2 (Certificates.certificate1950.1)
  rwa [c.ρ_z] at h

theorem b_mem_N : c.u' * z ∈ Subgroup.normalizer (c.D : Set G) := by
  have h := (c.rho_mem_normalizer pb).2 (Certificates.certificate1950.2.2)
  rwa [c.ρ_pb] at h

theorem conj_mem_C
    {g q : G} (hg : g ∈ Subgroup.normalizer (c.D : Set G))
    (hq : q ∈ Subgroup.centralizer (c.D : Set G)) :
    g * q * g⁻¹ ∈ Subgroup.centralizer (c.D : Set G) := by
  rw [mem_C] at hq ⊢
  intro d hd
  have hd' : g⁻¹ * d * g ∈ c.D := (Subgroup.mem_normalizer_iff''.1 hg d).1 hd
  have := hq _ hd'
  calc g * q * g⁻¹ * d = g * (q * (g⁻¹ * d * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * d * g) * q) * g⁻¹ := by rw [this]
    _ = d * (g * q * g⁻¹) := by group

theorem centralizer_D_b_trivial
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z)
    (h27 : 27 ∣ Nat.card G) {y : G} (h : OuterData c y) {q : G}
    (hq : q ∈ Subgroup.centralizer (c.D : Set G)) (hqb : (c.u' * z) * q = q * (c.u' * z)) :
    q = 1 := by
  classical
  by_contra hq1
  have hbconj := c.isConj_b hyp
  obtain ⟨mb⟩ := exists_model_of_isConj m hbconj
  have hypb := asc03Hyp_of_isConj hyp hbconj
  have hcardb : Nat.card ↥(ascH (c.u' * z)) = 192 := AscModel.card_ascH hypb
  let S : Subgroup G := Subgroup.centralizer (c.D : Set G) ⊓ ascH (c.u' * z)
  have hSodd : ∀ g ∈ S, Odd (orderOf g) := fun g hg =>
    c.odd_orderOf_of_centralizes_D hyp h27 ((mem_C c).1 hg.1)
  have hS3 : Nat.card S ∣ 3 := card_dvd_three_of_odd hcardb inf_le_right hSodd
  have hqb' : q * (c.u' * z) = (c.u' * z) * q := hqb.symm
  have hqS : q ∈ S := ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 hqb'⟩
  have hqo3 : orderOf q ∣ 3 := by
    have h1 : orderOf (⟨q, hqS⟩ : ↥S) ∣ Nat.card ↥S := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h1.trans hS3
  have hq1' : orderOf q ≠ 1 := fun e => hq1 (orderOf_eq_one_iff.1 e)
  have hqo : orderOf q = 3 := ((Nat.dvd_prime Nat.prime_three).1 hqo3).resolve_left hq1'
  have hq3' : q ^ 3 = 1 := by rw [← hqo]; exact pow_orderOf_eq_one q
  have hq3 : q * q * q = 1 := by rwa [pow_succ, pow_two] at hq3'
  have hcardz : Nat.card (zpowers q) = 3 := by rw [Nat.card_zpowers, hqo]
  have hzS : zpowers q ≤ S := (Subgroup.zpowers_le).2 hqS
  have hSz : S ≤ zpowers q := by
    have h1 : Nat.card (zpowers q) ∣ Nat.card S := Subgroup.card_dvd_of_le hzS
    have h2 : Nat.card S = 3 := Nat.dvd_antisymm hS3 (hcardz ▸ h1)
    exact (Subgroup.eq_of_le_of_card_ge hzS (by rw [h2, hcardz])).ge
  have hgN := h.g8_normalizes
  have hgb := h.g8_comm_b
  have hgqC : (c.ρ tau0 * y) * q * (c.ρ tau0 * y)⁻¹ ∈ Subgroup.centralizer (c.D : Set G) :=
    c.conj_mem_C hgN hq
  have hgqb : (c.ρ tau0 * y) * q * (c.ρ tau0 * y)⁻¹ ∈ ascH (c.u' * z) :=
    Subgroup.mem_centralizer_singleton_iff.2 (conj_comm_of_comm hgb hqb')
  have hmem : (c.ρ tau0 * y) * q * (c.ρ tau0 * y)⁻¹ ∈ zpowers q := hSz ⟨hgqC, hgqb⟩
  have hsq := sq_conj_eq_of_mem_zpowers hq3 hq1 hmem
  have hsq' : ((c.ρ tau0 * y) * (c.ρ tau0 * y)) * q = q * ((c.ρ tau0 * y) * (c.ρ tau0 * y)) := by
    calc (c.ρ tau0 * y) * (c.ρ tau0 * y) * q
        = ((c.ρ tau0 * y) * (c.ρ tau0 * y) * q * ((c.ρ tau0 * y) * (c.ρ tau0 * y))⁻¹) *
          ((c.ρ tau0 * y) * (c.ρ tau0 * y)) := by group
      _ = q * ((c.ρ tau0 * y) * (c.ρ tau0 * y)) := by rw [hsq]
  have hgg : (c.ρ tau0 * y) * (c.ρ tau0 * y) ∈ ascH (c.u' * z) := by
    apply Subgroup.mem_centralizer_singleton_iff.2
    calc (c.ρ tau0 * y) * (c.ρ tau0 * y) * (c.u' * z)
        = (c.ρ tau0 * y) * ((c.ρ tau0 * y) * (c.u' * z)) := by group
      _ = (c.ρ tau0 * y) * ((c.u' * z) * (c.ρ tau0 * y)) := by rw [hgb]
      _ = ((c.ρ tau0 * y) * (c.u' * z)) * (c.ρ tau0 * y) := by group
      _ = ((c.u' * z) * (c.ρ tau0 * y)) * (c.ρ tau0 * y) := by rw [hgb]
      _ = (c.u' * z) * ((c.ρ tau0 * y) * (c.ρ tau0 * y)) := by group
  have h6 := mb.pow6_of_comm (Subgroup.mem_centralizer_singleton_iff.2 hqb') hgg hq3' hq1 hsq'
  rw [h.g8_sq, ← map_pow] at h6
  apply omega0_pow6
  apply c.ρ_inj
  rw [h6, map_one]

theorem b_inverts_C
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G)
    {y : G} (h : OuterData c y) {q : G} (hq : q ∈ Subgroup.centralizer (c.D : Set G)) :
    (c.u' * z) * q * (c.u' * z)⁻¹ = q⁻¹ := by
  classical
  let C : Subgroup G := Subgroup.centralizer (c.D : Set G)
  have hbC : ∀ p ∈ C, (c.u' * z) * p * (c.u' * z)⁻¹ ∈ C := fun p hp => c.conj_mem_C c.b_mem_N hp
  let σ : ↥C →* ↥C := conjP C (c.u' * z) hbC
  have hσ : ∀ a, σ (σ a) = a := by
    intro a
    apply Subtype.ext
    simp only [σ, conjP_coe]
    calc (c.u' * z) * ((c.u' * z) * (a : G) * (c.u' * z)⁻¹) * (c.u' * z)⁻¹
        = ((c.u' * z) * (c.u' * z)) * (a : G) * ((c.u' * z) * (c.u' * z))⁻¹ := by group
      _ = a := by rw [c.b_sq]; group
  have hfix : ∀ a, σ a = a → a = 1 := by
    intro a ha
    have h1 : (c.u' * z) * (a : G) * (c.u' * z)⁻¹ = a := congrArg Subtype.val ha
    have hcomm : (c.u' * z) * (a : G) = (a : G) * (c.u' * z) := by
      calc (c.u' * z) * (a : G) = ((c.u' * z) * (a : G) * (c.u' * z)⁻¹) * (c.u' * z) := by group
        _ = (a : G) * (c.u' * z) := by rw [h1]
    exact Subtype.ext (c.centralizer_D_b_trivial hyp h27 h a.2 hcomm)
  have := fpf_inverts σ hσ hfix ⟨q, hq⟩
  exact congrArg Subtype.val this

end AscCox

end CFSG.Quasithin
