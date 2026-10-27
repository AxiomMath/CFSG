module

public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem eq_of_commute_of_widthOne (hS : Setup G D) (hW : WidthOne D) {u v : G}
    (hu : u ∈ D) (hv : v ∈ D) (hc : Commute u v) : u = v := by
  classical
  have huP : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hS.oddT.orderOf_eq_two hu, pow_one]
  have hvP : IsPGroup 2 (Subgroup.zpowers v) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hS.oddT.orderOf_eq_two hv, pow_one]
  have hcent : u ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hc.zpow_right n).symm.eq
  have hle : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hnorm : Subgroup.zpowers u ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (hle hcent)
  have hP : IsPGroup 2 ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right' (p := 2) huP hvP hnorm
  obtain ⟨S, hle⟩ := hP.exists_le_sylow
  have huS : u ∈ (S : Subgroup G) :=
    hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hvS : v ∈ (S : Subgroup G) :=
    hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp (hW S)
  have hu' : u = x := by
    have : u ∈ (D ∩ (S : Set G) : Set G) := ⟨hu, huS⟩
    rw [hx] at this
    exact Set.mem_singleton_iff.mp this
  have hv' : v = x := by
    have : v ∈ (D ∩ (S : Set G) : Set G) := ⟨hv, hvS⟩
    rw [hx] at this
    exact Set.mem_singleton_iff.mp this
  rw [hu', hv']

theorem index_oddCore_eq_two_of_widthOne (hS : Setup G D) (hW : WidthOne D) :
    (CFSG.oddCore G).index = 2 := by
  classical
  obtain ⟨d, hd⟩ := hS.nonempty
  have hd1 : d ≠ 1 := hS.oddT.ne_one hd
  have hd2 : d * d = 1 := hS.oddT.mul_self_eq_one hd
  haveI : Fintype G := Fintype.ofFinite G
  have hiso : ∀ g : G, (g * d * g⁻¹) * d = d * (g * d * g⁻¹) → g * d * g⁻¹ = d :=
    fun g hc => eq_of_commute_of_widthOne hS hW (hS.conj_mem g hd) hd hc
  obtain ⟨N, hNn, hNodd, hNz⟩ := CFSG.ZStar.glauberman_zStar G d hd1 hd2 hiso
  haveI : N.Normal := hNn
  have hNO : N ≤ CFSG.oddCore G := le_sSup ⟨hNn, hNodd⟩
  have hcentN : QuotientGroup.mk' N d ∈ Subgroup.center (G ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_eq_mk']
    refine ⟨d * g⁻¹ * d * g, ?_, ?_⟩
    · simpa [mul_assoc, hS.oddT.inv_eq hd] using N.inv_mem (hNz g⁻¹)
    · have e : (g * d) * (d * g⁻¹ * d * g) = g * (d * d) * (g⁻¹ * d * g) := by group
      rw [e, hd2, mul_one]
      group
  have hcentO : QuotientGroup.mk' (CFSG.oddCore G) d ∈
      Subgroup.center (G ⧸ CFSG.oddCore G) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore G) x
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_eq_mk']
    refine ⟨d * g⁻¹ * d * g, ?_, ?_⟩
    · exact hNO (by simpa [mul_assoc, hS.oddT.inv_eq hd] using N.inv_mem (hNz g⁻¹))
    · have e : (g * d) * (d * g⁻¹ * d * g) = g * (d * d) * (g⁻¹ * d * g) := by group
      rw [e, hd2, mul_one]
      group
  have himg : (QuotientGroup.mk' (CFSG.oddCore G)) '' D =
      {QuotientGroup.mk' (CFSG.oddCore G) d} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd hy)
      rw [Set.mem_singleton_iff]
      have hc := Subgroup.mem_center_iff.mp hcentO (QuotientGroup.mk' (CFSG.oddCore G) g)
      have hgc : QuotientGroup.mk' (CFSG.oddCore G) g * QuotientGroup.mk' (CFSG.oddCore G) d =
          QuotientGroup.mk' (CFSG.oddCore G) d * QuotientGroup.mk' (CFSG.oddCore G) g := hc
      calc QuotientGroup.mk' (CFSG.oddCore G) (g * d * g⁻¹)
          = QuotientGroup.mk' (CFSG.oddCore G) g * QuotientGroup.mk' (CFSG.oddCore G) d *
              (QuotientGroup.mk' (CFSG.oddCore G) g)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = QuotientGroup.mk' (CFSG.oddCore G) d := by rw [hgc]; group
    · rintro rfl
      exact ⟨d, hd, rfl⟩
  have htop : (⊤ : Subgroup (G ⧸ CFSG.oddCore G)) =
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore G) d) := by
    rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' (CFSG.oddCore G))
      (QuotientGroup.mk'_surjective (CFSG.oddCore G)), ← hS.gen, MonoidHom.map_closure, himg]
    exact (Subgroup.zpowers_eq_closure _).symm
  have hord : orderOf (QuotientGroup.mk' (CFSG.oddCore G) d) = 2 := by
    rw [orderOf_eq_prime_iff]
    refine ⟨?_, ?_⟩
    · rw [pow_two, ← map_mul, hd2, map_one]
    · intro h
      have hdO : d ∈ CFSG.oddCore G := by
        rw [← QuotientGroup.eq_one_iff]
        exact h
      have h2dvd : 2 ∣ Nat.card (CFSG.oddCore G) := by
        have h := Subgroup.orderOf_dvd_natCard (CFSG.oddCore G) hdO
        rwa [hS.oddT.orderOf_eq_two hd] at h
      have hoddO : Odd (Nat.card (CFSG.oddCore G)) := by
        have h : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
          rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore]
        rw [h]
        exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
      exact (Nat.not_even_iff_odd.mpr hoddO) (even_iff_two_dvd.mpr h2dvd)
  have hcard : Nat.card (G ⧸ CFSG.oddCore G) = 2 := by
    calc Nat.card (G ⧸ CFSG.oddCore G)
        = Nat.card (⊤ : Subgroup (G ⧸ CFSG.oddCore G)) :=
            (Subgroup.card_top (G := G ⧸ CFSG.oddCore G)).symm
      _ = Nat.card (Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore G) d)) := by rw [htop]
      _ = orderOf (QuotientGroup.mk' (CFSG.oddCore G) d) := Nat.card_zpowers _
      _ = 2 := hord
  simpa [Subgroup.index] using hcard

end CFSG.OddTranspositions
