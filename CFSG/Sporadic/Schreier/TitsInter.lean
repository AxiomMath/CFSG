module

public import CFSG.Sporadic.Schreier.TitsAutD

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.ComponentClassification.OuterAutomorphisms

theorem NoOddNormal.oddCore_eq_bot {G : Type*} [Group G] (h : NoOddNormal G) :
    CFSG.oddCore G = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro N ⟨hN, hodd⟩
  exact h N hN hodd

theorem NoOddNormal.piCore_eq_bot {G : Type*} [Group G] [Finite G] (h : NoOddNormal G) :
    CFSG.piCore {p : Nat.Primes | p.val ≠ 2} G = ⊥ := by
  rw [CFSG.piCore, sSup_eq_bot]
  rintro K ⟨hK, hπ⟩
  apply h K hK
  rw [Nat.odd_iff]
  by_contra h2
  have h2' : 2 ∣ Nat.card K := Nat.dvd_of_mod_eq_zero (by omega)
  exact (hπ ⟨2, Nat.prime_two⟩ h2') rfl

theorem conj_titsD_injective :
    Function.Injective (MulAut.conj : titsD →* MulAut titsD) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcen : x ∈ Subgroup.center titsD := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut titsD => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  rw [titsD_center, Subgroup.mem_bot] at hcen
  exact hcen

theorem mem_inner_of_orderOf_two
    {u : MulAut titsD} (hu : orderOf u = 2) :
    ∃ x : titsD, orderOf x = 2 ∧ MulAut.conj x = u := by
  obtain ⟨a, rfl⟩ := titsConj_surjective u
  have ha : orderOf (a : Equiv.Perm (Fin 1755)) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective titsConj titsConj_injective a]
    exact hu
  have haD := titsA_involution_mem_D a.2 ha
  have hmem : titsConj a ∈ inner titsD := by
    rw [← map_titsConj_titsD]
    exact ⟨a, haD, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_, hx⟩
  rw [← orderOf_injective _ conj_titsD_injective x]
  change orderOf (MulAut.conj x) = 2
  rw [hx, orderOf_injective titsConj titsConj_injective a, ← Subgroup.orderOf_coe]
  exact ha

theorem noOddNormal_inter_centralizer_conj
    {Y : Subgroup (MulAut titsD)} (hY : inner titsD ≤ Y)
    {x : titsD} (hx2 : orderOf x = 2) :
    NoOddNormal ↥(Y ⊓ Subgroup.centralizer {MulAut.conj x}) := by
  intro R hR hodd
  set R' : Subgroup (MulAut titsD) := R.map (Y ⊓ Subgroup.centralizer {MulAut.conj x}).subtype
    with hR'def
  have hcardR' : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hinner : R' ≤ inner titsD := by
    intro r hr
    have h2 : orderOf (QuotientGroup.mk r : Outer titsD) ∣ 2 := by
      rw [← card_outer_titsD]
      exact orderOf_dvd_natCard _
    have hodd' : orderOf (QuotientGroup.mk r : Outer titsD) ∣ Nat.card R' :=
      (orderOf_map_dvd (QuotientGroup.mk' (inner titsD)) r).trans
        (Subgroup.orderOf_dvd_natCard R' hr)
    rw [hcardR'] at hodd'
    have h1 : orderOf (QuotientGroup.mk r : Outer titsD) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h2 hodd'
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  set R'' : Subgroup titsD := R'.comap MulAut.conj with hR''def
  have hmap : R''.map MulAut.conj = R' := by
    rw [hR''def, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hinner
  have hRC : ∀ r ∈ R', r ∈ Y ⊓ Subgroup.centralizer {MulAut.conj x} := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have hcent : R'' ≤ Subgroup.centralizer {x} := by
    intro y hy
    have h := (Subgroup.mem_inf.1 (hRC _ hy)).2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at h
    exact Subgroup.mem_centralizer_singleton_iff.2 (conj_titsD_injective h)
  have hconjC : ∀ c ∈ Subgroup.centralizer {x},
      MulAut.conj c ∈ Y ⊓ Subgroup.centralizer {MulAut.conj x} := by
    intro c hc
    refine Subgroup.mem_inf.2 ⟨hY ⟨c, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 hc]
  have hnormal : (R''.subgroupOf (Subgroup.centralizer {x})).Normal := by
    refine ⟨fun r hr c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    obtain ⟨r', hr', hr'eq⟩ := hr
    have hc := hconjC c c.2
    refine ⟨⟨_, hc⟩ * r' * ⟨_, hc⟩⁻¹, hR.conj_mem r' hr' ⟨_, hc⟩, ?_⟩
    rw [Subgroup.coe_subtype] at hr'eq
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hr'eq]
  have hcard'' : Nat.card (R''.subgroupOf (Subgroup.centralizer {x})) = Nat.card R := by
    rw [card_subgroupOf_eq hcent, ← hcardR', ← hmap,
      Subgroup.card_map_of_injective conj_titsD_injective]
  have hall := CTUC_Tits_two_involution_classes_and_centralizer_two_kernels
  have hbot := hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x hx2 _ hnormal (hcard'' ▸ hodd)
  have hR'' : R'' = ⊥ := by
    have e : (R''.subgroupOf (Subgroup.centralizer {x})).map
        (Subgroup.centralizer {x}).subtype = R'' := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hcent]
    rw [← e, hbot, Subgroup.map_bot]
  have hR'bot : R' = ⊥ := by rw [← hmap, hR'', Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 hR'bot

theorem CTUC_Tits_all_intermediate_involution_centralizers_odd_core_free :
    ∀ Y : Subgroup (MulAut titsD), inner titsD ≤ Y → ∀ u ∈ Y, orderOf u = 2 →
      u ∈ inner titsD ∧
      (∀ R : Subgroup ↥(Y ⊓ Subgroup.centralizer {u}), R.Normal → Odd (Nat.card R) → R = ⊥) ∧
      CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {u}) = ⊥ ∧
      CFSG.piCore {p : Nat.Primes | p.val ≠ 2} ↥(Y ⊓ Subgroup.centralizer {u}) = ⊥ := by
  intro Y hY u _ hu
  obtain ⟨x, hx2, rfl⟩ := mem_inner_of_orderOf_two hu
  have h := noOddNormal_inter_centralizer_conj hY hx2
  exact ⟨⟨x, rfl⟩, h, h.oddCore_eq_bot, h.piCore_eq_bot⟩

end CFSG.Sporadic.Schreier.Tits
