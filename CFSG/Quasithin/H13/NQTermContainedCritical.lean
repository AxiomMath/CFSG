module

public import CFSG.Quasithin.H13.NQTermOddCriticalLayer

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem pCore_two_quotient_eq_bot : pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pCore 2 H)
  have hN : IsPGroup 2 ((pCore 2 (H ⧸ pCore 2 H)).comap π) :=
    (pCore_isPGroup (p := 2) (G := H ⧸ pCore 2 H)).comap_of_ker_isPGroup π
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hle : (pCore 2 (H ⧸ pCore 2 H)).comap π ≤ pCore 2 H :=
    le_sSup ⟨Subgroup.Normal.comap inferInstance π, hN⟩
  have := Subgroup.map_mono (f := π) hle
  rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self, le_bot_iff] at this

theorem contained_critical_fitting_layer_forces_exact_intersection_two_core
    (D : (r : ℕ) → Subgroup (pCore r (H ⧸ pCore 2 H)))
    (hD : ∀ r ∈ oddPrimeCoreSupport (H ⧸ pCore 2 H), IsOddCriticalDetector r (D r))
    (I : Subgroup H)
    (hI : (oddCriticalLayer (H ⧸ pCore 2 H) D).comap (QuotientGroup.mk' (pCore 2 H)) ≤ I) :
    (pCore 2 I).map I.subtype = pCore 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCore 2 H with hP
  set π := QuotientGroup.mk' P with hπ
  set Θ := oddCriticalLayer (H ⧸ P) D with hΘ
  obtain ⟨-, hdet⟩ := odd_critical_fitting_layer_detects_every_two_subgroup (H ⧸ P)
    pCore_two_quotient_eq_bot
  obtain ⟨hΘc, hΘ2, hCodd⟩ := hdet D hD
  rw [← hΘ] at hΘc hΘ2 hCodd
  have hΘn : Θ.Normal := inferInstance
  have hPI : P ≤ I := by
    intro x hx
    refine hI ?_
    change π x ∈ Θ
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact Θ.one_mem
  set Q := (pCore 2 I).map I.subtype with hQ
  have hQI : Q ≤ I := Subgroup.map_subtype_le _
  have hQ2 : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := I)).map I.subtype
  have hIQ : ∀ i ∈ I, ∀ q ∈ Q, i * q * i⁻¹ ∈ Q := by
    intro i hi q hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨⟨i, hi⟩ * q' * ⟨i, hi⟩⁻¹, (pCore_normal (p := 2) (G := I)).conj_mem q' hq' ⟨i, hi⟩, rfl⟩
  have hPQ : P ≤ Q := by
    have hPn : (P.subgroupOf I).Normal := Subgroup.Normal.subgroupOf inferInstance I
    have hP2 : IsPGroup 2 (P.subgroupOf I) :=
      (pCore_isPGroup (p := 2) (G := H)).comap_subtype
    have hle : P.subgroupOf I ≤ pCore 2 I := le_sSup ⟨hPn, hP2⟩
    intro x hx
    exact ⟨⟨x, hPI hx⟩, hle hx, rfl⟩
  have hΘI : ∀ θ ∈ Θ, ∃ i ∈ I, π i = θ := fun θ hθ => by
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective P θ
    exact ⟨i, hI hθ, rfl⟩
  have hcomm : Q.map π ≤ Subgroup.centralizer (Θ : Set (H ⧸ P)) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_iff]
    intro θ hθ
    obtain ⟨i, hi, rfl⟩ := hΘI θ hθ
    set c := π (q * i * q⁻¹ * i⁻¹) with hc
    have hcQ : c ∈ Q.map π := by
      refine ⟨q * (i * q⁻¹ * i⁻¹), Q.mul_mem hq (hIQ i hi _ (Q.inv_mem hq)), ?_⟩
      rw [hc]
      congr 1
      group
    have hcΘ : c ∈ Θ := by
      have h1 : π q * π i * (π q)⁻¹ ∈ Θ := hΘn.conj_mem _ hθ _
      have h2 : c = π q * π i * (π q)⁻¹ * (π i)⁻¹ := by rw [hc]; simp [map_mul, map_inv]
      rw [h2]
      exact Θ.mul_mem h1 (Θ.inv_mem hθ)
    have hS2 : IsPGroup 2 ((Q.map π ⊓ Θ).subgroupOf Θ) :=
      ((hQ2.map π).to_inf_left).comap_subtype
    have hSn : ((Q.map π ⊓ Θ).subgroupOf Θ).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [mem_subgroupOf] at hx ⊢
      obtain ⟨hxQ, hxΘ⟩ := hx
      refine ⟨?_, Θ.mul_mem (Θ.mul_mem g.2 hxΘ) (Θ.inv_mem g.2)⟩
      obtain ⟨j, hj, hjg⟩ := hΘI g g.2
      obtain ⟨y, hy, hyx⟩ := hxQ
      refine ⟨j * y * j⁻¹, hIQ j hj y hy, ?_⟩
      rw [map_mul, map_mul, map_inv, hjg, hyx]
      rfl
    have hSle : (Q.map π ⊓ Θ).subgroupOf Θ ≤ pCore 2 Θ := le_sSup ⟨hSn, hS2⟩
    rw [hΘ2, le_bot_iff] at hSle
    have hc1 : c = 1 := by
      have hmem : (⟨c, hcΘ⟩ : Θ) ∈ (Q.map π ⊓ Θ).subgroupOf Θ := by
        rw [mem_subgroupOf]
        exact ⟨hcQ, hcΘ⟩
      rw [hSle, mem_bot] at hmem
      exact congrArg Subtype.val hmem
    have h3 : π q * π i * (π q)⁻¹ * (π i)⁻¹ = 1 := by
      rw [← hc1, hc]
      simp [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hQbot : Q.map π = ⊥ := by
    have hdvd : Nat.card (Q.map π) ∣ Nat.card (Subgroup.centralizer (Θ : Set (H ⧸ P))) :=
      Subgroup.card_dvd_of_le hcomm
    obtain ⟨k, hk⟩ := (hQ2.map π).exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · exfalso
      rw [hk] at hdvd
      have h2 : 2 ∣ Nat.card (Subgroup.centralizer (Θ : Set (H ⧸ P))) :=
        (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hCodd) (even_iff_two_dvd.mpr h2)
  have hQP : Q ≤ P := by
    intro q hq
    have : π q ∈ Q.map π := Subgroup.mem_map_of_mem π hq
    rw [hQbot, mem_bot] at this
    exact (QuotientGroup.eq_one_iff q).mp this
  exact le_antisymm hQP hPQ

theorem contained_critical_fitting_layer_inter_two_core {G : Type*} [Group G] [Finite G]
    (H M : Subgroup G) (D : (r : ℕ) → Subgroup (pCore r (H ⧸ pCore 2 H)))
    (hD : ∀ r ∈ oddPrimeCoreSupport (H ⧸ pCore 2 H), IsOddCriticalDetector r (D r))
    (hM : ((oddCriticalLayer (H ⧸ pCore 2 H) D).comap (QuotientGroup.mk' (pCore 2 H))).map
      H.subtype ≤ M) :
    inSubgroup (pCore 2) (H ⊓ M) = inSubgroup (pCore 2) H := by
  set I : Subgroup H := M.subgroupOf H
  have hI : (oddCriticalLayer (H ⧸ pCore 2 H) D).comap (QuotientGroup.mk' (pCore 2 H)) ≤ I :=
    fun x hx => hM ⟨x, hx, rfl⟩
  have key := contained_critical_fitting_layer_forces_exact_intersection_two_core D hD I hI
  have hHM : (H ⊓ M) = I.map H.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  set e : I ≃* ↥(H ⊓ M) := (I.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hHM.symm)
  have he : ∀ x : I, ((e x : ↥(H ⊓ M)) : G) = ((x : H) : G) := fun _ => rfl
  have hcore : pCore 2 ↥(H ⊓ M) = (pCore 2 I).map e.toMonoidHom :=
    (CFSG.pCore_map_iso 2 e).symm
  unfold inSubgroup
  rw [hcore, Subgroup.map_map, ← key, Subgroup.map_map]
  congr 1

end CFSG.Quasithin.H13.NQTerm
