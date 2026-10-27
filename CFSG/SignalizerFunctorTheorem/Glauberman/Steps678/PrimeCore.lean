module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.LocalAnalysis.SignalizerFunctor.LocalSylowIntersections

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem primeCoreIn_le (π : Set ℕ) (H : Subgroup G) : primeCoreIn π H ≤ H :=
  Subgroup.map_subtype_le _

theorem le_normalizer_primeCoreIn (π : Set ℕ) {B H : Subgroup G}
    (h : B ≤ Subgroup.normalizer (H : Set G)) :
    B ≤ Subgroup.normalizer (primeCoreIn π H : Set G) := by
  let _ := prime_set_core_characteristic (GroupType := H) π
  exact characteristic_subgroup_map_normalized B H h (primeSetCore (GroupType := H) π)

theorem primeSupported_primeCoreIn (π : Set ℕ) (H : Subgroup G) :
    primeSupported π (Nat.card (primeCoreIn π H)) := by
  have hcard : Nat.card (primeCoreIn π H) = Nat.card (primeSetCore (GroupType := H) π) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [hcard]
  exact prime_set_core_supported π

omit [Finite G] in
theorem le_primeCoreIn {π : Set ℕ} {N H : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hπ : primeSupported π (Nat.card N)) :
    N ≤ primeCoreIn π H := by
  have hnormal : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hsupp : primeSupported π (Nat.card (N.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hπ
  have h1 : N.subgroupOf H ≤ primeSetCore (GroupType := H) π :=
    prime_set_core_contains π _ hnormal hsupp
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le hNH] at h2
  exact h2

theorem isPGroup_primeCoreIn {q : ℕ} (hq : q.Prime) (H : Subgroup G) :
    IsPGroup q (primeCoreIn {q} H) :=
  (prime_supported_singleton_iff_pgroup q hq _).mp (primeSupported_primeCoreIn {q} H)

theorem coprime_primeCoreIn {q : ℕ} (hq : q.Prime) (H : Subgroup G) :
    Nat.Coprime q (Nat.card (primeCoreIn ({q}ᶜ : Set ℕ) H)) :=
  (prime_supported_complement_singleton_iff_coprime q hq _).mp
    (primeSupported_primeCoreIn ({q}ᶜ : Set ℕ) H)

omit [Finite G] in
theorem le_primeCoreIn_compl {q : ℕ} (hq : q.Prime) {N H : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime q (Nat.card N)) :
    N ≤ primeCoreIn ({q}ᶜ : Set ℕ) H :=
  le_primeCoreIn hNH hN ((prime_supported_complement_singleton_iff_coprime q hq _).mpr hcop)

theorem le_primeCoreIn_pgroup {q : ℕ} (hq : q.Prime) {N H : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hp : IsPGroup q N) :
    N ≤ primeCoreIn {q} H :=
  le_primeCoreIn hNH hN ((prime_supported_singleton_iff_pgroup q hq _).mpr hp)

theorem primeCoreIn_inf_le (π : Set ℕ) {H H' : Subgroup G} (h : H' ≤ H) :
    primeCoreIn π H ⊓ H' ≤ primeCoreIn π H' := by
  apply le_primeCoreIn inf_le_right
  · exact normalizer_inf_of_le H' _ _
      (le_normalizer_primeCoreIn π (h.trans Subgroup.le_normalizer)) Subgroup.le_normalizer
  · exact prime_supported_of_dvd π (primeSupported_primeCoreIn π H)
      (Subgroup.card_dvd_of_le inf_le_left)

theorem isPGroup_of_coprime_of_support {q r : ℕ} (hq : q.Prime) (hr : r.Prime) {Y : Subgroup G}
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card Y → ℓ = q ∨ ℓ = r)
    (hcop : Nat.Coprime q (Nat.card Y)) : IsPGroup r Y := by
  apply (prime_supported_singleton_iff_pgroup r hr Y).mp
  intro ℓ hℓ hdvd
  rcases hsupp ℓ hℓ hdvd with rfl | rfl
  · exact absurd hdvd (hq.coprime_iff_not_dvd.mp hcop)
  · exact rfl

theorem coprime_of_isPGroup {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : r ≠ q)
    {Y : Subgroup G} (hY : IsPGroup q Y) : Nat.Coprime r (Nat.card Y) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := hY.exists_card_eq
  rw [hn]
  exact (Nat.coprime_primes hr hq |>.mpr hqr).pow_right n

omit [Finite G] in
theorem sylowOf_le {q : ℕ} {T U : Subgroup G} (h : IsSylowOf q T U) : T ≤ U := by
  obtain ⟨P, rfl⟩ := h
  exact Subgroup.map_subtype_le _

omit [Finite G] in
theorem sylowOf_isPGroup {q : ℕ} {T U : Subgroup G} (h : IsSylowOf q T U) : IsPGroup q T := by
  obtain ⟨P, rfl⟩ := h
  exact P.isPGroup'.map U.subtype

omit [Finite G] in
theorem sylowOf_eq_of_le {q : ℕ} {T U Y : Subgroup G} (h : IsSylowOf q T U)
    (hY : IsPGroup q Y) (hTY : T ≤ Y) (hYU : Y ≤ U) : Y = T := by
  obtain ⟨P, rfl⟩ := h
  have hY' : IsPGroup q (Y.subgroupOf U) :=
    hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYU).symm
  have hPY : (P : Subgroup U) ≤ Y.subgroupOf U := Subgroup.map_le_iff_le_comap.mp hTY
  have heq : Y.subgroupOf U = (P : Subgroup U) := P.is_maximal' hY' hPY
  have hmap := congrArg (Subgroup.map U.subtype) heq
  rw [Subgroup.map_subgroupOf_eq_of_le hYU] at hmap
  exact hmap

omit [Finite G] in
theorem sylowOf_le_of_normal {q : ℕ} {T U Y : Subgroup G} (h : IsSylowOf q T U)
    (hYU : Y ≤ U) (hY : IsPGroup q Y) (hN : U ≤ Subgroup.normalizer (Y : Set G)) : Y ≤ T := by
  obtain ⟨P, rfl⟩ := h
  have hnormal : (Y.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hY' : IsPGroup q (Y.subgroupOf U) :=
    hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYU).symm
  have hle : Y.subgroupOf U ≤ (P : Subgroup U) := hY'.le_sylow_of_normal P
  have hmap := Subgroup.map_mono (f := U.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hYU] at hmap
  exact hmap

theorem sylowOf_card_eq {q : ℕ} (hq : q.Prime) {T T' U : Subgroup G} (h : IsSylowOf q T U)
    (h' : IsSylowOf q T' U) : Nat.card T = Nat.card T' := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, rfl⟩ := h
  obtain ⟨P', rfl⟩ := h'
  have e1 : Nat.card (P : Subgroup U) = q ^ (Nat.card U).factorization q :=
    Sylow.card_eq_multiplicity P
  have e2 : Nat.card (P' : Subgroup U) = q ^ (Nat.card U).factorization q :=
    Sylow.card_eq_multiplicity P'
  rw [Subgroup.card_map_of_injective U.subtype_injective,
    Subgroup.card_map_of_injective U.subtype_injective, e1, e2]

theorem sylowOf_card_le {q : ℕ} (hq : q.Prime) {T U Y : Subgroup G} (h : IsSylowOf q T U)
    (hY : IsPGroup q Y) (hYU : Y ≤ U) : Nat.card Y ≤ Nat.card T := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, rfl⟩ := h
  have hY' : IsPGroup q (Y.subgroupOf U) :=
    hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYU).symm
  obtain ⟨P', hle⟩ := hY'.exists_le_sylow
  have e1 : Nat.card (P : Subgroup U) = q ^ (Nat.card U).factorization q :=
    Sylow.card_eq_multiplicity P
  have e2 : Nat.card (P' : Subgroup U) = q ^ (Nat.card U).factorization q :=
    Sylow.card_eq_multiplicity P'
  have h3 : Nat.card (Y.subgroupOf U) ≤ Nat.card (P' : Subgroup U) := Subgroup.card_le_of_le hle
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYU).toEquiv] at h3
  rw [Subgroup.card_map_of_injective U.subtype_injective, e1, ← e2]
  exact h3

theorem isSylowOf_of_card {q : ℕ} (hq : q.Prime) {T T₀ U : Subgroup G} (h : IsSylowOf q T₀ U)
    (hTU : T ≤ U) (hT : IsPGroup q T) (hcard : Nat.card T = Nat.card T₀) : IsSylowOf q T U := by
  obtain ⟨P, rfl⟩ := h
  have hT' : IsPGroup q (T.subgroupOf U) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTU).symm
  have hc : Nat.card (T.subgroupOf U) = Nat.card (P : Subgroup U) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTU).toEquiv, hcard,
      Subgroup.card_map_of_injective U.subtype_injective]
  obtain ⟨R, hR⟩ := pgroup_sylow_of_card_eq q hq (T.subgroupOf U) hT' P hc
  refine ⟨R, ?_⟩
  rw [hR]
  exact Subgroup.map_subgroupOf_eq_of_le hTU

theorem sylowOf_conj {q : ℕ} (hq : q.Prime) {T U : Subgroup G} (h : IsSylowOf q T U) {c : G}
    (hc : c ∈ U) : IsSylowOf q (conjugateSubgroup c T) U := by
  have hTU := sylowOf_le h
  have hle : conjugateSubgroup c T ≤ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact U.mul_mem (U.mul_mem hc (hTU ht)) (U.inv_mem hc)
  refine isSylowOf_of_card hq h hle ?_ ?_
  · exact (sylowOf_isPGroup h).of_equiv ((MulAut.conj c).subgroupMap T)
  · exact conjugate_subgroup_card c T

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
