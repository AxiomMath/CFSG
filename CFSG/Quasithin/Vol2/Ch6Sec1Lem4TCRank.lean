module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCSteps

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def ZV614 (T L V : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)

@[expose] noncomputable def Aprime614 (K : Subgroup G) (E : Subgroup (ModO2 K)) : Subgroup G :=
  (E.comap (mk614 K)).map K.subtype

theorem mem_pCoreOf_of_mk614_eq_one {K : Subgroup G} {x : G} (hxK : x ∈ K)
    (h : mk614 K ⟨x, hxK⟩ = 1) : x ∈ pCoreOf 2 K := by
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp h
  exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hmem, rfl⟩

theorem normalizer_ZV614 {T L V : Subgroup G} {d : G}
    (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hdTL : d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) :
    d ∈ Subgroup.normalizer ((ZV614 T L V : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) →
      g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) →
      ∀ z ∈ ZV614 T L V, g * z * g⁻¹ ∈ ZV614 T L V := by
    intro g hgV hgTL z hz
    obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hgV z).mp hzV
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : g⁻¹ * t * g ∈ T ⊓ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgTL) t).mp ht
        rwa [inv_inv] at this
      have hc := (Subgroup.mem_centralizer_iff.mp hzC) (g⁻¹ * t * g) ht'
      calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
        _ = g * z * g⁻¹ * t := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key d hdV hdTL z
  · intro hz
    have := key d⁻¹ (Subgroup.inv_mem _ hdV) (Subgroup.inv_mem _ hdTL) _ hz
    have e : d⁻¹ * (d * z * d⁻¹) * d⁻¹⁻¹ = z := by group
    rwa [e] at this

theorem aprime_le_K614 {K : Subgroup G} (E : Subgroup (ModO2 K)) : Aprime614 K E ≤ K := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem fwd_Aprime614 {K : Subgroup G} {E : Subgroup (ModO2 K)} {e : G}
    (he : e ∈ Subgroup.normalizer (K : Set G)) (hΦe : actModO2_614 K ⟨e, he⟩ = 1) :
    ∀ a ∈ Aprime614 K E, e * a * e⁻¹ ∈ Aprime614 K E := by
  intro a ha
  have haK : a ∈ K := aprime_le_K614 E ha
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha
  have hyE : mk614 K y ∈ E := hy
  have heaK : e * a * e⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp he a).mp haK
  have h2 : actModO2_614 K ⟨e, he⟩ (mk614 K ⟨a, haK⟩) = mk614 K ⟨a, haK⟩ := by
    rw [hΦe, MulAut.one_apply]
  have hmk : mk614 K ⟨e * a * e⁻¹, heaK⟩ = mk614 K y := by
    have hay : (⟨a, haK⟩ : ↥K) = y := Subtype.ext hya.symm
    rw [← hay]
    exact (actModO2_614_mk K ⟨e, he⟩ ⟨a, haK⟩).symm.trans h2
  refine Subgroup.mem_map.mpr ⟨⟨e * a * e⁻¹, heaK⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, hmk]
  exact hyE

theorem normalizes_Aprime614 {K : Subgroup G} {E : Subgroup (ModO2 K)} {d : G}
    (hdK : d ∈ Subgroup.normalizer (K : Set G)) (hΦ : actModO2_614 K ⟨d, hdK⟩ = 1) :
    d ∈ Subgroup.normalizer ((Aprime614 K E : Subgroup G) : Set G) := by
  have hd' : d⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hdK
  have hΦ' : actModO2_614 K ⟨d⁻¹, hd'⟩ = 1 := by
    have e : (⟨d⁻¹, hd'⟩ : ↥(Subgroup.normalizer (K : Set G))) = (⟨d, hdK⟩)⁻¹ := rfl
    rw [e, map_inv, hΦ, inv_one]
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact fwd_Aprime614 hdK hΦ a
  · intro ha
    have := fwd_Aprime614 hd' hΦ' _ ha
    have e : d⁻¹ * (d * a * d⁻¹) * d⁻¹⁻¹ = a := by group
    rwa [e] at this

theorem card_Aprime614 {K : Subgroup G} {E : Subgroup (ModO2 K)} (hE : Nat.card ↥E = 9) :
    Nat.card ↥(Aprime614 K E) = 9 * Nat.card ↥(pCoreOf 2 K) := by
  classical
  have hmapC : Nat.card ↥(Aprime614 K E) = Nat.card ↥(E.comap (mk614 K)) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hpc : Nat.card ↥(pCoreOf 2 K) = Nat.card ↥(CFSG.pCore 2 ↥K) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hsurj : Function.Surjective (mk614 K) := QuotientGroup.mk'_surjective _
  have hidx : (E.comap (mk614 K)).index = E.index :=
    Subgroup.index_comap_of_surjective E hsurj
  have h1 := Subgroup.card_mul_index (E.comap (mk614 K))
  have h2 := Subgroup.card_mul_index E
  have h3 := Subgroup.card_mul_index (CFSG.pCore 2 ↥K)
  rw [hmapC, hpc]
  rw [hidx] at h1
  have hpos : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hN : (CFSG.pCore 2 ↥K).index = Nat.card (ModO2 K) := rfl
  rw [hN] at h3
  rw [hE] at h2
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  calc Nat.card ↥K = Nat.card ↥(CFSG.pCore 2 ↥K) * (9 * E.index) := by
        rw [← h3, ← h2]
    _ = 9 * Nat.card ↥(CFSG.pCore 2 ↥K) * E.index := by ring

end CFSG.Quasithin.H13.T614

end
