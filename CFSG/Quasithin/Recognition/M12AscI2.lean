module

public import CFSG.Quasithin.Recognition.M12AscI1
public import CFSG.Quasithin.Recognition.M12AscDouble
public import CFSG.Quasithin.Recognition.M12AscKlein

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

structure IData (m : AscModel z) (t y : G) (K V : Subgroup G) : Prop where
  t_sq : t * t = 1
  t_Q : t ∈ ascQ z
  t_F : t ∉ m.fSub
  V_F : V ≤ m.fSub
  K_le : K ≤ Subgroup.centralizer ({t} : Set G)
  K_norm : ∀ i ∈ Subgroup.centralizer ({t} : Set G), ∀ k ∈ K, i * k * i⁻¹ ∈ K
  card_I : Nat.card (Subgroup.centralizer ({t} : Set G)) = 4 * Nat.card K
  sq_mem : ∀ i ∈ Subgroup.centralizer ({t} : Set G), i * i ∈ K
  t_K : t ∉ K
  klein : KleinCore K V z y
  conj_mem : ∀ x ∈ Subgroup.centralizer ({t} : Set G), IsConj z x → x ∈ K

namespace AscModel

variable (m : AscModel z)

include m

theorem exists_IData [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) :
    ∃ (t y : G) (K V : Subgroup G), IData m t y K V := by
  obtain ⟨g, hgz, q, hqP, hq⟩ := hyp.not_weakly_closed
  have hsQ : g * z * g⁻¹ ∈ ascQ z := by
    rw [← hq]
    exact (mem_ascQ_iff z _).2 ⟨q.2, hqP⟩
  obtain ⟨y, t, hyN, hy3, hyz, htQ, htF, ht2, hVt, hyt⟩ := m.exists_t_data hyp hgz hsQ
  set V := m.ascV hyp hgz hsQ with hV
  have hf := m.tb_facts hyp htQ htF ht2
  set S := m.cSub hf with hS
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hVF : V ≤ m.fSub := m.ascV_le_fSub hyp hgz hsQ
  have hVcard : Nat.card V = 4 := m.card_ascV hyp hgz hsQ
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => (m.fSub_elab (hVF hv) (hVF hv)).1
  have hzV : z ∈ V := (m.mem_ascV hyp hgz hsQ).2 (Or.inr (Or.inl rfl))
  have hSmax := m.cSub_maximal hyp htQ htF hf
  have hmemS : ∀ x, x ∈ S ↔ x ∈ ascH z ∧ x * t = t * x := fun x => m.mem_cSub_iff htQ hf
  have hSI : S ≤ Subgroup.centralizer ({t} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 ((hmemS s).1 hs).2
  have hS16 : Nat.card S = 16 := m.card_cSub hf
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 4) (by rw [hS16]; norm_num)
  have htS : t ∈ S := (hmemS t).2 ⟨ascQ_le_ascH z htQ, rfl⟩
  have hVS : V ≤ S := fun v hv =>
    (hmemS v).2 ⟨ascQ_le_ascH z (m.fSub_le_ascQ hyp (hVF hv)), hVt v hv⟩
  obtain ⟨r, hrS, hr2, hrF, hrtF⟩ := m.exists_r_cSub htQ hf
  have hrQ : r ∈ ascQ z := m.cSub_le_ascQ hyp hf hrS
  have hrV' : ∀ v ∈ V, r * v * r⁻¹ ∈ V := fun v hv => m.V_norm_Q hyp hgz hsQ hrQ hv
  have hrV : r ∉ V := fun h => hrF (hVF h)
  set D := extInv V r hr2 hrV' with hD
  have hDcard : Nat.card D = 2 * Nat.card V := card_extInv hrV
  have hDS : D ≤ S := by
    intro x hx
    rcases hx with h | ⟨v, hv, rfl⟩
    · exact hVS h
    · exact S.mul_mem (hVS hv) hrS
  have htD : t ∉ D := by
    rintro (h | ⟨v, hv, h⟩)
    · exact htF (hVF h)
    · have hr : r = v⁻¹ * t := by
        calc r = v⁻¹ * (v * r) := by group
          _ = v⁻¹ * t := by rw [← h]
      have hrt : r * t = v⁻¹ := by
        calc r * t = v⁻¹ * t * t := by rw [hr]
          _ = v⁻¹ * (t * t) := by group
          _ = v⁻¹ := by rw [ht2, mul_one]
      exact hrtF (by rw [hrt]; exact inv_mem (hVF hv))
  have hVcl : ∀ v ∈ V, ∀ a ∈ Subgroup.centralizer ({t} : Set G), a⁻¹ * v * a ∈ S →
      a⁻¹ * v * a ∈ V := by
    intro v hv a ha haS
    by_cases hv1 : v = 1
    · rw [hv1]
      simp
    · have hvF := hVF hv
      have hvQ := m.fSub_le_ascQ hyp hvF
      obtain ⟨c, hc⟩ := (m.conj_mem_Q_iff hyp hvQ hv1).2 hvF
      have hconj : (a⁻¹ * c) * z * (a⁻¹ * c)⁻¹ = a⁻¹ * v * a := by
        rw [← hc]
        group
      have hxQ : a⁻¹ * v * a ∈ ascQ z := m.cSub_le_ascQ hyp hf haS
      have hxF : a⁻¹ * v * a ∈ m.fSub :=
        m.zconj_mem_fSub hyp hxQ (isConj_iff.2 ⟨a⁻¹ * c, hconj⟩)
      exact m.fSub_comm_mem_V hyp hgz hsQ htF hVt _ hxF ((hmemS _).1 haS).2
  have hrV2 : ∀ a : G, a⁻¹ * r * a ∉ V ∧ a⁻¹ * (r * t) * a ∉ V := fun a =>
    ⟨m.not_conj_mem_V hyp hgz hsQ hrQ hrF a,
      m.not_conj_mem_V hyp hgz hsQ (mul_mem hrQ htQ) hrtF a⟩
  obtain ⟨I0, K, hI0I, hKI0, hI0n, hKn, hcard, htI0, hsq, hVK, hKS⟩ :=
    double_transfer ht2 hSI hSp hSmax htS hDS hS16 (by rw [hS16, hDcard, hVcard]) htD le_extInv
      hVcard hVsq hrS hr2 hVcl hrV2
  have hKI : K ≤ Subgroup.centralizer ({t} : Set G) := hKI0.trans hI0I
  have hyI : y ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * t = (y * t * y⁻¹) * y := by group
      _ = t * y := by rw [hyt]
  have hyinv : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hy3)
  have hyK : y ∈ K := by
    have h := hsq y⁻¹ (inv_mem hyI)
    have e : y⁻¹ * y⁻¹ = y := by
      calc y⁻¹ * y⁻¹ = (y * y) * (y * y) := by rw [hyinv]
        _ = (y * y * y) * y := by group
        _ = y := by rw [hy3, one_mul]
    rwa [e] at h
  obtain ⟨m', hm'odd, hIm⟩ := exists_odd_card_of_maximal _ S hSI hSp hSmax
  rw [hS16] at hIm
  have hKm : Nat.card K = 2 ^ 2 * m' := by
    have : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [this]
    omega
  refine ⟨t, y, K, V, ⟨ht2, htQ, htF, hVF, hKI, hKn, hcard, hsq, fun h => htI0 (hKI0 h), ?_, ?_⟩⟩
  · exact
      { z_sq := hz2
        z_ne := asc_z_ne_one hyp
        z_mem := hzV
        V_le := fun v hv => hVK hv
        V_card := hVcard
        V_sq := hVsq
        cent := fun k hk hkz => by
          have hkS : k ∈ S := (hmemS k).2
            ⟨Subgroup.mem_centralizer_singleton_iff.2 hkz,
              Subgroup.mem_centralizer_singleton_iff.1 (hKI hk)⟩
          exact hKS k hk hkS
        y_mem := hyK
        y_cube := hy3
        y_norm := fun v hv => (Subgroup.mem_normalizer_iff.1 hyN v).1 hv
        y_ne := hyz
        syl := fun W hWK hW => by
          have h := card_le_of_isPGroup_of_odd hKm hm'odd hW hWK
          simpa using h }
  · intro x hx hzx
    obtain ⟨c, hc⟩ := isConj_iff.1 hzx
    have hx2 : x * x = 1 := by rw [← hc]; exact asc_conj_sq hyp c
    have hx1 : x ≠ 1 := by rw [← hc]; exact asc_conj_ne_one hyp c
    obtain ⟨d, hdI, hdS⟩ := exists_conj_mem_of_maximal _ S hSI hSp hSmax hx hx2 hx1
    have hdxQ : d * x * d⁻¹ ∈ ascQ z := m.cSub_le_ascQ hyp hf hdS
    have hdz : IsConj z (d * x * d⁻¹) := isConj_iff.2 ⟨d * c, by rw [← hc]; group⟩
    have hdxF := m.zconj_mem_fSub hyp hdxQ hdz
    have hdxV := m.fSub_comm_mem_V hyp hgz hsQ htF hVt _ hdxF ((hmemS _).1 hdS).2
    have h := hKn d⁻¹ (inv_mem hdI) _ (hVK hdxV)
    rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at h

end AscModel

end CFSG.Quasithin
