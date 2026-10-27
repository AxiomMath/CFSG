module

public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Data
public import CFSG.RankThree.GF2n.Parrott.CaseII
public import CFSG.GroupTheory.SylowNormalizerConj

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

private theorem spinB_zero_right (v : V) : b v 0 = 0 := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have hq0 : q (0 : V) = 0 := by simp [q]
  have hb : b v 0 = q v + q v := by simp [b, hq0]
  rw [hb, h2]

variable {G : Type} [Group G] {z : G}

theorem exists_conj_eq_z_mul_of_isConj [Finite G] (h : Tim79a.ParrottHypA z)
    {ψ : ↥(H z) →* A45} {κ : G → V} (hκ : IsSpinCoord ψ κ) {w₀ : V}
    (h5 : ∀ a ∈ spinStab w₀,
      (∀ v : V, b v w₀ = 0 → ((rhoA a : GL8) : Mat8) *ᵥ v = v) → a = 1)
    (h6 : ∀ v : V, (∀ w : V, b w w₀ = 0 → b v w = 0) → v = 0 ∨ v = w₀)
    (hnd : ∃ v : V, b v w₀ ≠ 0)
    {j : G} (hjJ : j ∈ J z) (hjκ : κ j = w₀) (hzj : IsConj z j) :
    ∃ y : G, y * j = j * y ∧ y * z * y⁻¹ = z * j := by
  classical
  have hz1 : z ≠ 1 := by
    intro hz
    have h := orderOf_z_A h
    rw [hz, orderOf_one] at h
    norm_num at h
  have hzJ : z ∈ J z := z_mem_J_A h
  have hjc : j * z = z * j :=
    Subgroup.mem_centralizer_singleton_iff.mp (J_le_H hjJ)
  have hw0 : w₀ ≠ 0 := by
    intro hw
    obtain ⟨v, hv⟩ := hnd
    exact hv (by rw [hw]; exact spinB_zero_right v)
  have hjz : j ≠ z := by
    intro e
    apply hw0
    have h0 : κ j = 0 := by
      rw [e]
      exact (hκ.eq_zero_iff z hzJ).mpr (Or.inr rfl)
    rw [hjκ] at h0
    exact h0
  let K : Subgroup G :=
    Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({j} : Set G)
  have hzK : z ∈ K := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hjc.symm
  let N : Subgroup K := Subgroup.zpowers (⟨z, hzK⟩ : K)
  have hN2 : IsPGroup 2 N := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_z_A h]
    norm_num
  obtain ⟨S, hNS⟩ := hN2.exists_le_sylow
  let T : Subgroup G := (S : Subgroup K).map K.subtype
  have hT2 : IsPGroup 2 T := S.isPGroup'.map K.subtype
  have hzT : z ∈ T := by
    have hzN : (⟨z, hzK⟩ : K) ∈ N := Subgroup.mem_zpowers _
    exact Subgroup.mem_map_of_mem K.subtype (hNS hzN)
  have hTK : T ≤ K := Subgroup.map_subtype_le _
  have hTH : T ≤ H z := hTK.trans inf_le_left
  have hTmax : ∀ T' : Subgroup G, T' ≤ K → IsPGroup 2 T' → T ≤ T' → T' = T := by
    intro T' hT'K hT'2 hTle
    have hSle : (S : Subgroup K) ≤ T'.subgroupOf K := by
      intro s hs
      exact hTle (Subgroup.mem_map_of_mem K.subtype hs)
    have hT'2' : IsPGroup 2 (T'.subgroupOf K) := hT'2.comap_subtype
    have hEq : T'.subgroupOf K = (S : Subgroup K) := S.is_maximal' hT'2' hSle
    calc T' = (T'.subgroupOf K).map K.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hT'K).symm
      _ = (S : Subgroup K).map K.subtype := by rw [hEq]
      _ = T := rfl
  let Q : Subgroup G := J z ⊓ Subgroup.centralizer ({j} : Set G)
  have hQ2 : IsPGroup 2 Q :=
    (isPGroup_J_A h).to_inf_left (K := Subgroup.centralizer ({j} : Set G))
  have hQK : Q ≤ K := by
    intro x hx
    exact ⟨J_le_H hx.1, hx.2⟩
  have hTnormJ : T ≤ Subgroup.normalizer (J z : Set G) :=
    hTH.trans (J_le_normalizer_A (z := z))
  have hTnormCj : T ≤
      Subgroup.normalizer (Subgroup.centralizer ({j} : Set G) : Set G) := by
    intro t ht
    have htCj : t ∈ Subgroup.centralizer ({j} : Set G) := (hTK ht).2
    rw [Subgroup.mem_set_normalizer_iff']
    intro h
    change h * t ∈ Subgroup.centralizer ({j} : Set G) ↔
      t * h ∈ Subgroup.centralizer ({j} : Set G)
    constructor
    · intro hh
      have h2 : h ∈ Subgroup.centralizer ({j} : Set G) := by
        simpa [mul_assoc] using mul_mem hh (inv_mem htCj)
      exact mul_mem htCj h2
    · intro hh
      have h2 : h ∈ Subgroup.centralizer ({j} : Set G) := by
        simpa [mul_assoc] using mul_mem (inv_mem htCj) hh
      exact mul_mem h2 htCj
  have hTnormQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    (le_inf hTnormJ hTnormCj).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := J z)
        (K := Subgroup.centralizer ({j} : Set G)))
  have hsup2 : IsPGroup 2 (T ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hT2 hQ2 hTnormQ
  have hsupK : (T ⊔ Q : Subgroup G) ≤ K := sup_le hTK hQK
  have hQleT : Q ≤ T :=
    (hTmax (T ⊔ Q : Subgroup G) hsupK hsup2 le_sup_left) ▸ le_sup_right
  let P : Subgroup G := T ⊔ J z
  have hP2 : IsPGroup 2 P :=
    IsPGroup.to_sup_of_normal_right' hT2 (isPGroup_J_A h) hTnormJ
  have hPz : P ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (hTK.trans inf_le_left) (J_le_H (z := z))
  have hTneP : T ≠ P := by
    intro heq
    have hJleT : J z ≤ T := heq.symm ▸ le_sup_right
    obtain ⟨v, hv⟩ := hnd
    obtain ⟨k, hk, hkv⟩ := hκ.surj v
    have hkT : k ∈ T := hJleT hk
    have hkc : k * j = j * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (hTK hkT).2
    have hb : b (κ k) (κ j) = 0 := (hκ.commute_iff hz1 hk hjJ).mp hkc
    exact hv (by simpa [← hkv, hjκ] using hb)
  have hcard : Nat.card T < Nat.card P :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left hTneP)
  obtain ⟨y, hyCj, hyNorm, hyz⟩ :=
    CFSG.GroupTheory.exists_mem_normalizer_not_mem_centralizer_of_isConj hzj hTK hT2 hTmax hP2 hPz
      hcard
  let t : G := y * z * y⁻¹
  have htT : t ∈ T := (Subgroup.mem_set_normalizer_iff.mp hyNorm z).mp hzT
  have htK : t ∈ K := hTK htT
  have htCj : t ∈ Subgroup.centralizer ({j} : Set G) := htK.2
  have htH : t ∈ H z := htK.1
  have ht_comm_T : ∀ t' ∈ T, t' * t = t * t' := by
    intro t' ht'
    have hconj : y⁻¹ * t' * y ∈ T :=
      (Subgroup.mem_set_normalizer_iff''.mp hyNorm t').mp ht'
    have hcommz : (y⁻¹ * t' * y) * z = z * (y⁻¹ * t' * y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hTK hconj).1
    calc
      t' * t = y * (y⁻¹ * t' * y) * z * y⁻¹ := by simp only [t]; group
      _ = y * ((y⁻¹ * t' * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * t' * y)) * y⁻¹ := by rw [hcommz]
      _ = t * t' := by simp only [t]; group
  have hψt : ψ ⟨t, htH⟩ ∈ spinStab w₀ := by
    simpa [hjκ] using
      hκ.mem_spinStab hjJ htH (Subgroup.mem_centralizer_singleton_iff.mp htCj)
  have hfix : ∀ v : V, b v w₀ = 0 →
      ((rhoA (ψ ⟨t, htH⟩) : GL8) : Mat8) *ᵥ v = v := by
    intro v hv
    obtain ⟨k, hk, hkv⟩ := hκ.surj v
    have hbkj : b (κ k) (κ j) = 0 := by rw [hkv, hjκ]; exact hv
    have hkj : k * j = j * k := (hκ.commute_iff hz1 hk hjJ).mpr hbkj
    have hkQ : k ∈ Q := ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hkj⟩
    have hkT : k ∈ T := hQleT hkQ
    have htk : t * k = k * t := (ht_comm_T k hkT).symm
    have hact := hκ.act t htH k hk
    have he : t * k * t⁻¹ = k := by rw [htk, mul_inv_cancel_right]
    rw [he] at hact
    rw [← hkv]
    exact hact.symm
  have hψ1 : ψ ⟨t, htH⟩ = 1 := h5 _ hψt hfix
  have htJ : t ∈ J z := (hκ.eq_one_iff ⟨t, htH⟩).mp hψ1
  have horth : ∀ w : V, b w w₀ = 0 → b (κ t) w = 0 := by
    intro w hw
    obtain ⟨k, hk, hkw⟩ := hκ.surj w
    have hbkj : b (κ k) (κ j) = 0 := by rw [hkw, hjκ]; exact hw
    have hkj : k * j = j * k := (hκ.commute_iff hz1 hk hjJ).mpr hbkj
    have hkQ : k ∈ Q := ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hkj⟩
    have hkT : k ∈ T := hQleT hkQ
    have htk : t * k = k * t := (ht_comm_T k hkT).symm
    have hb : b (κ t) (κ k) = 0 := (hκ.commute_iff hz1 htJ hk).mp htk
    rwa [hkw] at hb
  have ht_cases : t = 1 ∨ t = z ∨ t = j ∨ t = j * z := by
    rcases h6 (κ t) horth with h0 | hw
    · rcases (hκ.eq_zero_iff t htJ).mp h0 with h1 | hz
      · exact Or.inl h1
      · exact Or.inr (Or.inl hz)
    · have htj : κ t = κ j := hw.trans hjκ.symm
      rcases (hκ.kappa_eq_iff (j := j) (k := t) hjJ htJ).mp htj with hj | hjz
      · exact Or.inr (Or.inr (Or.inl hj))
      · exact Or.inr (Or.inr (Or.inr hjz))
  have ht_ne_one : t ≠ 1 := by
    intro e
    have hz1' : z = 1 := by
      calc z = y⁻¹ * t * y := by simp only [t]; group
        _ = 1 := by rw [e]; group
    exact hz1 hz1'
  have ht_ne_z : t ≠ z := hyz
  have hyj : y * j = j * y := Subgroup.mem_centralizer_singleton_iff.mp hyCj
  have ht_ne_j : t ≠ j := by
    intro e
    have hzj' : z = j := by
      calc z = y⁻¹ * t * y := by simp only [t]; group
        _ = y⁻¹ * j * y := by rw [e]
        _ = y⁻¹ * (j * y) := by group
        _ = y⁻¹ * (y * j) := by rw [hyj.symm]
        _ = j := by group
    exact hjz hzj'.symm
  have ht_eq : t = j * z := by
    rcases ht_cases with e | e | e | e
    · exact absurd e ht_ne_one
    · exact absurd e ht_ne_z
    · exact absurd e ht_ne_j
    · exact e
  refine ⟨y, hyj, ?_⟩
  have hfinal : y * z * y⁻¹ = j * z := ht_eq
  rw [hfinal, hjc]

end CFSG.RankThree.GF2n.Parrott
