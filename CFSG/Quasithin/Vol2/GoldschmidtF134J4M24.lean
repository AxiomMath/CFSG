module

public import CFSG.Quasithin.Vol2.F134M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24

public section

namespace CFSG.Quasithin.F134.J4E9

open Equiv CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1

theorem mem_map_conj {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem m24_core {K Q : Subgroup (Perm (Fin 24))} (hKM : K ≤ NativeSporadic.M24)
    (hTK : m24T ≤ K) (hK : Nat.card K = 9 * 2 ^ 10) (hQK : Q ≤ K) (hQ : Nat.card Q = 9) :
    Nat.card m24T = 2 ^ 10 ∧ ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧
      ∀ t ∈ m24T, t ∈ Subgroup.normalizer (Q : Set (Perm (Fin 24))) →
        t * y₀ * t⁻¹ ∈ Subgroup.zpowers y₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 m24T_isPGroup
  have hle : Nat.card m24T ≤ 2 ^ 10 := by
    have hdvd : Nat.card m24T ∣ 9 * 2 ^ 10 := hK ▸ Subgroup.card_dvd_of_le hTK
    rw [ha] at hdvd ⊢
    have : 2 ^ a ∣ 2 ^ 10 :=
      (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 9)).dvd_of_dvd_mul_left hdvd
    exact Nat.le_of_dvd (by positivity) this
  have h5 : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_nine_mul_two_pow (Or.inl rfl)
  have h7 : ¬ 7 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_nine_mul_two_pow (Or.inr (Or.inl rfl))
  obtain ⟨X, hX, hKset⟩ := m24_classify hTK hKM h5 h7 (by omega)
  have hge : 2 ^ 10 ≤ Nat.card m24T := by
    have h1 : Nat.card K ≤ 9 * Nat.card m24T := by
      rw [show Nat.card K = (K : Set (Perm (Fin 24))).ncard from Nat.card_coe_set_eq _, hKset]
      exact ncard_m24HSet_le X
    omega
  have hTcard : Nat.card m24T = 2 ^ 10 := le_antisymm hle hge
  have hK9 : Nat.card K = 9 * Nat.card m24T := by rw [hK, hTcard]
  refine ⟨hTcard, ?_⟩
  rcases Nat.lt_or_ge X 2 with hX2 | hX2
  · obtain ⟨y₀, hy₀Q, hy₀o, hy₀z, hmax⟩ := m24_key_z hX2 hKset hTK hK9 hQK hQ
    refine ⟨y₀, hy₀Q, hy₀o, fun t ht htN => ?_⟩
    have hmem : t * y₀ * t⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp htN y₀).mp hy₀Q
    refine hmax _ hmem ?_
    have h1 : t * m24Z0E = m24Z0E * t := m24Z0E_comm ht
    have h2 : t⁻¹ * m24Z0E = m24Z0E * t⁻¹ := m24Z0E_comm (inv_mem ht)
    calc t * y₀ * t⁻¹ * m24Z0E = t * y₀ * (t⁻¹ * m24Z0E) := by group
      _ = t * (y₀ * m24Z0E) * t⁻¹ := by rw [h2]; group
      _ = t * (m24Z0E * y₀) * t⁻¹ := by rw [hy₀z]
      _ = (t * m24Z0E) * y₀ * t⁻¹ := by group
      _ = m24Z0E * (t * y₀ * t⁻¹) := by rw [h1]; group
  · have hX' : X = 2 := by omega
    subst hX'
    obtain ⟨y₀, hy₀Q, hy₀o, hy₀psi, hmax⟩ := m24_key_psi hKset hKM hK9 hQK hQ
    refine ⟨y₀, hy₀Q, hy₀o, fun t ht htN => ?_⟩
    have hmem : t * y₀ * t⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp htN y₀).mp hy₀Q
    refine hmax _ hmem fun h => hy₀psi ?_
    have := m24Psi_conj (inv_mem (m24T_le ht)) h
    rwa [show t⁻¹ * (t * y₀ * t⁻¹) * t⁻¹⁻¹ = y₀ by group] at this

theorem exists_conj_m24T {T : Subgroup (Perm (Fin 24))}
    (hTM : T ≤ NativeSporadic.M24) (hT : Nat.card T = 2 ^ 10) :
    ∃ g ∈ NativeSporadic.M24, ∀ t ∈ m24T, g⁻¹ * t * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : Nat.card S24 = 2 ^ 10 * 239085 := m24_card_eq
  let Tb : Subgroup S24 := T.subgroupOf NativeSporadic.M24
  have hTb : Nat.card Tb = 2 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT]
  have hTbp : IsPGroup 2 Tb := IsPGroup.of_card hTb
  have hTbidx : ¬ 2 ∣ Tb.index := by
    have h := Tb.card_mul_index
    rw [hTb, hG] at h
    have : Tb.index = 239085 := by omega
    rw [this]
    norm_num
  let P : Sylow 2 S24 := hTbp.toSylow hTbidx
  let Mb : Subgroup S24 := m24T.subgroupOf NativeSporadic.M24
  have hMbp : IsPGroup 2 Mb :=
    m24T_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe m24T_le).symm
  obtain ⟨Q, hMQ⟩ := hMbp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S24 P Q
  refine ⟨g.1, g.2, fun t ht => ?_⟩
  have htM : (⟨t, m24T_le ht⟩ : S24) ∈ Mb := Subgroup.mem_subgroupOf.mpr ht
  have hmem : (⟨t, m24T_le ht⟩ : S24) ∈ ((g • P : Sylow 2 S24) : Subgroup S24) := by
    rw [hg]
    exact hMQ htM
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  have h2 : (MulAut.conj g)⁻¹ ⟨t, m24T_le ht⟩ ∈ Tb := hmem
  rw [MulAut.conj_inv_apply] at h2
  exact Subgroup.mem_subgroupOf.mp h2

theorem m24_core' {K Q T : Subgroup (Perm (Fin 24))}
    (hKM : K ≤ NativeSporadic.M24) (hTK : T ≤ K) (hT : Nat.card T = 2 ^ 10)
    (hK : Nat.card K = 9 * 2 ^ 10) (hQK : Q ≤ K) (hQ : Nat.card Q = 9) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ ∀ t ∈ T, t ∈ Subgroup.normalizer (Q : Set (Perm (Fin 24))) →
      t * y₀ * t⁻¹ ∈ Subgroup.zpowers y₀ := by
  obtain ⟨g, hgM, hg⟩ := exists_conj_m24T (hTK.trans hKM |> fun h => (h : T ≤ _)) hT
  let c : Perm (Fin 24) →* Perm (Fin 24) := (MulAut.conj g).toMonoidHom
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hKM1 : K.map c ≤ NativeSporadic.M24 := by
    rintro _ ⟨k, hk, rfl⟩
    exact mul_mem (mul_mem hgM (hKM hk)) (inv_mem hgM)
  have hmK1 : m24T ≤ K.map c := by
    intro t ht
    refine (mem_map_conj K g t).mpr (hTK (hg t ht))
  have hK1 : Nat.card (K.map c) = 9 * 2 ^ 10 := by rw [Subgroup.card_map_of_injective hcinj, hK]
  have hQK1 : Q.map c ≤ K.map c := Subgroup.map_mono hQK
  have hQ1 : Nat.card (Q.map c) = 9 := by rw [Subgroup.card_map_of_injective hcinj, hQ]
  obtain ⟨hm24, y₁, hy₁Q, hy₁o, hy₁⟩ := m24_core hKM1 hmK1 hK1 hQK1 hQ1
  have hTeq : m24T = T.map c := Subgroup.eq_of_le_of_card_ge
    (fun t ht => (mem_map_conj T g t).mpr (hg t ht))
    (by rw [Subgroup.card_map_of_injective hcinj, hT, hm24])
  obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.mp hy₁Q
  refine ⟨q, hqQ, ?_, fun t htT htN => ?_⟩
  · rw [← hy₁o]
    exact (MulEquiv.orderOf_eq (MulAut.conj g) q).symm
  · have ht1 : c t ∈ m24T := by
      rw [hTeq]
      exact Subgroup.mem_map_of_mem c htT
    have hN1 : c t ∈ Subgroup.normalizer ((Q.map c : Subgroup (Perm (Fin 24))) :
        Set (Perm (Fin 24))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := (Subgroup.mem_normalizer_iff.mp htN (g⁻¹ * h * g))
      rw [mem_map_conj, mem_map_conj, h1]
      have e : g⁻¹ * (c t * h * (c t)⁻¹) * g = t * (g⁻¹ * h * g) * t⁻¹ := by
        simp only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
    have := hy₁ (c t) ht1 hN1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp this
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have e : t * q * t⁻¹ = (MulAut.conj g)⁻¹ (c t * c q * (c t)⁻¹) := by
      simp only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rw [e, ← hn, ← map_zpow]
    simp only [c, MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply, MulAut.conj_apply]
    group

end CFSG.Quasithin.F134.J4E9
