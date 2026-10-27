module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Act

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D]

theorem mul_mem_of_relIndex_two {K Q : Subgroup D} (hK : K.relIndex Q = 2) {a b : D}
    (ha : a ∈ Q) (hb : b ∈ Q) (haK : a ∉ K) (hbK : b ∉ K) : a * b ∈ K := by
  have hidx : (K.subgroupOf Q).index = 2 := hK
  have h := (Subgroup.mul_mem_iff_of_index_two (H := K.subgroupOf Q) hidx
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr (by
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun h => absurd h haK, fun h => absurd h hbK⟩)
  simpa [Subgroup.mem_subgroupOf] using h

theorem mul_self_mem_of_relIndex_two {K Q : Subgroup D} (hK : K.relIndex Q = 2) {a : D}
    (ha : a ∈ Q) : a * a ∈ K := by
  have hidx : (K.subgroupOf Q).index = 2 := hK
  have h := Subgroup.mul_self_mem_of_index_two hidx ⟨a, ha⟩
  simpa [Subgroup.mem_subgroupOf] using h

theorem conj_mul_inv_mem_of_relIndex_two {K Q : Subgroup D} (hK : K.relIndex Q = 2) {b q : D}
    (hbK : b ∈ Subgroup.normalizer (K : Set D)) (hbQ : ∀ x ∈ Q, b * x * b⁻¹ ∈ Q) (hq : q ∈ Q) :
    b * q * b⁻¹ * q⁻¹ ∈ K := by
  by_cases hqK : q ∈ K
  · have h1 : b * q * b⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp hbK q).mp hqK
      exact this
    exact K.mul_mem h1 (K.inv_mem hqK)
  · have hbq : b * q * b⁻¹ ∉ K := fun hmem => hqK <| by
      have := (Subgroup.mem_normalizer_iff.mp hbK q).mpr hmem
      exact this
    exact mul_mem_of_relIndex_two hK (hbQ q hq) (Q.inv_mem hq) hbq
      (fun h => hqK (by simpa using K.inv_mem h))

omit [Group D] in
theorem perm3_conj_inv : ∀ a b : Equiv.Perm (Fin 3), a ≠ 1 → a * a = 1 → b ≠ 1 →
    b * b * b = 1 → a * b * a⁻¹ * b = 1 := by
  decide

variable [Finite D]

theorem vertex_conj_inv_mem {H T : Subgroup D} (hv : Vertex H T) {t y : D} (ht : t ∈ T)
    (htQ : t ∉ pCoreOf 2 H) (hy : y ∈ H) (hy3 : orderOf y = 3) :
    t * y * t⁻¹ * y ∈ pCoreOf 2 H := by
  obtain ⟨φ, -, hφ⟩ := hv.exists_hom
  have htH : t ∈ H := hv.T_le ht
  have hyQ : y ∉ pCoreOf 2 H := fun hmem => hv.not_mem_of_orderOf hy3 (hv.pCoreOf_le hmem)
  have h1 : φ ⟨t, htH⟩ ≠ 1 := fun h => htQ ((hφ ⟨t, htH⟩).mp h)
  have h2 : φ ⟨y, hy⟩ ≠ 1 := fun h => hyQ ((hφ ⟨y, hy⟩).mp h)
  have hsq : t * t ∈ pCoreOf 2 H :=
    mul_self_mem_of_relIndex_two hv.relIndex_pCoreOf_T ht
  have h3 : φ ⟨t, htH⟩ * φ ⟨t, htH⟩ = 1 := by
    rw [← map_mul]
    exact (hφ _).mpr hsq
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have h4 : φ ⟨y, hy⟩ * φ ⟨y, hy⟩ * φ ⟨y, hy⟩ = 1 := by
    rw [← map_mul, ← map_mul]
    have : (⟨y, hy⟩ : H) * ⟨y, hy⟩ * ⟨y, hy⟩ = 1 := Subtype.ext hy3'
    rw [this, map_one]
  have h5 := perm3_conj_inv _ _ h1 h3 h2 h4
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul] at h5
  exact (hφ _).mp h5


theorem relIndex_inf_pCoreOf_right' {A B : Subgroup D} (h : GoldHyp A B)
    (hne : pCoreOf 2 A ≠ pCoreOf 2 B) :
    (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex (pCoreOf 2 B) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) (pCoreOf 2 B) (A ⊓ B)
    inf_le_right h.pCoreOf_right_le
  rw [h.relIndex_inf_pCoreOf hne, h.relIndex_pCoreOf_T_right] at h1
  omega

theorem relIndex_inf_pCoreOf_left' {A B : Subgroup D} (h : GoldHyp A B)
    (hne : pCoreOf 2 A ≠ pCoreOf 2 B) :
    (pCoreOf 2 A ⊓ pCoreOf 2 B).relIndex (pCoreOf 2 A) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) (pCoreOf 2 A) (A ⊓ B)
    inf_le_left h.pCoreOf_left_le
  rw [h.relIndex_inf_pCoreOf hne, h.relIndex_pCoreOf_T_left] at h1
  omega

theorem conj_inv_mem_inf {A B : Subgroup D} (h : GoldHyp A B) (hne : pCoreOf 2 A ≠ pCoreOf 2 B)
    (hN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
    {t y : D} (ht : t ∈ A ⊓ B) (htQ : t ∉ pCoreOf 2 B) (hy : y ∈ B) (hy3 : orderOf y = 3) :
    t * y * t⁻¹ * y ∈ pCoreOf 2 A ⊓ pCoreOf 2 B := by
  classical
  have hgQ : t * y * t⁻¹ * y ∈ pCoreOf 2 B := vertex_conj_inv_mem h.vertex_right ht htQ hy hy3
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have hQN : B ≤ Subgroup.normalizer (pCoreOf 2 B : Set D) := le_normalizer_pCoreOf 2 B
  have hR2 := relIndex_inf_pCoreOf_right' h hne
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set g : D := t * y * t⁻¹ * y with hg
  by_contra hgR
  have hyi : y⁻¹ ∈ B := B.inv_mem hy
  have hiff : ∀ x : D, y⁻¹ * x * y ∈ R ↔ x ∈ R := by
    intro x
    have := Subgroup.mem_normalizer_iff.mp (hN hyi) x
    simpa using this.symm
  have hQconj : ∀ x ∈ pCoreOf 2 B, y⁻¹ * x * y ∈ pCoreOf 2 B := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp (hQN hyi) x).mp hx
    simpa using this
  set g₁ : D := y⁻¹ * g * y with hg₁
  set g₂ : D := y⁻¹ * g₁ * y with hg₂
  have hg₁Q : g₁ ∈ pCoreOf 2 B := hQconj g hgQ
  have hg₂Q : g₂ ∈ pCoreOf 2 B := hQconj g₁ hg₁Q
  have hg₁R : g₁ ∉ R := fun hmem => hgR ((hiff g).mp hmem)
  have hg₂R : g₂ ∉ R := fun hmem => hg₁R ((hiff g₁).mp hmem)
  have hgg₁ : g * g₁ ∈ R := mul_mem_of_relIndex_two hR2 hgQ hg₁Q hgR hg₁R
  have hs3 : (t * y * t⁻¹) * (t * y * t⁻¹) * (t * y * t⁻¹) = 1 := by
    calc (t * y * t⁻¹) * (t * y * t⁻¹) * (t * y * t⁻¹) = t * (y * y * y) * t⁻¹ := by group
      _ = 1 := by rw [hy3']; group
  have hrel : g * g₁ * g₂ = 1 := by
    have e : g * g₁ * g₂ = (g * y⁻¹) * (g * y⁻¹) * (g * y⁻¹) * (y * y * y) := by
      simp only [hg₁, hg₂]; group
    have e2 : g * y⁻¹ = t * y * t⁻¹ := by simp only [hg]; group
    rw [e, e2, hs3, hy3']
    group
  have : g₂ ∈ R := by
    have h1 : g₂ = (g * g₁)⁻¹ * (g * g₁ * g₂) := by group
    rw [h1, hrel, mul_one]
    exact R.inv_mem hgg₁
  exact hg₂R this

end GoldAmLab7

end F6

end CFSG.Quasithin
