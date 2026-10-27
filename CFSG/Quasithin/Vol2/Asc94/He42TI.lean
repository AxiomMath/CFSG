module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.HeJ13
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

namespace HeSetup

variable (S : HeSetup G)

@[expose] def StepFus : Prop :=
  ∀ y ∈ S.Z, ∀ y' ∈ S.Z, ∀ g : G, g⁻¹ * y * g = y' → ∃ n ∈ S.N, n⁻¹ * y * n = y'

end HeSetup

@[expose] def Open427 (S : HeSetup G) : Prop :=
  ∀ c : G, c * S.a = S.a * c → c ∈ normalizer (S.B : Set G)

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem he42ti_gl2_cent : ∀ g P Q : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ M M' : M2, M ≠ 0 →
    g.val * M = M * g.val → g.val * (P.val * M * Q.valᵀ) = (P.val * M * Q.valᵀ) * g.val →
    g.val * M' = M' * g.val → g.val * (P.val * M' * Q.valᵀ) = (P.val * M' * Q.valᵀ) * g.val := by
  decide +kernel

private theorem he42ti_normalizer_of_conj (S : HeSetup G) {n x : G} (hn : n ∈ S.N)
    (hx : x ∈ S.B) (hx1 : x ≠ 1) (hnx : n * x * n⁻¹ ∈ S.B) :
    n ∈ normalizer (S.B : Set G) := by
  have hxZ : x ∈ S.A ⊓ S.A' := hx.1
  have hxc : S.g.val * S.m x = S.m x * S.g.val := ((S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hx).2
  have hMne : S.m x ≠ 0 := by
    intro h0
    apply hx1
    apply S.hD.hT.minj x hxZ 1 (one_mem _)
    rw [h0, S.hD.hT.m_one]
  obtain ⟨P, hP⟩ : ∃ P : GL2, P = (S.hD.hT.rho S.N S.hD.hK.norm ⟨n, hn⟩).1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : GL2, Q = (S.hD.hT.rho S.N S.hD.hK.norm ⟨n, hn⟩).2 := ⟨_, rfl⟩
  have hmc : ∀ y ∈ S.A ⊓ S.A', S.m (n * y * n⁻¹) = P.val * S.m y * Q.valᵀ := by
    intro y hy
    rw [hP, hQ]
    exact S.hD.hT.m_conj S.N S.hD.hK.norm ⟨n, hn⟩ hy
  have hnxc : S.g.val * (P.val * S.m x * Q.valᵀ) = (P.val * S.m x * Q.valᵀ) * S.g.val := by
    have h := ((S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hnx).2
    rwa [hmc x hxZ] at h
  have hg3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hgc := he42ti_gl2_cent S.g P Q hg3 hg1
  apply Subgroup.mem_normalizer_fintype
  intro y hy
  have hyc := (S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hy
  apply (S.hD.mem_B_iff S.hxN S.hxa S.hx3).2
  refine ⟨S.hD.mem_Z_conj hn hyc.1, ?_⟩
  rw [hmc y hyc.1]
  exact hgc (S.m x) (S.m y) hMne hxc hnxc hyc.2

private theorem he42ti_normalizer_of_centralizer (S : HeSetup G) (h427 : Open427 S) {x : G}
    (hx : x ∈ S.B) (hx1 : x ≠ 1) {c : G} (hc : c * x = x * c) :
    c ∈ normalizer (S.B : Set G) := by
  have h427' : ∀ c : G, c * S.a = S.a * c → c ∈ normalizer (S.B : Set G) := h427
  have hg1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  obtain ⟨b, hb, hbm⟩ := S.hD.exists_b S.hxN S.hxa S.hx3
  have hbm' : S.m b = S.g.val := hbm
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply Units.ne_zero S.g
    rw [← hbm', S.hD.hT.m_one]
  have hba : b ≠ S.a := by
    rintro rfl
    apply hg1
    apply Units.ext
    rw [Units.val_one, ← hbm', S.hD.ham]
  obtain ⟨r, -, hrB, hra, hrb⟩ := S.hD.exists_rot_B S.hxN S.hxa S.hx3 hb hb1 hba hbm'
  have hrB' : r ∈ normalizer (S.B : Set G) := hrB
  have hBel := S.hD.B_elems S.hxN S.hxa S.hx3 hb hb1 hba
  have hback : ∀ c' : G, r⁻¹ * c' * r ∈ normalizer (S.B : Set G) →
      c' ∈ normalizer (S.B : Set G) := by
    intro c' h
    convert mul_mem (mul_mem hrB' h) (inv_mem hrB') using 1
    group
  have hDb : ∀ c' : G, c' * b = b * c' → c' ∈ normalizer (S.B : Set G) := by
    intro c' hc'
    apply hback
    apply h427'
    have ha : S.a = r⁻¹ * b * r := by rw [← hra]; group
    calc r⁻¹ * c' * r * S.a = r⁻¹ * c' * r * (r⁻¹ * b * r) := by rw [← ha]
      _ = r⁻¹ * (c' * b) * r := by group
      _ = r⁻¹ * (b * c') * r := by rw [hc']
      _ = (r⁻¹ * b * r) * (r⁻¹ * c' * r) := by group
      _ = S.a * (r⁻¹ * c' * r) := by rw [← ha]
  have hDab : ∀ c' : G, c' * (S.a * b) = (S.a * b) * c' → c' ∈ normalizer (S.B : Set G) := by
    intro c' hc'
    apply hback
    apply hDb
    have hb' : b = r⁻¹ * (S.a * b) * r := by rw [← hrb]; group
    calc r⁻¹ * c' * r * b = r⁻¹ * c' * r * (r⁻¹ * (S.a * b) * r) := by rw [← hb']
      _ = r⁻¹ * (c' * (S.a * b)) * r := by group
      _ = r⁻¹ * ((S.a * b) * c') * r := by rw [hc']
      _ = (r⁻¹ * (S.a * b) * r) * (r⁻¹ * c' * r) := by group
      _ = b * (r⁻¹ * c' * r) := by rw [← hb']
  rcases hBel x hx with h | h | h | h
  · exact absurd h hx1
  · rw [h] at hc
    exact h427' c hc
  · rw [h] at hc
    exact hDb c hc
  · rw [h] at hc
    exact hDab c hc

theorem HeSetup.tightlyEmbedded_of (S : HeSetup G) (hB : S.BaseFacts) (hF : S.StepFus)
    (h427 : Open427 S) : TightlyEmbedded S.B := by
  unfold TightlyEmbedded
  refine ⟨⟨2, hB.card_B⟩, fun g hg => ?_⟩
  have hbot : S.B ⊓ rightConjugate S.B g = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    obtain ⟨hxB, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxc' : g * x * g⁻¹ ∈ S.B := (mem_rightConjugate_iff S.B g x).1 hxc
    have hxZ : x ∈ S.Z := hB.B_le_Z hxB
    have hyZ : g * x * g⁻¹ ∈ S.Z := hB.B_le_Z hxc'
    obtain ⟨n, hnN, hn⟩ := hF (g * x * g⁻¹) hyZ x hxZ g (by group)
    have hnx' : n * x * n⁻¹ = g * x * g⁻¹ := by
      calc n * x * n⁻¹ = n * (n⁻¹ * (g * x * g⁻¹) * n) * n⁻¹ := by rw [hn]
        _ = g * x * g⁻¹ := by group
    have hnB : n * x * n⁻¹ ∈ S.B := by rw [hnx']; exact hxc'
    have hnN' := he42ti_normalizer_of_conj S hnN hxB hx1 hnB
    have hcomm : g⁻¹ * n * x = x * (g⁻¹ * n) := by
      calc g⁻¹ * n * x = g⁻¹ * (n * x * n⁻¹) * n := by group
        _ = g⁻¹ * (g * x * g⁻¹) * n := by rw [hnx']
        _ = x * (g⁻¹ * n) := by group
    have hcN := he42ti_normalizer_of_centralizer S h427 hxB hx1 hcomm
    apply hg
    convert mul_mem hnN' (inv_mem hcN) using 1
    group
  rw [hbot, Subgroup.card_bot]
  exact odd_one

end CFSG.Quasithin.A94.He42
