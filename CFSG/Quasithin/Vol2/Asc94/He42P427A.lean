module

public import CFSG.Quasithin.Vol2.Asc94.He42SE5
public import CFSG.Quasithin.Vol2.Asc94.He42SE6
public import CFSG.Quasithin.Vol2.Asc94.He42BaseFacts

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

structure P427 (T : HeSetup G) (z : G) : Prop where
  hfus : T.StepFus
  hzZ : z ∈ T.Z
  hzm : T.m z = Matrix.of ![![0, 1], ![0, 0]]
  hz2 : z * z = 1
  hL : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L
  hLodd : ∀ K : Subgroup G, K ≤ T.L → (K.subgroupOf T.L).Normal → Odd (Nat.card K) → K ≤ T.B
  hLcard : Nat.card T.L = 80640
  hSp : T.StepSpread
  hfour : ∀ y ∈ T.Z, (T.m y).det ≠ 0 →
    IsPGroup 2 ↥(centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G))
  hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512
  hS3 : ∀ c ∈ centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G), c * c = 1 → c ∉ T.J →
    Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) ⊓
      centralizer ({c} : Set G)) ≤ 32

theorem p427_J_le_cent (T : HeSetup G) (hB : T.BaseFacts) {y : G} (hy : y ∈ T.Z) :
    T.J ≤ centralizer ({y} : Set G) := by
  have hyA : y ∈ T.A := hB.Z_le_A hy
  have hyA' : y ∈ T.A' := hB.Z_le_A' hy
  refine sup_le ?_ ?_
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    exact (hB.A_comm y hyA x hx).symm
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    exact (hB.A'_comm y hyA' x hx).symm

theorem p427_J_le_S (T : HeSetup G) (hB : T.BaseFacts) {z : G} (hz : z ∈ T.Z) (ha : T.a ∈ T.Z) :
    T.J ≤ centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) :=
  le_inf (p427_J_le_cent T hB hz) (p427_J_le_cent T hB ha)

theorem p427_J_relIndex (T : HeSetup G) (hB : T.BaseFacts) {z : G} (hz : z ∈ T.Z)
    (ha : T.a ∈ T.Z) (hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512) :
    T.J.relIndex (centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 2 := by
  have h := Subgroup.relIndex_mul_card T.J (centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G))
  rw [inf_eq_left.2 (p427_J_le_S T hB hz ha), hB.card_J, hS] at h
  omega

theorem p427_J_normal_S (T : HeSetup G) (hB : T.BaseFacts) {z : G} (hz : z ∈ T.Z)
    (ha : T.a ∈ T.Z) (hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512) :
    (T.J.subgroupOf (centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G))).Normal := by
  apply Subgroup.normal_of_index_eq_two
  exact p427_J_relIndex T hB hz ha hS

theorem p427_S_le_N (T : HeSetup G) (hB : T.BaseFacts) {z : G} (hz : z ∈ T.Z)
    (ha : T.a ∈ T.Z) (hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512) :
    centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) ≤ T.N := by
  have hle := p427_J_le_S T hB hz ha
  have hn := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 (p427_J_normal_S T hB hz ha hS)
  rw [T.hN]
  exact hn

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem p427_gl2_cent : ∀ g P Q : HeJ.GL2, g ^ 3 = 1 → g ≠ 1 → ∀ M M' : HeJ.M2, M ≠ 0 →
    g.val * M = M * g.val → g.val * (P.val * M * Q.valᵀ) = (P.val * M * Q.valᵀ) * g.val →
    g.val * M' = M' * g.val → g.val * (P.val * M' * Q.valᵀ) = (P.val * M' * Q.valᵀ) * g.val := by
  decide +kernel

private theorem p427_normalizer_of_conj (S : HeSetup G) {n x : G} (hn : n ∈ S.N)
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
  have hgc := p427_gl2_cent S.g P Q hg3 hg1
  apply Subgroup.mem_normalizer_fintype
  intro y hy
  have hyc := (S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hy
  apply (S.hD.mem_B_iff S.hxN S.hxa S.hx3).2
  refine ⟨S.hD.mem_Z_conj hn hyc.1, ?_⟩
  rw [hmc y hyc.1]
  exact hgc (S.m x) (S.m y) hMne hxc hnxc hyc.2

theorem p427_S_le_normalizer_B (T : HeSetup G) (hB : T.BaseFacts) {z : G} (hz : z ∈ T.Z)
    (ha : T.a ∈ T.Z)
    (hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512)
    (haB : T.a ∈ T.B) (ha1 : T.a ≠ 1) :
    centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) ≤ normalizer (T.B : Set G) := by
  intro s hs
  have hsN : s ∈ T.N := p427_S_le_N T hB hz ha hS hs
  have hsa : s * T.a * s⁻¹ = T.a := by
    have h := (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2)
    rw [h, mul_inv_cancel_right]
  exact p427_normalizer_of_conj T hsN haB ha1 (by rw [hsa]; exact haB)

theorem p427_eq_sylow_of_odd_index {H : Type} [Group H] [Finite H] {P R : Subgroup H}
    (hP : IsPGroup 2 P) (hR : IsPGroup 2 R) (hPR : P ≤ R) (hPi : Odd P.index) : R ≤ P := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have h1 : P.relIndex R * Nat.card ↥(P ⊓ R : Subgroup H) = Nat.card R :=
    Subgroup.relIndex_mul_card P R
  rw [inf_eq_left.2 hPR] at h1
  have hdvd1 : P.relIndex R ∣ 2 ^ k := ⟨Nat.card P, by rw [← hk, ← h1, mul_comm]⟩
  have hdvd2 : P.relIndex R ∣ P.index := ⟨R.index, (Subgroup.relIndex_mul_index hPR).symm⟩
  have hcop : Nat.Coprime (2 ^ k) P.index :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hPi)
  have hrel : P.relIndex R = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
  exact Subgroup.relIndex_eq_one.1 hrel

theorem p427_conj_into {H : Type} [Group H] [Finite H] {P Q : Subgroup H}
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hPi : Odd P.index) :
    ∃ g : H, ∀ q ∈ Q, g⁻¹ * q * g ∈ P := by
  obtain ⟨SP, hPSP⟩ := hP.exists_le_sylow
  have hPeq : (SP : Subgroup H) = P :=
    le_antisymm (p427_eq_sylow_of_odd_index hP SP.isPGroup' hPSP hPi) hPSP
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H SP Q'
  refine ⟨g, fun q hq => ?_⟩
  have hqQ' : q ∈ (Q' : Subgroup H) := hQQ' hq
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hPeq] at hqQ'
  have e : (MulAut.conj g)⁻¹ • q = g⁻¹ * q * g := by
    simp [MulAut.conj_apply]
  rw [e] at hqQ'
  exact hqQ'


end CFSG.Quasithin.A94.He42

