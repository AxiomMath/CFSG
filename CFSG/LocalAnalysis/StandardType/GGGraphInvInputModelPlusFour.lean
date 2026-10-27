module

public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms

private def ggOmW6d_concl {C : Type} [Group C] (α : MulAut C) : Prop :=
  GGOutTwoPartLeTwo C ∧ GGGraphInvFixClauses α

private theorem ggOmW6d_mem_fixSubgroup_conj {C : Type} [Group C] (β α : MulAut C) (g : C) :
    g ∈ ggFixSubgroup (β * α * β⁻¹) ↔ β⁻¹ g ∈ ggFixSubgroup α := by
  show (β * α * β⁻¹) g = g ↔ α (β⁻¹ g) = β⁻¹ g
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
  constructor
  · intro h
    simpa using congrArg β.symm h
  · intro h
    rw [h]
    simp

private theorem ggOmW6d_map_fixSubgroup {C : Type} [Group C] (β α : MulAut C) :
    (ggFixSubgroup α).map β.toMonoidHom = ggFixSubgroup (β * α * β⁻¹) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (ggOmW6d_mem_fixSubgroup_conj β α (β y)).mpr (by simpa using hy)
  · intro hx
    refine ⟨β⁻¹ x, (ggOmW6d_mem_fixSubgroup_conj β α x).mp hx, ?_⟩
    simp

private theorem ggOmW6dA_centralizer_image {C : Type} [Group C] (β : MulAut C) (s : Set C) :
    Subgroup.centralizer (β '' s) = (Subgroup.centralizer s).map β.toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine ⟨β⁻¹ x, ?_, ?_⟩
    · show β⁻¹ x ∈ Subgroup.centralizer s
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := hx (β y) (Set.mem_image_of_mem β hy)
      simpa [mul_assoc] using congrArg β.symm h
    · simp
  · rintro ⟨y, hy, rfl⟩
    have hyc : ∀ h ∈ s, h * y = y * h := Subgroup.mem_centralizer_iff.mp hy
    show ∀ z ∈ β '' s, z * β y = β y * z
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp only [← map_mul, hyc w hw]

private theorem ggOmW6d_centralizer_map {C : Type} [Group C] (β : MulAut C)
    (S : Subgroup C) :
    Subgroup.centralizer (S.map β.toMonoidHom : Set C) =
      (Subgroup.centralizer (S : Set C)).map β.toMonoidHom := by
  rw [Subgroup.coe_map]
  exact ggOmW6dA_centralizer_image β (S : Set C)

private theorem ggOmW6d_clauses_conj {C : Type} [Group C] (β α : MulAut C)
    (h : GGGraphInvFixClauses α) : GGGraphInvFixClauses (β * α * β⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hNle hNp hNnorm
    have hN'le : N.map (β⁻¹).toMonoidHom ≤ ggFixSubgroup α := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
      exact (ggOmW6d_mem_fixSubgroup_conj β α n).mp (hNle hn)
    have hN'p : IsPGroup 2 (N.map (β⁻¹).toMonoidHom) := hNp.map (β⁻¹).toMonoidHom
    have hN'norm : ∀ y ∈ N.map (β⁻¹).toMonoidHom,
        ∀ z ∈ ggFixSubgroup α, z * y * z⁻¹ ∈ N.map (β⁻¹).toMonoidHom := by
      intro y hy z hz
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
      have hβz : β z ∈ ggFixSubgroup (β * α * β⁻¹) :=
        (ggOmW6d_mem_fixSubgroup_conj β α (β z)).mpr (by simpa using hz)
      have hmem : β z * n * (β z)⁻¹ ∈ N := hNnorm n hn (β z) hβz
      have heq : β⁻¹ (β z * n * (β z)⁻¹) = z * β⁻¹ n * z⁻¹ := by
        simp only [map_mul, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply, mul_assoc]
      change z * β⁻¹ n * z⁻¹ ∈ N.map (β⁻¹).toMonoidHom
      rw [← heq]
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    have hbot : N.map (β⁻¹).toMonoidHom = ⊥ := h.1 _ hN'le hN'p hN'norm
    exact (Subgroup.map_eq_bot_iff_of_injective (H := N) (f := (β⁻¹).toMonoidHom)
      (β⁻¹).injective).mp hbot
  · intro hp
    have hconj : (β⁻¹) * (β * α * β⁻¹) * (β⁻¹)⁻¹ = α := by group
    have hfixeq : (ggFixSubgroup (β * α * β⁻¹)).map (β⁻¹).toMonoidHom = ggFixSubgroup α := by
      rw [ggOmW6d_map_fixSubgroup, hconj]
    have hp' : IsPGroup 2 ↥(ggFixSubgroup α) := by
      have := hp.map (β⁻¹).toMonoidHom
      rwa [hfixeq] at this
    exact h.2.1 hp'
  · calc
      Subgroup.centralizer ((ggFixSubgroup (β * α * β⁻¹) : Subgroup C) : Set C)
          = Subgroup.centralizer (((ggFixSubgroup α).map β.toMonoidHom : Subgroup C) : Set C) := by
            rw [← ggOmW6d_map_fixSubgroup β α]
      _ = (Subgroup.centralizer ((ggFixSubgroup α : Subgroup C) : Set C)).map β.toMonoidHom :=
            ggOmW6d_centralizer_map β (ggFixSubgroup α)
      _ = ⊥ := by rw [h.2.2, Subgroup.map_bot]

private theorem ggOmW6d_concl_conj {C : Type} [Group C] (β α : MulAut C)
    (h : ggOmW6d_concl α) : ggOmW6d_concl (β * α * β⁻¹) :=
  ⟨h.1, ggOmW6d_clauses_conj β α h.2⟩

private theorem ggOmW6dA_centralizer_singleton {C : Type} [Group C] (β : MulAut C) (b : C) :
    Subgroup.centralizer ({β b} : Set C) =
      (Subgroup.centralizer ({b} : Set C)).map β.toMonoidHom := by
  rw [← Set.image_singleton]
  exact ggOmW6dA_centralizer_image β {b}

private theorem ggOmW6d_component_conj {C : Type} [Group C] (β : MulAut C) (b : C)
    (h : ∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {b})) :
    ∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {β b}) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L.map β.toMonoidHom, ?_, ?_, ?_⟩
  · rw [ggOmW6dA_centralizer_singleton]
    exact Subgroup.map_mono hL.1
  · have hsub := hL.2.1.map β.toMonoidHom
    rw [← ggOmW6dA_centralizer_singleton] at hsub
    exact hsub
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupMap β L).symm hL.2.2

private theorem ggOmW6dA_conj_conj {C : Type} [Group C] (β : MulAut C) (c : C) :
    β⁻¹ * MulAut.conj c * β = MulAut.conj (β⁻¹ c) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, mul_assoc]

private theorem ggOmW6d_hyps_conj {C : Type} [Group C] (β : MulAut C) (p : ℕ) (b : C)
    (α : MulAut C) (hb : b ≠ 1) (hbp : b ^ p = 1) (hα2 : α * α = 1)
    (hout : ∀ c : C, α ≠ MulAut.conj c) (hαb : α b = b)
    (hcomp : ∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {b}))
    (hcent : ∀ g ∈ Subgroup.centralizer {b}, α g = g) :
    (β b) ≠ 1 ∧ (β b) ^ p = 1 ∧ (β * α * β⁻¹) * (β * α * β⁻¹) = 1 ∧
      (∀ c : C, β * α * β⁻¹ ≠ MulAut.conj c) ∧
      (β * α * β⁻¹) (β b) = β b ∧
      (∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {β b})) ∧
      (∀ g ∈ Subgroup.centralizer {β b}, (β * α * β⁻¹) g = g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ggOmW6d_component_conj β b hcomp, ?_⟩
  · intro h
    exact hb (β.injective (by simpa using h))
  · simpa using congrArg β hbp
  · calc (β * α * β⁻¹) * (β * α * β⁻¹) = β * (α * α) * β⁻¹ := by group
      _ = 1 := by rw [hα2, mul_one, mul_inv_cancel]
  · intro c h
    have hcc : β⁻¹ * MulAut.conj c * β = MulAut.conj (β⁻¹ c) := ggOmW6dA_conj_conj β c
    have h2 := congrArg (fun f : MulAut C => β⁻¹ * f * β) h
    rw [hcc] at h2
    have h3 : α = MulAut.conj (β⁻¹ c) := by
      rw [← h2]
      group
    exact hout (β⁻¹ c) h3
  · simp [MulAut.mul_apply, hαb]
  · intro g hg
    have hg' : β⁻¹ g ∈ Subgroup.centralizer ({b} : Set C) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have h := congrArg (fun x : C => β⁻¹ x) hg
      simpa [mul_assoc] using h
    have hfix := hcent (β⁻¹ g) hg'
    simp only [MulAut.mul_apply]
    rw [hfix]
    simp

private theorem ggOmW6d_of_normalForm {C : Type} [Group C] (A : Subgroup (MulAut C))
    (hA : ∀ (p : ℕ) (b : C) (α : MulAut C), p.Prime → p ≠ 2 → b ≠ 1 → b ^ p = 1 →
      α * α = 1 → (∀ c : C, α ≠ MulAut.conj c) → α b = b →
      (∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {b})) →
      (∀ g ∈ Subgroup.centralizer {b}, α g = g) → α ∈ A → ggOmW6d_concl α)
    (hnorm : ∀ (p : ℕ) (b : C) (α : MulAut C), p.Prime → p ≠ 2 → b ≠ 1 → b ^ p = 1 →
      α * α = 1 → (∀ c : C, α ≠ MulAut.conj c) → α b = b →
      (∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {b})) →
      (∀ g ∈ Subgroup.centralizer {b}, α g = g) →
      ∃ β : MulAut C, β * α * β⁻¹ ∈ A) :
    GGGraphInvInputModel C := by
  intro p b α hp hp2 hb hbp hα2 hout hαb hcomp hcent
  obtain ⟨β, hβA⟩ := hnorm p b α hp hp2 hb hbp hα2 hout hαb hcomp hcent
  obtain ⟨hb', hbp', hα2', hout', hαb', hcomp', hcent'⟩ :=
    ggOmW6d_hyps_conj β p b α hb hbp hα2 hout hαb hcomp hcent
  have hconj := hA p (β b) (β * α * β⁻¹) hp hp2 hb' hbp' hα2' hout' hαb' hcomp' hcent' hβA
  have hback := ggOmW6d_concl_conj β⁻¹ (β * α * β⁻¹) hconj
  have hαeq : β⁻¹ * (β * α * β⁻¹) * (β⁻¹)⁻¹ = α := by group
  rw [hαeq] at hback
  exact hback

private theorem ggOmW6dC_inner_sq {G : Type*} [Group G] {ι β : MulAut G}
    (hι : ι ∈ inner G) (h : (ι * β) * (ι * β) = 1) : β * β ∈ inner G := by
  have h1 : (ι * (β * ι * β⁻¹)) * (β * β) = 1 := by
    rw [show (ι * (β * ι * β⁻¹)) * (β * β) = (ι * β) * (ι * β) by group, h]
  have h2 : β * β = (ι * (β * ι * β⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact (inner G).inv_mem ((inner G).mul_mem hι ((inner_normal G).conj_mem ι hι β))

private theorem ggOmW6dC_conj_pow_inv {M : Type*} [Group M] {t r : M}
    (hr : r * r = 1) (hrt : r * t * r = t⁻¹) (k : ℕ) : r * t ^ k * r = (t ^ k)⁻¹ := by
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_left hr
  calc r * t ^ k * r = MulAut.conj r (t ^ k) := by rw [MulAut.conj_apply, hrinv]
    _ = (MulAut.conj r t) ^ k := map_pow (MulAut.conj r) t k
    _ = (t⁻¹) ^ k := by
        rw [show MulAut.conj r t = t⁻¹ by rw [MulAut.conj_apply, hrinv, hrt]]
    _ = (t ^ k)⁻¹ := by rw [inv_pow]

private theorem ggOmW6dC_mul_inv_pow_of_conj {M : Type*} [Group M] {t r : M}
    (hr : r * r = 1) (hrt : r * t * r = t⁻¹) (k : ℕ) : r * (t ^ k)⁻¹ = t ^ k * r := by
  have h := ggOmW6dC_conj_pow_inv hr hrt k
  calc r * (t ^ k)⁻¹ = r * (r * t ^ k * r) := by rw [← h]
    _ = (r * r) * (t ^ k * r) := by group
    _ = t ^ k * r := by rw [hr, one_mul]

private theorem ggOmW6dC_theta_mul_commute_sq {M : Type*} [Group M] {t f : M}
    (htf : t * f = f * t) (k : ℕ) : (t ^ k * f) * (t ^ k * f) = t ^ (k + k) * (f * f) := by
  have hft : f * t ^ k = t ^ k * f :=
    ((show Commute f t from htf.symm).pow_right k).eq
  calc (t ^ k * f) * (t ^ k * f) = t ^ k * (f * t ^ k) * f := by group
    _ = t ^ k * (t ^ k * f) * f := by rw [hft]
    _ = t ^ (k + k) * (f * f) := by
        rw [show t ^ k * (t ^ k * f) * f = (t ^ k * t ^ k) * (f * f) by group, ← pow_add]

private theorem ggOmW6dC_theta_pow_eq_one_of_add {M : Type*} [Group M] {t : M}
    (ht : t ^ 3 = 1) {k : ℕ} (h : t ^ (k + k) = 1) : t ^ k = 1 := by
  have h3 : t ^ (3 * k) = 1 := by rw [pow_mul, ht, one_pow]
  have h4 : t ^ (k + k) * t ^ k = 1 := by
    rw [← pow_add, show k + k + k = 3 * k by ring, h3]
  rwa [h, one_mul] at h4

private theorem ggOmW6dC_conj_graph_core {M : Type*} [Group M] {t r f : M}
    (ht : t ^ 3 = 1) (hr : r * r = 1) (hrt : r * t * r = t⁻¹)
    (htf : t * f = f * t) (k : ℕ) :
    (t ^ k * t ^ k) * (r * f) * (t ^ k)⁻¹ = r * f := by
  have hft : f * (t ^ k)⁻¹ = (t ^ k)⁻¹ * f :=
    (((show Commute f t from htf.symm).pow_right k).inv_right).eq
  have hrt' : r * (t ^ k)⁻¹ = t ^ k * r := ggOmW6dC_mul_inv_pow_of_conj hr hrt k
  have h3k : t ^ (3 * k) = 1 := by rw [pow_mul, ht, one_pow]
  calc (t ^ k * t ^ k) * (r * f) * (t ^ k)⁻¹
      = t ^ (k + k) * r * (f * (t ^ k)⁻¹) := by
        rw [← pow_add]; group
    _ = t ^ (k + k) * r * ((t ^ k)⁻¹ * f) := by rw [hft]
    _ = t ^ (k + k) * (r * (t ^ k)⁻¹) * f := by group
    _ = t ^ (k + k) * (t ^ k * r) * f := by rw [hrt']
    _ = (t ^ (k + k) * t ^ k) * r * f := by group
    _ = t ^ (3 * k) * r * f := by rw [← pow_add, show k + k + k = 3 * k by ring]
    _ = r * f := by rw [h3k, one_mul]

private theorem ggOmW6d_plusFour_normalForm {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : MulAut (Triality.Om8 K)) (hα2 : α * α = 1) :
    ∃ β : MulAut (Triality.Om8 K),
      β * α * β⁻¹ ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner (Triality.Om8 K)) ⊔
        AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4) := by
  obtain ⟨ι, hι, k, c, hc, hα⟩ := Triality.exists_inner_mul_theta_pow_mul α
  obtain ⟨σ, hσ | hσ⟩ := (AutOm.mem_plusCompl (K := K)).mp hc
  ·
    have hf : AutOm.fieldAutP 4 σ ∈ AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4) :=
      hσ ▸ hc
    have hα' : α = ι * ((Triality.theta : MulAut (Triality.Om8 K)) ^ k *
        AutOm.fieldAutP 4 σ) := by rw [hα, hσ]
    have hsq : ((Triality.theta : MulAut (Triality.Om8 K)) ^ k * AutOm.fieldAutP 4 σ) *
        ((Triality.theta : MulAut (Triality.Om8 K)) ^ k * AutOm.fieldAutP 4 σ) ∈
        inner (Triality.Om8 K) := by
      refine ggOmW6dC_inner_sq hι ?_
      rw [← hα']
      exact hα2
    rw [ggOmW6dC_theta_mul_commute_sq (t := Triality.theta)
      (f := AutOm.fieldAutP 4 σ) (Triality.theta_fieldAutP σ) k] at hsq
    obtain ⟨hk_add, -⟩ :=
      Triality.theta_pow_mul_mem_inner (k + k) (mul_mem hf hf) hsq
    have hk1 : (Triality.theta : MulAut (Triality.Om8 K)) ^ k = 1 :=
      ggOmW6dC_theta_pow_eq_one_of_add Triality.theta_cube hk_add
    refine ⟨1, ?_⟩
    rw [one_mul, inv_one, mul_one, hα', hk1, one_mul]
    exact mul_mem (Subgroup.mem_sup_left hι) (Subgroup.mem_sup_right hf)
  ·
    have hrf : AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) * AutOm.fieldAutP 4 σ ∈
        AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4) := hσ ▸ hc
    have hρ2 : AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) *
        AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) = 1 :=
      AutOm.plusRefl_mul_self (K := K) (by norm_num : 1 ≤ 4)
    have hρθ : AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) *
        (Triality.theta : MulAut (Triality.Om8 K)) *
        AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) =
        (Triality.theta : MulAut (Triality.Om8 K))⁻¹ := by
      simpa using Triality.plusRefl_theta_plusRefl (K := K)
    have hθφ : (Triality.theta : MulAut (Triality.Om8 K)) * AutOm.fieldAutP 4 σ =
        AutOm.fieldAutP 4 σ * (Triality.theta : MulAut (Triality.Om8 K)) :=
      Triality.theta_fieldAutP σ
    have hα' : α = ι * ((Triality.theta : MulAut (Triality.Om8 K)) ^ k *
        (AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) * AutOm.fieldAutP 4 σ)) := by
      rw [hα, hσ]
    refine ⟨(Triality.theta : MulAut (Triality.Om8 K)) ^ k, ?_⟩
    have hstep : (Triality.theta : MulAut (Triality.Om8 K)) ^ k * α *
        ((Triality.theta : MulAut (Triality.Om8 K)) ^ k)⁻¹ =
        ((Triality.theta : MulAut (Triality.Om8 K)) ^ k * ι *
          ((Triality.theta : MulAut (Triality.Om8 K)) ^ k)⁻¹) *
        (((Triality.theta : MulAut (Triality.Om8 K)) ^ k *
          (Triality.theta : MulAut (Triality.Om8 K)) ^ k) *
          (AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4) * AutOm.fieldAutP 4 σ) *
          ((Triality.theta : MulAut (Triality.Om8 K)) ^ k)⁻¹) := by
      rw [hα']
      group
    rw [hstep, ggOmW6dC_conj_graph_core Triality.theta_cube hρ2 hρθ hθφ k]
    exact mul_mem
      (Subgroup.mem_sup_left ((inner_normal (Triality.Om8 K)).conj_mem ι hι _))
      (Subgroup.mem_sup_right hrf)

private theorem ggOmW6dB_eq_zero_or_eq_one {K : Type} [Field K]
    (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    obtain ⟨y, _, hyu⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    exact (hyu x hx).trans (hyu 1 one_ne_zero).symm

private theorem ggOmW6dB_ringEquiv_eq_one {K : Type} [Field K]
    (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases ggOmW6dB_eq_zero_or_eq_one hK x with rfl | rfl
  · simp
  · simp

private theorem ggOmW6dB_card_dvd_six_of_decomp {Q : Type} [Group Q]
    (x y : Q) (hx : x ^ 3 = 1) (hy : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹)
    (hgen : ∀ z : Q, (∃ k : ℕ, z = x ^ k) ∨ (∃ k : ℕ, z = x ^ k * y)) :
    Nat.card Q ∣ 6 := by
  set A : Subgroup Q := Subgroup.zpowers x with hA
  have hy_norm : y ∈ Subgroup.normalizer (A : Set Q) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hA, MonoidHom.map_zpowers]
    have hconj : (MulAut.conj y : Q →* Q) x = x⁻¹ := by
      change y * x * y⁻¹ = x⁻¹
      exact hyx
    rw [hconj, Subgroup.zpowers_inv]
  have hnormal : A.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    rw [eq_top_iff]
    intro z _
    rcases hgen z with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact Subgroup.le_normalizer (show x ^ k ∈ A from Subgroup.npow_mem_zpowers x k)
    · exact mul_mem
        (Subgroup.le_normalizer (show x ^ k ∈ A from Subgroup.npow_mem_zpowers x k))
        hy_norm
  haveI : A.Normal := hnormal
  have hA3 : Nat.card A ∣ 3 := by
    rw [hA, Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hx
  have hAbar2 : Nat.card (Q ⧸ A) ∣ 2 := by
    let ybar : Q ⧸ A := QuotientGroup.mk' A y
    have htop : Subgroup.zpowers ybar = ⊤ := by
      rw [eq_top_iff]
      intro z _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A z
      rcases hgen g with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [map_pow]
        have hx1 : QuotientGroup.mk' A x = 1 :=
          (QuotientGroup.eq_one_iff x).mpr (show x ∈ A from Subgroup.mem_zpowers x)
        rw [hx1, one_pow]
        exact Subgroup.one_mem _
      · rw [map_mul, map_pow]
        have hx1 : QuotientGroup.mk' A x = 1 :=
          (QuotientGroup.eq_one_iff x).mpr (show x ∈ A from Subgroup.mem_zpowers x)
        rw [hx1, one_pow, one_mul]
        exact Subgroup.mem_zpowers ybar
    have hcard : Nat.card (Q ⧸ A) = orderOf ybar := by
      rw [← Subgroup.card_top (G := Q ⧸ A), ← htop, Nat.card_zpowers]
    rw [hcard]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hy, map_one])
  calc Nat.card Q = Nat.card (Q ⧸ A) * Nat.card A :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup A
    _ ∣ 2 * 3 := Nat.mul_dvd_mul hAbar2 hA3
    _ = 6 := by norm_num

private theorem ggOmW6dB_index_le_two_of_card_quotient {C : Type} [Group C] [Finite C]
    (I : Subgroup C) [I.Normal] (hI : Nat.card (C ⧸ I) ∣ 6) (S : Subgroup C)
    (hS : IsPGroup 2 S) : (I.subgroupOf S).index ≤ 2 := by
  let f : C →* C ⧸ I := QuotientGroup.mk' I
  have hfker : f.ker = I := QuotientGroup.ker_mk' I
  have hrel : (I.subgroupOf S).index = Nat.card (S.map f) := by
    have h := Subgroup.relIndex_ker (K := S) f
    rw [hfker] at h
    exact h
  rw [hrel]
  have hT2 : IsPGroup 2 (S.map f) := hS.map f
  have hTdvd : Nat.card (S.map f) ∣ 6 :=
    dvd_trans (Subgroup.card_subgroup_dvd_card _) hI
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hpow : 2 ^ n ∣ 6 := by rw [← hn]; exact hTdvd
  have hnle : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have h4 : 4 ∣ 2 ^ n := by
      obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [hm, pow_add, show (2 : ℕ) ^ 2 = 4 from by norm_num, mul_comm]
      exact dvd_mul_right 4 (2 ^ m)
    have h46 : 4 ∣ 6 := dvd_trans h4 hpow
    norm_num at h46
  calc Nat.card (S.map f) = 2 ^ n := hn
    _ ≤ 2 := by
        calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hnle
          _ = 2 := by norm_num

private theorem ggOmW6dB_GGOutTwoPartLeTwo_of_triality {C : Type} [Group C] [Finite C]
    (θ ρ : MulAut C) (hθ3 : θ ^ 3 = 1) (hρ2 : ρ ^ 2 = 1) (hρθ : ρ * θ * ρ = θ⁻¹)
    (hgen : ∀ α : MulAut C, ∃ ι ∈ (MulAut.conj : C →* MulAut C).range, ∃ k : ℕ,
      ∃ c : MulAut C, (c = 1 ∨ c = ρ) ∧ α = ι * (θ ^ k * c)) :
    GGOutTwoPartLeTwo C := by
  set I : Subgroup (MulAut C) := (MulAut.conj : C →* MulAut C).range with hI
  haveI : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal C
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
  let x : MulAut C ⧸ I := QuotientGroup.mk' I θ
  let y : MulAut C ⧸ I := QuotientGroup.mk' I ρ
  have hx : x ^ 3 = 1 := by
    show (QuotientGroup.mk' I θ) ^ 3 = 1
    rw [← map_pow, hθ3, map_one]
  have hy : y ^ 2 = 1 := by
    show (QuotientGroup.mk' I ρ) ^ 2 = 1
    rw [← map_pow, hρ2, map_one]
  have hyx : y * x * y⁻¹ = x⁻¹ := by
    show QuotientGroup.mk' I ρ * QuotientGroup.mk' I θ * (QuotientGroup.mk' I ρ)⁻¹ =
      (QuotientGroup.mk' I θ)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, hρinv, hρθ, ← map_inv]
  have hgenQ : ∀ z : MulAut C ⧸ I,
      (∃ k : ℕ, z = x ^ k) ∨ (∃ k : ℕ, z = x ^ k * y) := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective I z
    obtain ⟨ι, hι, k, c, hc, hgc⟩ := hgen g
    have hι1 : QuotientGroup.mk' I ι = 1 := (QuotientGroup.eq_one_iff ι).mpr hι
    rcases hc with rfl | rfl
    · left
      refine ⟨k, ?_⟩
      rw [hgc, map_mul, map_mul, map_pow, hι1, one_mul, map_one, mul_one]
    · right
      refine ⟨k, ?_⟩
      rw [hgc, map_mul, map_mul, map_pow, hι1, one_mul]
  have hQcard : Nat.card (MulAut C ⧸ I) ∣ 6 :=
    ggOmW6dB_card_dvd_six_of_decomp x y hx hy hyx hgenQ
  intro S hS
  exact ggOmW6dB_index_le_two_of_card_quotient I hQcard S hS

private theorem ggOmW6d_outTwoPart_om8_of_card_two {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) : GGOutTwoPartLeTwo (Triality.Om8 K) := by
  obtain ⟨θ, hθ3, hρθ, -, hgen, -, -⟩ :=
    CFSG.StandardType.plusFourTrialityInput_holds K
  let ρ : MulAut (Triality.Om8 K) :=
    AutOm.plusRefl (K := K) (by norm_num : 1 ≤ 4)
  have hρ2 : ρ * ρ = 1 := AutOm.plusRefl_mul_self (by norm_num : 1 ≤ 4)
  refine ggOmW6dB_GGOutTwoPartLeTwo_of_triality θ ρ hθ3 hρ2 ?_ ?_
  · exact hρθ
  · intro α
    obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen α
    obtain ⟨σ, hσ | hσ⟩ := AutOm.mem_plusCompl.mp hc
    · refine ⟨ι, hι, k, 1, Or.inl rfl, ?_⟩
      rw [hα, hσ, ggOmW6dB_ringEquiv_eq_one hK σ, map_one, mul_one]
    · refine ⟨ι, hι, k, ρ, Or.inr rfl, ?_⟩
      rw [hα, hσ, ggOmW6dB_ringEquiv_eq_one hK σ, map_one, mul_one]

theorem ggGraphInvInputModel_plus_four {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGGraphInvInputModel (Triality.Om8 K) := by
  refine ggOmW6d_of_normalForm
    ((CFSG.ComponentClassification.OuterAutomorphisms.inner (Triality.Om8 K)) ⊔
      (AutOm.plusCompl (K := K) (by norm_num : 1 ≤ 4))) ?_ ?_
  · intro p b α hp hp2 hb hbp hα2 hout hαb hcomp hcent hmem
    obtain ⟨hK2, hclauses⟩ :=
      ggGraphInvInputModel_plus_clauses (K := K) (n := 4) (by norm_num) p b α hp hp2 hb hbp
        hα2 hout hαb hcomp hcent hmem
    exact ⟨ggOmW6d_outTwoPart_om8_of_card_two hK2, hclauses⟩
  · intro p b α hp hp2 hb hbp hα2 hout hαb hcomp hcent
    exact ggOmW6d_plusFour_normalForm α hα2

end CFSG.StandardType
