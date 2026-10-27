module

public import CFSG.RankThree.GF2n.Stroth80.Swap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.L0_normalizes_Q (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) :
    ∀ y ∈ Q, t * y * t⁻¹ ∈ Q := by
  have : t ∈ M := by rw [← hc.QB_inf_M_eq] at ht; exact ht.2
  exact fun y hy => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 this) y).mp hy

theorem Ctx.act_fix_B (hc : Ctx M Q Z B) {t : G} (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G))
    {T : M₀.E → M₀.E} (hT : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = T (M₀.π y)) :
    ∀ u ∈ B, T (M₀.π u) = M₀.π u := by
  obtain ⟨g, hg⟩ := hc.conj
  intro u hu
  rw [← hT u (hc.le hu)]
  have htQ : t ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ ht.1
  have hu' : u ∈ conjSubgroup g Z := hg ▸ hu
  have := hc.hyp.toHyp79.conj_central g hu' htQ
  rw [← this]
  congr 1
  group

theorem Ctx.act_sub_mem_inf (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) {T : M₀.E → M₀.E}
    (hT : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = T (M₀.π y)) {y : G}
    (hy : y ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ∃ r ∈ Q ⊓ QB B, M₀.π r = T (M₀.π y) - M₀.π y := by
  obtain ⟨g, hg⟩ := hc.conj
  have hyQ := hy.1
  have hty : t * y * t⁻¹ ∈ Q := hc.L0_normalizes_Q ht y hyQ
  refine ⟨⁅t, y⁆, ⟨?_, ?_⟩, ?_⟩
  · rw [commutatorElement_def]
    exact Q.mul_mem hty (Q.inv_mem hyQ)
  ·
    have hyN : y ∈ Subgroup.normalizer (B : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun b hb => ?_
      have hbc := Subgroup.mem_centralizer_iff.mp hy.2 b hb
      have : y * b * y⁻¹ = b := by rw [← hbc]; group
      rw [this]; exact hb
    have hyQB : y ∈ Subgroup.normalizer ((QB B : Subgroup G) : Set G) := by
      have : Subgroup.normalizer (B : Set G) = conjSubgroup g M := (Ctx.QB_eq hc hg).1
      rw [(Ctx.QB_eq hc hg).2, mem_normalizer_conj_iff]
      rw [this] at hyN
      exact hc.hyp.Q_normal.2 (mem_conjSubgroup.mp hyN)
    rw [show ⁅t, y⁆ = t * (y * t⁻¹ * y⁻¹) by rw [commutatorElement_def]; group]
    exact (QB B).mul_mem ht.1 ((Subgroup.mem_normalizer_iff.mp hyQB _).mp ((QB B).inv_mem ht.1))
  · rw [show ⁅t, y⁆ = (t * y * t⁻¹) * y⁻¹ by rw [commutatorElement_def],
      M₀.π_mul _ hty _ (Q.inv_mem hyQ), hT y hyQ, Tim79.QuadModel.pi_inv M₀ hyQ, sub_eq_add_neg]

theorem Ctx.act_comm (hc : Ctx M Q Z B) {s t : G}
    (hs : s ∈ QB B ⊓ Subgroup.centralizer (Z : Set G))
    (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) {S T : M₀.E → M₀.E}
    (hS : ∀ y ∈ Q, M₀.π (s * y * s⁻¹) = S (M₀.π y))
    (hT : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = T (M₀.π y)) : ∀ e, S (T e) = T (S e) := by
  obtain ⟨g, hg⟩ := hc.conj
  intro e
  obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
  have hty : t * y * t⁻¹ ∈ Q := hc.L0_normalizes_Q ht y hyQ
  have hsy : s * y * s⁻¹ ∈ Q := hc.L0_normalizes_Q hs y hyQ
  have hsQB : s ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hs.1
  have htQB : t ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ ht.1
  have hc' : ⁅s, t⁆ ∈ Q := hc.le (hg ▸ hc.hyp.toHyp79.comm_mem_conj g hsQB htQB)
  rw [← hT y hyQ, ← hS y hyQ, ← hS _ hty, ← hT _ hsy]
  have : s * (t * y * t⁻¹) * s⁻¹ = ⁅s, t⁆ * (t * (s * y * s⁻¹) * t⁻¹) * ⁅s, t⁆⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [this, Tim79.QuadModel.pi_conj_self (M₀ := M₀) hc' (hc.L0_normalizes_Q ht _ hsy)]

theorem Ctx.comm_mem_inf (hc : Ctx M Q Z B) {t y : G}
    (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G))
    (hy : y ∈ Q ⊓ Subgroup.centralizer (B : Set G)) : ⁅t, y⁆ ∈ Q ⊓ QB B := by
  obtain ⟨g, hg⟩ := hc.conj
  have hyQ := hy.1
  have hty : t * y * t⁻¹ ∈ Q := hc.L0_normalizes_Q ht y hyQ
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact Q.mul_mem hty (Q.inv_mem hyQ)
  · have hyN : y ∈ Subgroup.normalizer (B : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun b hb => ?_
      have hbc := Subgroup.mem_centralizer_iff.mp hy.2 b hb
      have : y * b * y⁻¹ = b := by rw [← hbc]; group
      rw [this]; exact hb
    have hyQB : y ∈ Subgroup.normalizer ((QB B : Subgroup G) : Set G) := by
      have : Subgroup.normalizer (B : Set G) = conjSubgroup g M := (Ctx.QB_eq hc hg).1
      rw [(Ctx.QB_eq hc hg).2, mem_normalizer_conj_iff]
      rw [this] at hyN
      exact hc.hyp.Q_normal.2 (mem_conjSubgroup.mp hyN)
    rw [show ⁅t, y⁆ = t * (y * t⁻¹ * y⁻¹) by rw [commutatorElement_def]; group]
    exact (QB B).mul_mem ht.1 ((Subgroup.mem_normalizer_iff.mp hyQB _).mp ((QB B).inv_mem ht.1))

theorem Ctx.comm_mem_Z_sup_B (hc : Ctx M Q Z B) {a y : G}
    (ha : a ∈ QB B ⊓ Subgroup.centralizer (Z : Set G))
    (haA : ∀ r ∈ Q ⊓ QB B, ⁅a, r⁆ ∈ Z) (hy : y ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ⁅a, y⁆ ∈ Z ⊔ B := by
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  have hLM : ∀ t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G), t ∈ M := fun t ht => by
    rw [← hc.QB_inf_M_eq] at ht; exact ht.2
  have hLc : ∀ t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G), ∀ z ∈ Z, t * z * t⁻¹ = z :=
    fun t ht z hz => by
      have := Subgroup.mem_centralizer_iff.mp ht.2 z hz
      rw [← this]; group
  have hyQ := hy.1
  set r := ⁅a, y⁆ with hr
  have hrI : r ∈ Q ⊓ QB B := hc.comm_mem_inf ha hy
  have hrQ : r ∈ Q := hrI.1
  have hr₀ : r ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) :=
    ⟨hrI.2, Subgroup.mem_centralizer_iff.mpr fun z hz => hc.hyp.toHyp79.V_central hz hrQ⟩
  obtain ⟨Ta, hTa, -, -⟩ := h.linear_of_centralizes (hLM a ha) (hLc a ha)
  refine (hc.mem_center_iff_L0 hr₀).mp fun s hs => ?_
  obtain ⟨Ts, hTs, -, -⟩ := h.linear_of_centralizes (hLM s hs) (hLc s hs)
  have hcomm := hc.act_comm (M₀ := M₀) ha hs (S := Ta) (T := Ts) hTa hTs
  obtain ⟨r₁, hr₁, hr₁π⟩ := hc.act_sub_mem_inf (M₀ := M₀) hs hTs hy
  have hTs_y : Ts (M₀.π y) = M₀.π y + M₀.π r₁ := by rw [hr₁π]; abel
  have hTa_r₁ : Ta (M₀.π r₁) = M₀.π r₁ := by
    have := (M₀.comm_mem_iff hr₁.1 (hc.L0_normalizes_Q ha r₁ hr₁.1)).mp (haA r₁ hr₁)
    rw [← hTa r₁ hr₁.1]; exact this
  have hπr : M₀.π r = Ta (M₀.π y) - M₀.π y := by
    rw [hr, show ⁅a, y⁆ = (a * y * a⁻¹) * y⁻¹ by rw [commutatorElement_def],
      M₀.π_mul _ (hc.L0_normalizes_Q ha y hyQ) _ (Q.inv_mem hyQ), hTa y hyQ,
      Tim79.QuadModel.pi_inv M₀ hyQ, sub_eq_add_neg]
  have hfix : Ts (M₀.π r) = M₀.π r := by
    rw [hπr, map_sub, ← hcomm, hTs_y, map_add, hTa_r₁]
    abel
  have hsr : s * r * s⁻¹ ∈ Q := hc.L0_normalizes_Q hs r hrQ
  have h1 : ⁅s, r⁆ ∈ Z := (M₀.comm_mem_iff hrQ hsr).mpr (by rw [hTs r hrQ, hfix])
  have hsQB : s ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hs.1
  have hrQB : r ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hrI.2
  have h2 : ⁅s, r⁆ ∈ B := hg ▸ hc.hyp.toHyp79.comm_mem_conj g hsQB hrQB
  have h3 : ⁅s, r⁆ ∈ Z ⊓ B := ⟨h1, h2⟩
  rw [hc.inf_eq_bot, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

end CFSG.RankThree.GF2n.Stroth80
