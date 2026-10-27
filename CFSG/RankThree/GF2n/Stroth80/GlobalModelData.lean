module

public import CFSG.RankThree.GF2n.Stroth80.DictModel
public import CFSG.RankThree.GF2n.Stroth80.Basic
public import CFSG.RankThree.GF2n.Stroth80.FieldModelLinear
public import CFSG.RankThree.GF2n.Stroth80.FieldModelFinal
public import CFSG.RankThree.GF2n.Stroth80.FieldModelSimilitude

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem isLine_of_mulData {K : Type} [Field K] {γ : G → K} {Q Z U : Subgroup G}
    (M₀ : Tim79.QuadModel Q Z K γ) (hU : U ≤ Q) (hZU : Z ⊓ U = ⊥)
    (D : Tim79.MulData Z U Q K) {c : K} (σ : K ≃+* K) (hc : c ≠ 0)
    (hcσ : ∀ v ∈ Z, D.γ v = c * σ (γ v)) : M₀.IsLine U := by
  have hcomm : ∀ x ∈ Q, ∀ u ∈ U, M₀.B (M₀.π x) (M₀.π u) =
      σ.symm (c⁻¹ * D.t x) * σ.symm (D.ψ u) := by
    intro x hx u hu
    obtain ⟨hmem, hγ⟩ := D.comm x hx u hu
    rw [← M₀.comm_eq x hx u (hU hu)]
    have h1 := hcσ _ hmem
    rw [hγ] at h1
    have h2 : σ (γ ⁅x, u⁆) = c⁻¹ * (D.t x * D.ψ u) := by
      rw [eq_inv_mul_iff_mul_eq₀ hc, ← h1]
    have h3 : γ ⁅x, u⁆ = σ.symm (c⁻¹ * (D.t x * D.ψ u)) := by
      rw [← h2, RingEquiv.symm_apply_apply]
    rw [h3, ← map_mul]
    congr 1
    ring
  obtain ⟨u₀, hu₀U, hψ₀⟩ := D.ψ_surj 1
  have hu₀Q : u₀ ∈ Q := hU hu₀U
  have hlin : ∀ u ∈ U, M₀.π u = σ.symm (D.ψ u) • M₀.π u₀ := by
    intro u hu
    refine sub_eq_zero.mp (M₀.nondeg _ fun f => ?_)
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj f
    have h := hcomm x hxQ u hu
    have h0 := hcomm x hxQ u₀ hu₀U
    rw [hψ₀, map_one, mul_one] at h0
    have e1 : M₀.B (M₀.π u) (M₀.π x) = - (σ.symm (c⁻¹ * D.t x) * σ.symm (D.ψ u)) := by
      rw [Tim79.QuadModel.B_comm, h]
    have e0 : M₀.B (M₀.π u₀) (M₀.π x) = - σ.symm (c⁻¹ * D.t x) := by
      rw [Tim79.QuadModel.B_comm, h0]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, e1, e0]
    ring
  have hne : M₀.π u₀ ≠ 0 := by
    intro h0
    have h1 : u₀ ∈ Z := (M₀.π_ker _ hu₀Q).mp h0
    have h2 : u₀ ∈ Z ⊓ U := ⟨h1, hu₀U⟩
    rw [hZU, Subgroup.mem_bot] at h2
    rw [h2, D.ψ_one] at hψ₀
    exact zero_ne_one hψ₀
  refine ⟨M₀.π u₀, hne, fun v => ⟨?_, ?_⟩⟩
  · rintro ⟨u, huU, huQ, rfl⟩
    exact ⟨_, hlin u huU⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨u, huU, hu⟩ := D.ψ_surj (σ t)
    refine ⟨u, huU, hU huU, ?_⟩
    rw [hlin u huU, hu, RingEquiv.symm_apply_apply]

structure GlobalModelData (M Q Z : Subgroup G) {K : Type} [Field K] (γ : G → K)
    (M₀ : Tim79.QuadModel Q Z K γ) : Prop where
  reg : Tim79.GammaReg Q Z γ
  card : Nat.card K = Nat.card Z
  hyperbolic : ∃ S₁ S₂ : Submodule K M₀.E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, M₀.Qf x = 0) ∧
    ∀ x ∈ S₂, M₀.Qf x = 0
  line : ∀ g : G, conjSubgroup g Z ≠ Z → conjSubgroup g Z ≤ Q → M₀.IsLine (conjSubgroup g Z)
  act : ∀ m ∈ M, ∃ (σ : K ≃+* K) (a : Kˣ) (T : M₀.E ≃+ M₀.E),
    (∀ (c : K) e, T (c • e) = σ c • T e) ∧
    (∀ x ∈ Q, M₀.π (m * x * m⁻¹) = T (M₀.π x)) ∧
    (∀ z ∈ Z, γ (m * z * m⁻¹) = (a : K) * σ (γ z)) ∧
    ∀ e, M₀.Qf (T e) = (a : K) * σ (M₀.Qf e)

theorem stroth_globalModelDataGF [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) :
    ∃ (n : ℕ) (γ : G → GaloisField 2 n) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 n) γ),
      Nat.card Z = 2 ^ n ∧ GlobalModelData M Q Z γ M₀ := by
  have H79 := H.toHyp79
  obtain ⟨g, hgV, hgQ⟩ := H79.exists_opposite
  obtain ⟨n, hVn, D, M₀, S₁, S₂, hS, hS₁, hS₂⟩ := H79.exists_hyperbolic_quadModel hgV hgQ
  have hcl : Tim79.classGroup Z Q D.γ = Q := FieldModel.classGroup_eq_self H79 hgV hgQ hVn D
  have hZQ : Z ≤ Q := H.Z_normal.1
  refine ⟨n, D.γ, FieldModel.castQuadModel hcl M₀, hVn, ⟨hZQ, D.γ_add, D.γ_inj, D.γ_surj⟩,
    D.natCard_V.symm, ⟨S₁, S₂, hS, hS₁, hS₂⟩, ?_, ?_⟩
  · intro g₂ hg₂V hg₂Q
    obtain ⟨n₂, hVn₂, ⟨D₂⟩⟩ := H79.exists_mulData hg₂V hg₂Q
    have hnn : n = n₂ := Nat.pow_right_injective (le_refl 2) (hVn.symm.trans hVn₂)
    subst hnn
    obtain ⟨c, σ, hc, hcσ⟩ := FieldModel.gammaCompat_of_opposite H79 hgV hgQ hg₂V hg₂Q hVn D D₂
    exact isLine_of_mulData (FieldModel.castQuadModel hcl M₀) hg₂Q
      (inf_conjSubgroup_eq_bot_of_isTI H79.ti hg₂V) D₂ σ hc hcσ
  · intro m hm
    obtain ⟨c, σ, hc, hcσ⟩ := FieldModel.semilinear_of_mem_M H79 hgV hgQ hVn D hm
    have hh := H79.toHyp218 hgV hgQ
    have hmV := hh.M_le_normalizer hm
    have hmQ := hh.M_le_normalizer_Q hm
    have hQF : ∀ x ∈ Tim79.classGroup Z Q D.γ, m * x * m⁻¹ ∈ Tim79.classGroup Z Q D.γ := by
      rw [hcl]; exact fun x hx => (Tim79.mem_iff_conj_of_normalizer hmQ x).mp hx
    have hQF' : ∀ x ∈ Tim79.classGroup Z Q D.γ, m⁻¹ * x * m ∈ Tim79.classGroup Z Q D.γ := by
      rw [hcl]; exact fun x hx => (Tim79.mem_iff_conj_inv_of_normalizer hmQ x).mp hx
    obtain ⟨T, hT1, hT2, hT3⟩ :=
      FieldModel.semilinear_similitude M₀ Tim79.V_le_classGroup σ hmV hQF hQF' hcσ
    refine ⟨σ, Units.mk0 c hc, T, hT1, fun x hx => hT2 x ?_, hcσ, hT3⟩
    rw [hcl]; exact hx

theorem stroth_globalModelData [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ := by
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF H
  exact ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance, γ, M₀, h⟩

variable {M Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem GlobalModelData.linear_of_centralizes (h : GlobalModelData M Q Z γ M₀) {m : G} (hm : m ∈ M)
    (hc : ∀ z ∈ Z, m * z * m⁻¹ = z) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E, (∀ x ∈ Q, M₀.π (m * x * m⁻¹) = T (M₀.π x)) ∧
      (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧ ∀ e f, M₀.B (T e) (T f) = M₀.B e f := by
  obtain ⟨σ, a, T, hT1, hTπ, hTγ, hTQ⟩ := h.act m hm
  obtain ⟨ha, hσ⟩ := FieldModel.scalars_of_centralizes h.reg.surj hTγ hc
  subst hσ
  have hQ : ∀ e, M₀.Qf (T e) = M₀.Qf e := fun e => by rw [hTQ, ha]; simp
  refine ⟨AddEquiv.toLinearEquiv T (fun c x => by rw [hT1]; rfl), hTπ, hQ, fun e f => ?_⟩
  have h1 := M₀.Qf_add (T e) (T f)
  have h2 := M₀.Qf_add e f
  rw [← map_add, hQ, hQ e, hQ f] at h1
  show M₀.B (T e) (T f) = M₀.B e f
  linear_combination h2 - h1

theorem GlobalModelData.conj (h : GlobalModelData M Q Z γ M₀) (g : G) :
    GlobalModelData (conjSubgroup g M) (conjSubgroup g Q) (conjSubgroup g Z)
      (fun x => γ (g⁻¹ * x * g)) (M₀.conj g) where
  reg := h.reg.conj g
  card := by rw [card_conjSubgroup]; exact h.card
  hyperbolic := h.hyperbolic
  line := by
    intro g' hg'Z hg'Q
    set k := g⁻¹ * g' * g with hk
    have hconj : conjSubgroup g' (conjSubgroup g Z) = conjSubgroup g (conjSubgroup k Z) := by
      rw [← conjSubgroup_mul, ← conjSubgroup_mul, hk]
      congr 1
      group
    rw [hconj] at hg'Z hg'Q ⊢
    have hkZ : conjSubgroup k Z ≠ Z := fun e => hg'Z (by rw [e])
    have hkQ : conjSubgroup k Z ≤ Q := by
      intro x hx
      have := hg'Q ⟨x, hx, rfl⟩
      simpa [mem_conjSubgroup, mul_assoc] using this
    obtain ⟨e, he0, he⟩ := h.line k hkZ hkQ
    exact ⟨e, he0, fun v => (Tim79.QuadModel.mem_img_conj M₀ g v).trans (he v)⟩
  act := by
    intro m' hm'
    obtain ⟨σ, a, T, hT1, hTπ, hTγ, hTQ⟩ := h.act (g⁻¹ * m' * g) (mem_conjSubgroup.mp hm')
    refine ⟨σ, a, T, hT1, fun x hx => ?_, fun z hz => ?_, hTQ⟩
    · have := hTπ (g⁻¹ * x * g) (mem_conjSubgroup.mp hx)
      show M₀.π (g⁻¹ * (m' * x * m'⁻¹) * g) = T (M₀.π (g⁻¹ * x * g))
      rw [← this]
      congr 1
      group
    · have := hTγ (g⁻¹ * z * g) (mem_conjSubgroup.mp hz)
      show γ (g⁻¹ * (m' * z * m'⁻¹) * g) = (a : K) * σ (γ (g⁻¹ * z * g))
      rw [← this]
      congr 1
      group

end CFSG.RankThree.GF2n.Stroth80
