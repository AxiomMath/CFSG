module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Smith81.Sec1Types

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem Xbar_le_bar_Lgen (hc : Ctx M Q Z B) :
    Xbar M Q Z B ≤ bar M Q (Lgen M (LB M Q B)) := by
  unfold Xbar
  refine (Subgroup.closure_le _).mpr ?_
  intro τ hτ
  obtain ⟨-, x, hx⟩ := hτ
  have h1 : x * τ * x⁻¹ ∈ bar M Q (Lgen M (LB M Q B)) :=
    hc.bar_LB_le_bar_Lgen hx
  have h2 := hc.normal_bar_Lgen.conj_mem' (x * τ * x⁻¹) h1 x
  have h3 : x⁻¹ * (x * τ * x⁻¹) * x = τ := by group
  rw [h3] at h2
  exact h2

theorem bar_Lgen_eq_Xbar (hc : Ctx M Q Z B)
    (h : Lgen M (LB M Q B) ≤ XbarPre M Q Z B) :
    bar M Q (Lgen M (LB M Q B)) = Xbar M Q Z B := by
  refine le_antisymm ?_ (Xbar_le_bar_Lgen hc)
  calc bar M Q (Lgen M (LB M Q B))
      ≤ bar M Q (XbarPre M Q Z B) :=
        Subgroup.map_mono (Subgroup.subgroupOf_mono M h)
    _ = Xbar M Q Z B := bar_XbarPre hc

section ModuleChain

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

abbrev PiImageStable (M₀ : Tim79.QuadModel Q Z K γ) (X : Subgroup G) : Prop :=
  ∀ (c : K) (e : M₀.E), e ∈ M₀.img X → c • e ∈ M₀.img X

theorem pi_mem_cmComm (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {X₄ : Subgroup G} (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) {x : G} (hx : x ∈ X₄) :
    M₀.π x ∈ cmComm M Q Z B K γ M₀ φ := by
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hpre : Z ⊔ ⁅Q, XbarPre M Q Z B⁆ ≤
      CFSG.RankThree.GF2n.Smith81.preimageSub M₀ (cmComm M Q Z B K γ M₀ φ) := by
    refine sup_le ?_ ?_
    · intro z hz
      rw [CFSG.RankThree.GF2n.Smith81.mem_preimageSub]
      refine ⟨hZQ hz, ?_⟩
      rw [(M₀.π_ker z (hZQ hz)).mpr hz]
      exact (cmComm M Q Z B K γ M₀ φ).zero_mem
    · intro c hcC
      rw [CFSG.RankThree.GF2n.Smith81.mem_preimageSub]
      exact ⟨commutator_le_Q hc hcC,
        (mem_cmComm_iff hc hD φ hφπ (M₀.π c)).mpr ⟨c, hcC, rfl⟩⟩
  rw [hX₄] at hx
  exact (CFSG.RankThree.GF2n.Smith81.mem_preimageSub.mp (hpre hx)).2

theorem cmComm_le_span_pi_X₄ (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {X₄ : Subgroup G} (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) :
    cmComm M Q Z B K γ M₀ φ ≤ Submodule.span K (M₀.π '' (X₄ : Set G)) := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := (mem_cmComm_iff hc hD φ hφπ e).mp he
  refine Submodule.subset_span ⟨x, ?_, rfl⟩
  rw [hX₄]
  exact Subgroup.mem_sup_right hx

theorem span_pi_X₄_eq_cmComm (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {X₄ : Subgroup G} (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) :
    Submodule.span K (M₀.π '' (X₄ : Set G)) = cmComm M Q Z B K γ M₀ φ := by
  refine le_antisymm ?_ (cmComm_le_span_pi_X₄ hc hD φ hφπ hX₄)
  rw [Submodule.span_le]
  rintro e ⟨x, hx, rfl⟩
  exact pi_mem_cmComm hc hD φ hφπ hX₄ hx

theorem card_quotient_X₂_X₁ {m : ℕ} {X₁ X₂ : Subgroup G}
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁
      (Q)) :
    Nat.card (↥X₂ ⧸ X₁.subgroupOf X₂) = Nat.card K ^ m := by
  obtain ⟨-, -, -, -, hN, ψ, -⟩ := nat2
  haveI := hN
  rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_fin]

theorem card_X₂ {m : ℕ} {X₁ X₂ : Subgroup G} (hX₁ : X₁ = Z) (hZ₁ : Z ≤ X₁)
    (h₁₂ : X₁ ≤ X₂)
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁
      (Q)) :
    Nat.card ↥X₂ = Nat.card Z * Nat.card K ^ m := by
  have hindex := (X₁.subgroupOf X₂).index_mul_card
  rw [Subgroup.index_eq_card, card_quotient_X₂_X₁ nat2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁₂).toEquiv, hX₁] at hindex
  rw [← hindex, mul_comm]

end ModuleChain

end CFSG.RankThree.GF2n.Stroth80
