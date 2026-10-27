module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridgeStab

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Conj

variable {G : Type} [Group G]

theorem mem_ggAutomizer_of_fix_conj {p : ℕ} {Bs H : Subgroup G} {z : G}
    (hstab : ∀ ψ ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs,
      GGIsPseudoReflection p ψ → ψ ∈ ggAutomizer H Bs)
    {φ : MulAut ↥Bs} (hφA : φ ∈ ggAutomizer ⊤ Bs) (hφ : GGIsPseudoReflection p φ) {h : G}
    (hhH : h ∈ H) (hhN : h ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs)
    (hb : (b : G) = h * z * h⁻¹) (hφb : φ b = b) : φ ∈ ggAutomizer H Bs := by
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφA
  have hwW : ggConjAut Bs hhN ∈ ggAutomizer H Bs := ggConjAut_mem_ggAutomizer hhH hhN
  have hfix : g * (h * z * h⁻¹) * g⁻¹ = h * z * h⁻¹ := by
    have h1 := congrArg Subtype.val hφb
    rwa [hφg, hb] at h1
  have hgc : h⁻¹ * g * h ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine (?_ : z * (h⁻¹ * g * h) = h⁻¹ * g * h * z).symm
    calc z * (h⁻¹ * g * h) = h⁻¹ * ((h * z * h⁻¹) * g) * h := by group
      _ = h⁻¹ * (g * (h * z * h⁻¹) * g⁻¹ * g) * h := by rw [hfix]
      _ = h⁻¹ * g * h * z := by group
  have hgN' : h⁻¹ * g * h ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhN) hgN) hhN
  have hψ : (ggConjAut Bs hhN)⁻¹ * φ * ggConjAut Bs hhN ∈
      ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := by
    rw [mem_ggAutomizer_iff]
    refine ⟨h⁻¹ * g * h, hgc, hgN', fun c => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, inv_apply_of_forall (ggConjAut_apply Bs hhN), hφg,
      ggConjAut_apply]
    group
  have hψp : GGIsPseudoReflection p ((ggConjAut Bs hhN)⁻¹ * φ * ggConjAut Bs hhN) := by
    have h1 := hφ.conj (ggConjAut Bs hhN)⁻¹
    rwa [inv_inv] at h1
  have hψW := hstab _ hψ hψp
  have heq : φ = ggConjAut Bs hhN * ((ggConjAut Bs hhN)⁻¹ * φ * ggConjAut Bs hhN) *
      (ggConjAut Bs hhN)⁻¹ := by group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwW hψW) (Subgroup.inv_mem _ hwW)

end Conj

@[expose] def GGPseudoReflNbrStabInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({y} : Set G)) Bs, GGIsPseudoReflection p φ →
          φ ∈ ggAutomizer (ggG0 p B x L D J) Bs

@[expose] def GGPseudoReflNbrStabModInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({y} : Set G)) Bs, GGIsPseudoReflection p φ →
          ∃ ψ ∈ ggAutomizer (ggG0 p B x L D J) Bs, (∀ b : ↥Bs, (b : G) = y → ψ b = b) ∧
            ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers y

@[expose] def GGPseudoReflAwayInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ φ ∈ ggAutomizer ⊤ Bs, GGIsPseudoReflection p φ →
        (∀ h ∈ ggG0 p B x L D J, h ∈ Subgroup.normalizer (Bs : Set G) →
          ∀ b : ↥Bs, (b : G) = h * x * h⁻¹ → φ b ≠ b) →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ∀ h ∈ ggG0 p B x L D J, h ∈ Subgroup.normalizer (Bs : Set G) →
            ∀ b : ↥Bs, (b : G) = h * y * h⁻¹ → φ b ≠ b) →
        φ ∈ ggAutomizer (ggG0 p B x L D J) Bs

theorem ggPseudoReflOrbitInput_of_nbr (hN : GGPseudoReflNbrStabInput)
    (hA : GGPseudoReflAwayInput) : GGPseudoReflOrbitInput := by
  intro G _ _ p B Bs x L D J hH φ hφA hφ hx
  by_cases hy : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ∃ h ∈ ggG0 p B x L D J, h ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∃ b : ↥Bs, (b : G) = h * y * h⁻¹ ∧ φ b = b
  · obtain ⟨y, K, hyK, h, hhG0, hhN, b, hb, hφb⟩ := hy
    exact mem_ggAutomizer_of_fix_conj (hN G p B Bs x L D J hH y K hyK) hφA hφ hhG0 hhN b hb hφb
  · exact hA G p B Bs x L D J hH φ hφA hφ hx fun y K hyK h hhG0 hhN b hb hφb =>
      hy ⟨y, K, hyK, h, hhG0, hhN, b, hb, hφb⟩

theorem ggPseudoReflNbrStabInput_of_mod (h : GGPseudoReflNbrStabModInput) :
    GGPseudoReflNbrStabInput := by
  intro G _ _ p B Bs x L D J hH y K hyK φ hφ hφp
  obtain ⟨ψ, hψ, hψy, hmod⟩ := h G p B Bs x L D J hH y K hyK φ hφ hφp
  have hcfg := hH.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyK.1.2.1
  have hy1 : (⟨y, hyBs⟩ : ↥Bs) ≠ 1 := fun h => hyK.1.2.2.1 (congrArg Subtype.val h)
  have hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
    ggAutomizer_apply_eq_of_le_centralizer (x := ⟨y, hyBs⟩) le_rfl hφ
  have hmod' : ∀ b : ↥Bs, (ψ b)⁻¹ * φ b ∈ Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs) := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmod b)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  rw [eq_of_mem_zpowers_of_noTransvection hcfg.2.1.2.1 hH.2.2.2.1 hy1
    (mem_ggInduced_top_of_mem_ggAutomizer hφ) (mem_ggInduced_top_of_mem_ggAutomizer hψ) hφy
    (hψy _ rfl) hmod']
  exact hψ

theorem ggPseudoReflNbrStabModInput_of_stab (h : GGPseudoReflNbrStabInput) :
    GGPseudoReflNbrStabModInput := by
  intro G _ _ p B Bs x L D J hH y K hyK φ hφ hφp
  refine ⟨φ, h G p B Bs x L D J hH y K hyK φ hφ hφp, fun b hb => ?_, fun b => ?_⟩
  · have hc : (⟨y, hb ▸ b.2⟩ : ↥Bs) = b := Subtype.ext hb.symm
    rw [← hc]
    exact ggAutomizer_apply_eq_of_le_centralizer le_rfl hφ
  · rw [inv_mul_cancel, Subgroup.coe_one]
    exact Subgroup.one_mem _

theorem ggPseudoReflOvergroupInput_of_nbr (hRL : GGPseudoReflStabInput)
    (hN : GGPseudoReflNbrStabInput) (hA : GGPseudoReflAwayInput) :
    GGPseudoReflOvergroupInput :=
  ggPseudoReflOvergroupInput_of_stab hRL (ggPseudoReflOrbitInput_of_nbr hN hA)

end CFSG.StandardType

end
