module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneMoving

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45RankXAbsIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁, (∀ b ∈ U₁, a₁ * b = b * a₁) ∧ (∀ b ∈ U₁, a₂ * b = b * a₂) ∧
        (a₁ * x * a₁⁻¹ * x⁻¹) ^ p = 1 ∧ (a₂ * x * a₂⁻¹ * x⁻¹) ^ p = 1 ∧
        a₁ * x * a₁⁻¹ * x⁻¹ ∉ U ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ i j : ℕ, (a₁ * x * a₁⁻¹ * x⁻¹) ^ i * (a₂ * x * a₂⁻¹ * x⁻¹) ^ j = 1 → p ∣ i ∧ p ∣ j

@[expose] def GGL45FiveIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
    Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (U₁ : Set G) →
    (∀ r ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G),
          r * v * r⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) → v = 1) →
    (∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), v ^ p = 1 → v ∈ Subgroup.zpowers d) →
    (∀ n ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), n * v * n⁻¹ ∈ U₁) →
    ∀ r ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        r ∈ Subgroup.normalizer (U₁ : Set G)

section Moving

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem ggL45_conj_V_mem_of_rankXAbs_of_cent (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G))
    {g₀ : G} (hg₀ : g₀ ∈ U) (hcyc : U ≤ Subgroup.zpowers g₀ ⊔ U₁)
    (hrx : ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁, (∀ b ∈ U₁, a₁ * b = b * a₁) ∧ (∀ b ∈ U₁, a₂ * b = b * a₂) ∧
        (a₁ * x * a₁⁻¹ * x⁻¹) ^ p = 1 ∧ (a₂ * x * a₂⁻¹ * x⁻¹) ^ p = 1 ∧
        a₁ * x * a₁⁻¹ * x⁻¹ ∉ U ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ i j : ℕ, (a₁ * x * a₁⁻¹ * x⁻¹) ^ i * (a₂ * x * a₂⁻¹ * x⁻¹) ^ j = 1 → p ∣ i ∧ p ∣ j)
    {n : G} (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) : n * v * n⁻¹ ∈ U₁ := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  refine ggL45_conj_V_mem_of_moving hraw hiso hcfg (fun n hn hnd v hv => ?_) hn hv
  by_contra hw
  obtain ⟨v'', hv'', b, hb, hvb⟩ := hcfg.exists_conj_eq_mul hraw hiso hg₀ hcyc hn.1 hv hw
  obtain ⟨a₁, ha₁, a₂, ha₂, hz₁, hz₂, hp₁, hp₂, -, hind⟩ := hrx
  have key : ∀ a : G, (∀ b' ∈ U₁, a * b' = b' * a) →
      a * (n * v'' * n⁻¹) * a⁻¹ * (n * v'' * n⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ := by
    intro a hz
    have hba : b * a⁻¹ * b⁻¹ = a⁻¹ := by
      rw [← Commute.inv_left (hz b hb), mul_inv_cancel_right]
    calc a * (n * v'' * n⁻¹) * a⁻¹ * (n * v'' * n⁻¹)⁻¹
        = a * (x * b) * a⁻¹ * (x * b)⁻¹ := by rw [hvb]
      _ = a * x * (b * a⁻¹ * b⁻¹) * x⁻¹ := by group
      _ = a * x * a⁻¹ * x⁻¹ := by rw [hba]
  have hq₁ := ggL45_comm_mem_zpowers_of_comm_of_cent hraw hiso hcfg hC hcomm hn hnd hv'' ha₁
    (by rw [key a₁ hz₁, hp₁]; exact one_mem _)
  have hq₂ := ggL45_comm_mem_zpowers_of_comm_of_cent hraw hiso hcfg hC hcomm hn hnd hv'' ha₂
    (by rw [key a₂ hz₂, hp₂]; exact one_mem _)
  rw [key a₁ hz₁] at hq₁
  rw [key a₂ hz₂] at hq₂
  have hd'p : (n * d * n⁻¹) ^ p = 1 := by rw [conj_pow, hcfg.d_pow]; group
  exact not_independent_of_mem_zpowers hd'p hq₁ hq₂ ⊥
    fun i j hij => hind i j (Subgroup.mem_bot.mp hij)

end Moving

theorem ggL45MovingIOneInput_of_rankXAbs (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (h3 : GGNbrSubcomponentInput) (htorus : GGL45TorusIOneInput)
    (hrankx : GGL45RankXAbsIOneInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hD4 : GGL45CyclicD4IOneInput) (hfive : GGL45FiveIOneInput) : GGL45MovingIOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hFC hI1 hTBM hL43 hL44 hL44ii hK hsetup hpart hon r
    hr hrd
  have hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁ :=
    ⟨hFC, hTBM, hL43, hL44, hL44ii, hK, hsetup, hpart,
      fun u hu => hon ⟨Subgroup.le_normalizer hu, hpart.1 hu⟩⟩
  have hC := hcfg.cent_le_of_iOne h3 hI1
  obtain ⟨s, hs, -, -, -, x', hx'x, hx'V⟩ :=
    htorus G p B Bs x L D J X B₂ d y K U U₁ hcfg hI1
  have hcomm := fun z (hz : z ∈ U₁) hzp => hcfg.comm_mem_V_of_torus hs hx'x hx'V hz hzp
  obtain ⟨g₀, hg₀, hcyc⟩ := hcfg.exists_cyclic_of_iOne hpc hD4 hI1
  have hrx := hrankx G p B Bs x L D J X B₂ d y K U U₁ hcfg hI1
  have hconj := fun n hn v (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) =>
    ggL45_conj_V_mem_of_rankXAbs_of_cent hraw hiso hcfg hC hcomm hg₀ hcyc hrx (n := n) hn hv
  exact hfive G p B Bs x L D J X B₂ d y K U U₁ hcfg hI1 hon
    (fun r hr hrd => ggL45_inf_conj_eq_one_of_cent hraw hiso hcfg hC hr hrd)
    (fun v hv hvp => ggL45_omega_V_of_conj_of_cent hraw hiso hcfg hC hcomm hconj hv hvp)
    hconj r hr hrd

theorem ggL45IOneInput_of_rankXAbs (hN : GGInndiagNormalInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (h3 : GGNbrSubcomponentInput) (htorus : GGL45TorusIOneInput)
    (hrankx : GGL45RankXAbsIOneInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hD4 : GGL45CyclicD4IOneInput) (hfive : GGL45FiveIOneInput) : GGL45IOneInput :=
  ggL45IOneInput_of_moving hN (ggRawInnSubgroupInput_of_rawInnField hraw)
    (ggL45MovingIOneInput_of_rankXAbs hraw hiso h3 htorus hrankx hpc hD4 hfive)

end CFSG.StandardType

end
