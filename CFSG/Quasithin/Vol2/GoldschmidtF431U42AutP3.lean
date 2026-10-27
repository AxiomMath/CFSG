module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3Mod

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

theorem AutIso.toG_inv (iso : AutIso M₁ M₂) (x : Bh) : iso.toG x⁻¹ = (iso.toG x)⁻¹ := by
  simp only [AutIso.toG, map_inv, Subgroup.coe_inv]

theorem AutIso.mem_pCoreOf_iff
    (iso : AutIso M₁ M₂) {g : G} :
    g ∈ pCoreOf 2 (M₁ ⊓ M₂) ↔ ∃ y : ↥Bh, (y : Ah) ∈ TAh ∧ iso.toG y = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 iso.phiB] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨y, ?_, rfl⟩
    rw [← pCoreOf_Bh_eq]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← pCoreOf_Bh_eq] at hy
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.1 hy
    have : y' = y := Subtype.ext hyy'
    subst this
    refine Subgroup.mem_map.2 ⟨iso.phiB y', ?_, rfl⟩
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 iso.phiB]
    exact Subgroup.mem_map.2 ⟨y', hy', rfl⟩

theorem u42AutFusion :
    U42AutFusion := by
  intro G _ _ M₁ M₂ z c T hT u hu hu2 hu1
  obtain ⟨b, hbB, hTb⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_imgG_That c.iso) hT
  let bh : ↥Bh := c.iso.phiB.symm ⟨b, hbB⟩
  have hbh : c.iso.toG bh = b := congrArg Subtype.val (c.iso.phiB.apply_symm_apply ⟨b, hbB⟩)
  obtain ⟨y, hyT, hyu⟩ := c.iso.mem_pCoreOf_iff.1 hu
  have hconjT : ∀ (g : ↥Bh) (a : ↥Bh), (a : Ah) ∈ TAh → ((g * a * g⁻¹ : ↥Bh) : Ah) ∈ TAh :=
    fun g a ha => conj_TAh g.2 ha
  set y₀ : ↥Bh := bh⁻¹ * y * bh with hy₀
  have hy₀T : (y₀ : Ah) ∈ TAh := by
    have := hconjT bh⁻¹ y hyT
    simpa [hy₀] using this
  have hu₀ : c.iso.toG y₀ = b⁻¹ * u * b := by
    rw [hy₀, AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv, hbh, hyu]
  have hy₀2 : (y₀ : Ah) * y₀ = 1 := by
    have : y₀ * y₀ = 1 := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, hu₀, c.iso.toG_one]
      calc b⁻¹ * u * b * (b⁻¹ * u * b) = b⁻¹ * (u * u) * b := by group
        _ = 1 := by rw [← pow_two, hu2]; group
    exact congrArg Subtype.val this
  have hy₀1 : (y₀ : Ah) ≠ 1 := fun h => hu1 (by
    have h2 := congrArg c.iso.toG (Subtype.ext h : y₀ = 1)
    rw [hu₀, c.iso.toG_one] at h2
    calc u = b * (b⁻¹ * u * b) * b⁻¹ := by group
      _ = 1 := by rw [h2]; group)
  obtain ⟨g, û₁, hg, hû₁T, hû₁2, hconj, hcard⟩ := fusion_model hy₀T hy₀2 hy₀1
  let y₁ : ↥Bh := ⟨û₁, TAh_le_Bh hû₁T⟩
  have hrel1 : ∀ x : Bh, (c.iso.phi1 (Subgroup.inclusion Bh_le_P1h x) : G) = c.iso.toG x :=
    fun x => congrArg Subtype.val (c.iso.comm1 x).symm
  have hrel2 : ∀ x : Bh, (c.iso.phi2 (Subgroup.inclusion Bh_le_P2h x) : G) = c.iso.toG x :=
    fun x => congrArg Subtype.val (c.iso.comm2 x).symm
  have key : ∃ g₀ : G, g₀ * c.iso.toG y₀ * g₀⁻¹ = c.iso.toG y₁ := by
    rcases hg with hg | hg
    · refine ⟨(c.iso.phi1 ⟨g, hg⟩ : G), ?_⟩
      have e : (⟨g, hg⟩ : ↥P1h) * Subgroup.inclusion Bh_le_P1h y₀ * (⟨g, hg⟩ : ↥P1h)⁻¹ =
          Subgroup.inclusion Bh_le_P1h y₁ := Subtype.ext hconj
      have := congrArg (fun a => (c.iso.phi1 a : G)) e
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hrel1] at this
      exact this
    · refine ⟨(c.iso.phi2 ⟨g, hg⟩ : G), ?_⟩
      have e : (⟨g, hg⟩ : ↥P2h) * Subgroup.inclusion Bh_le_P2h y₀ * (⟨g, hg⟩ : ↥P2h)⁻¹ =
          Subgroup.inclusion Bh_le_P2h y₁ := Subtype.ext hconj
      have := congrArg (fun a => (c.iso.phi2 a : G)) e
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hrel2] at this
      exact this
  obtain ⟨g₀, hg₀⟩ := key
  have hy₁2 : y₁ * y₁ = 1 := Subtype.ext hû₁2
  have hu'2 : c.iso.toG y₁ * c.iso.toG y₁ = 1 := by
    rw [← AutIso.toG_mul, hy₁2, c.iso.toG_one]
  refine ⟨b * g₀ * b⁻¹, b * c.iso.toG y₁ * b⁻¹, ?_, ?_, ?_, ?_⟩
  · refine c.iso.mem_pCoreOf_iff.2 ⟨bh * y₁ * bh⁻¹, hconjT bh y₁ hû₁T, ?_⟩
    rw [AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv, hbh]
  · calc (b * c.iso.toG y₁ * b⁻¹) ^ 2 = b * (c.iso.toG y₁ * c.iso.toG y₁) * b⁻¹ := by
          rw [pow_two]; group
      _ = 1 := by rw [hu'2]; group
  · calc b * g₀ * b⁻¹ * u * (b * g₀ * b⁻¹)⁻¹ = b * (g₀ * (b⁻¹ * u * b) * g₀⁻¹) * b⁻¹ := by group
      _ = b * c.iso.toG y₁ * b⁻¹ := by rw [← hu₀, hg₀]
  · have hS : Nat.card ↥(That ⊓ Subgroup.centralizer ({û₁} : Set Ah)) ≤
        Nat.card ↥(T ⊓ cenOf (b * c.iso.toG y₁ * b⁻¹)) := by
      refine Nat.card_le_card_of_injective
        (fun a => ⟨b * c.iso.toG ⟨(a : Ah), That_le_Bh a.2.1⟩ * b⁻¹, ?_⟩) ?_
      · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [hTb]
          refine B6.mem_conjSub.2 ?_
          have : b⁻¹ * (b * c.iso.toG ⟨(a : Ah), That_le_Bh a.2.1⟩ * b⁻¹) * b =
              c.iso.toG ⟨(a : Ah), That_le_Bh a.2.1⟩ := by group
          rw [this]
          exact c.iso.mem_imgG.2 ⟨⟨(a : Ah), That_le_Bh a.2.1⟩, a.2.1, rfl⟩
        · rw [cenOf, Subgroup.mem_centralizer_singleton_iff]
          have h1 : y₁ * (⟨(a : Ah), That_le_Bh a.2.1⟩ : ↥Bh) = ⟨(a : Ah), That_le_Bh a.2.1⟩ * y₁ :=
            Subtype.ext ((Subgroup.mem_centralizer_singleton_iff.1 a.2.2).symm)
          have h2 := congrArg c.iso.toG h1
          rw [AutIso.toG_mul, AutIso.toG_mul] at h2
          calc b * c.iso.toG ⟨(a : Ah), That_le_Bh a.2.1⟩ * b⁻¹ * (b * c.iso.toG y₁ * b⁻¹)
              = b * (c.iso.toG ⟨(a : Ah), That_le_Bh a.2.1⟩ * c.iso.toG y₁) * b⁻¹ := by group
            _ = b * (c.iso.toG y₁ * c.iso.toG ⟨(a : Ah), That_le_Bh a.2.1⟩) * b⁻¹ := by rw [← h2]
            _ = b * c.iso.toG y₁ * b⁻¹ * (b * c.iso.toG ⟨(a : Ah), That_le_Bh a.2.1⟩ * b⁻¹) := by
              group
      · intro a₁ a₂ h
        have h1 := congrArg Subtype.val h
        have h2 : c.iso.toG ⟨(a₁ : Ah), That_le_Bh a₁.2.1⟩ =
            c.iso.toG ⟨(a₂ : Ah), That_le_Bh a₂.2.1⟩ := by
          simpa using h1
        have h3 := c.iso.toG_injective h2
        exact Subtype.ext (congrArg (fun z : ↥Bh => (z : Ah)) h3)
    calc 2 ^ 6 = 64 := by norm_num
      _ ≤ _ := hcard.trans hS

end CFSG.Quasithin.H13.F431.U42Aut
