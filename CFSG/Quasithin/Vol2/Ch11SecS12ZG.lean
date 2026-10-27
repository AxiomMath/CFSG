module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZF
public import CFSG.Quasithin.Vol2.Ch11SecS12ZA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem surjective_lXOne {X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G)) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      (Subgroup.inclusion ((perfectCore_le _).trans inf_le_left : lXOne L X₁ ≤ L))) := by
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨l', hl', hll⟩ := exists_lXOne_mul hL hcov l.2
  refine ⟨⟨l', hl'⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  obtain ⟨o, ho, hoe⟩ := hll
  have : (Subgroup.inclusion ((perfectCore_le _).trans inf_le_left : lXOne L X₁ ≤ L)
      ⟨l', hl'⟩)⁻¹ * l = o := Subtype.ext (by simpa using hoe.symm)
  rw [this]
  exact ho

theorem commutator_lXOne_eq_top (L X₁ : Subgroup G) : commutator ↥(lXOne L X₁) = ⊤ := by
  apply Subgroup.map_injective (lXOne L X₁).subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    perfectCore_perfect]

theorem hom_lXOne_eq_one {X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G))
    (hSL : IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L)) {p : ℕ} [Fact p.Prime]
    (ρ : ↥(lXOne L X₁) →* GL (Fin 2) (ZMod p)) : ρ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hSL
  let : Fintype F := Fintype.ofFinite F
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
    (Subgroup.inclusion ((perfectCore_le _).trans inf_le_left : lXOne L X₁ ≤ L)) with hf
  set π := (e.trans (SecD.statedSLEquiv' 3 F)).toMonoidHom.comp f with hπ
  have hπs : Function.Surjective π :=
    (e.trans (SecD.statedSLEquiv' 3 F)).surjective.comp (surjective_lXOne hL hcov)
  have hker : IsPGroup 2 π.ker := by
    rintro ⟨x, hx⟩
    have hx' : f x = 1 := by
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff] at hx
      exact hx
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    obtain ⟨k, hk⟩ := h2 ⟨_, hx'⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hk
  exact hom_eq_one_of_SL34 (commutator_lXOne_eq_top L X₁)
    (by rw [← Nat.card_eq_fintype_card, hF]) π hπs hker ρ

theorem lXOne_le_centralizer_pCoreOf {X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G))
    (hSL : IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H : Subgroup G} (hLH : lXOne L X₁ ≤ H) (hrank : CFSG.Open.pRank p (pCoreOf p H) ≤ 2) :
    lXOne L X₁ ≤ Subgroup.centralizer (pCoreOf p H : Set G) :=
  le_centralizer_of_pRank_le_two hp2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup p H) hrank
    (hLH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p H))
    (commutator_lXOne_eq_top L X₁) (fun ρ => hom_lXOne_eq_one hL hcov hSL ρ)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
