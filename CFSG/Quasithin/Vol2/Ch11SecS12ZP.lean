module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZG
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSetting
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_pi_lXOne {X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G))
    (hSL : IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
      ∃ π : ↥(lXOne L X₁) →* Matrix.SpecialLinearGroup (Fin 3) F,
        Function.Surjective π ∧ IsPGroup 2 π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hSL
  let : Fintype F := Fintype.ofFinite F
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
    (Subgroup.inclusion ((perfectCore_le _).trans inf_le_left : lXOne L X₁ ≤ L)) with hf
  refine ⟨F, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hF],
    (e.trans (SecD.statedSLEquiv' 3 F)).toMonoidHom.comp f,
    (e.trans (SecD.statedSLEquiv' 3 F)).surjective.comp (surjective_lXOne hL hcov), ?_⟩
  rintro ⟨x, hx⟩
  have hx' : f x = 1 := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff] at hx
    exact hx
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨k, hk⟩ := h2 ⟨_, hx'⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_inclusion] at h ⊢
  exact h

theorem isSL3_lXOne {X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G))
    (hSL : IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsSL3 4 (↥(lXOne L X₁) ⧸ CFSG.pCore 2 ↥(lXOne L X₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hSL
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
    (Subgroup.inclusion ((perfectCore_le _).trans inf_le_left : lXOne L X₁ ≤ L)) with hf
  have hfs : Function.Surjective f := surjective_lXOne hL hcov
  have h2L : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hker : f.ker = CFSG.pCore 2 ↥(lXOne L X₁) := by
    apply le_antisymm
    ·
      have hp : IsPGroup 2 ↥f.ker := by
        rintro ⟨x, hx⟩
        rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hx
        obtain ⟨k, hk⟩ := h2L ⟨_, hx⟩
        refine ⟨k, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        have h := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hk
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_inclusion] at h ⊢
        exact h
      exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance hp
    ·
      have hn : ((CFSG.pCore 2 ↥(lXOne L X₁)).map f).Normal := by
        have : (CFSG.pCore 2 ↥(lXOne L X₁)).Normal := by
          exact CFSG.LieType.BorelTits.pCore_normal 2
        exact Subgroup.Normal.map this f hfs
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥(lXOne L X₁)).map f) := by
        have : IsPGroup 2 ↥(CFSG.pCore 2 ↥(lXOne L X₁)) := by
          exact CFSG.LieType.BorelTits.pCore_isPGroup 2
        exact this.map f
      have hle : (CFSG.pCore 2 ↥(lXOne L X₁)).map f ≤ CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) := by
        exact CFSG.LieType.BorelTits.le_pCore 2 hn hp
      rw [CFSG.QuasithinUnique.Setup.Campbell.pCore_quotient_pCore_eq_bot', le_bot_iff,
        Subgroup.map_eq_bot_iff] at hle
      exact hle
  exact ⟨F, hFf, hFfin, hF, ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs)).trans e⟩⟩

theorem xOne_le_lXOne {X₁ : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G))
    (hX₁L : X₁ ≤ L) (hX₁3 : ∀ x ∈ X₁, x ^ 3 = 1) : X₁ ≤ lXOne L X₁ := fun x hx =>
  mem_lXOne hL hcov ⟨hX₁L hx, Subgroup.le_normalizer hx⟩ (hX₁3 x hx)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
