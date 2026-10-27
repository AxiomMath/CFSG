module

public import CFSG.Quasithin.Background.GoldschmidtG22M12IdentGraph
public import CFSG.Quasithin.Background.GoldschmidtG22M12IdentM12

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace F6

@[expose] def HasSylowOfG22OrM12 (D : Type) [Group D] [Finite D] : Prop :=
  ∃ (S : Sylow 2 D) (W : Type) (_ : Group W) (_ : Finite W) (P : Sylow 2 W),
    (IsG22 W ∨ IsM12 W) ∧ Nonempty (↥S ≃* ↥P)

@[expose] def G22M12SylowListFact : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSetting D → HasSylowOfG22OrM12 D →
    (twoResidual (⊤ : Subgroup D) = ⊤ ∧
        Nonempty (TwoResidualQuot D ≃* ↥CFSG.Blueprint.NativeSporadic.M12)) ∨
      ((twoResidual (⊤ : Subgroup D)).index = 2 ∧
        ((∃ p : ℕ, p % 8 = 5 ∧ StatedClassicalModel (TwoResidualQuot D) .PSL 3 p 1) ∨
          (∃ p : ℕ, p % 8 = 3 ∧ StatedClassicalModel (TwoResidualQuot D) .PSU 3 p 1)))

@[expose] def G22SylowIsoM12Fact : Prop :=
  ∀ (W : Type) [Group W] [Finite W], IsG22 W → ∀ P : Sylow 2 W,
    ∃ Q : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M12, Nonempty (↥P ≃* ↥Q)

@[expose] def M12SylowListFact : Prop :=
  ∀ (D : Type) [Group D] [Finite D], F618RecogSetting D →
    (∃ (S : Sylow 2 D) (Q : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M12),
        Nonempty (↥S ≃* ↥Q)) →
    (twoResidual (⊤ : Subgroup D) = ⊤ ∧
        Nonempty (TwoResidualQuot D ≃* ↥CFSG.Blueprint.NativeSporadic.M12)) ∨
      ((twoResidual (⊤ : Subgroup D)).index = 2 ∧
        ((∃ p : ℕ, p % 8 = 5 ∧ StatedClassicalModel (TwoResidualQuot D) .PSL 3 p 1) ∨
          (∃ p : ℕ, p % 8 = 3 ∧ StatedClassicalModel (TwoResidualQuot D) .PSU 3 p 1)))

theorem g22M12SylowListFact_of_iso (hIso : G22SylowIsoM12Fact) (hM : M12SylowListFact) :
    G22M12SylowListFact := by
  rintro D _ _ hS ⟨S, W, _, _, P, hW, ⟨e⟩⟩
  apply hM D hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, ⟨eQ⟩⟩ : ∃ Q : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M12,
      Nonempty (↥P ≃* ↥Q) := by
    rcases hW with hW | hW
    · exact hIso W hW P
    · obtain ⟨ψ⟩ := hW
      exact ⟨P.mapSurjective (f := ψ.toMonoidHom) ψ.surjective,
        ⟨((P : Subgroup W).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
          (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)⟩⟩
  exact ⟨S, Q, ⟨e.trans eQ⟩⟩

theorem hasSylowOfG22OrM12_of_goldCase {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (ho : IsGoldCaseG22 G₁ G₂ ∨ IsGoldCaseM12 G₁ G₂) :
    HasSylowOfG22OrM12 D := by
  rcases ho with ⟨⟨W, _, _, K₁, K₂, hW, ⟨-, -, -, S, hSK⟩, φ₁, φ₂, hag₁, hag₂⟩, -⟩ |
      ⟨⟨W, _, _, K₁, K₂, hW, ⟨-, -, -, S, hSK⟩, φ₁, φ₂, hag₁, hag₂⟩, -⟩
  · obtain ⟨S', ⟨e⟩⟩ := exists_sylow_of_inf h
      ((infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂).trans (MulEquiv.subgroupCongr hSK.symm))
    exact ⟨S', W, inferInstance, inferInstance, S, Or.inl hW, ⟨e⟩⟩
  · obtain ⟨S', ⟨e⟩⟩ := exists_sylow_of_inf h
      ((infMulEquivOfAmalgamIso φ₁ φ₂ hag₁ hag₂).trans (MulEquiv.subgroupCongr hSK.symm))
    exact ⟨S', W, inferInstance, inferInstance, S, Or.inr hW, ⟨e⟩⟩

section Identification


theorem f618RecogG22M12_of_sylowList (hL : G22M12SylowListFact) : F618RecogG22M12 := by
  intro D _ _ G₁ G₂ hS h ho
  rcases hL D hS (hasSylowOfG22OrM12_of_goldCase h ho) with ⟨hLtop, ⟨e⟩⟩ | ⟨hidx, hp⟩
  · exact Or.inr (isM12_of_setting hS hLtop e)
  · rcases hp with ⟨p, hp8, hK⟩ | ⟨p, hp8, hK⟩
    · exact Or.inl ⟨p, Or.inr hp8, isSLEps3GraphExt_of_setting_psl hS hidx (by omega) hK⟩
    · exact Or.inl ⟨p, Or.inl hp8, isSLEps3GraphExt_of_setting_psu hS hidx (by omega) hK⟩

theorem f618RecogG22M12_of_m12SylowList (hIso : G22SylowIsoM12Fact) (hM : M12SylowListFact) :
    F618RecogG22M12 :=
  f618RecogG22M12_of_sylowList (g22M12SylowListFact_of_iso hIso hM)

end Identification

end F6

end CFSG.Quasithin
