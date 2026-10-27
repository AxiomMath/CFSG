module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.Background.SmithB42Sp4Excl

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem nonempty_mulEquiv_antiSp {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) :
    Nonempty (X ≃* antiSp (GaloisField 2 f)) := by
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hcard]
  have hK' : Nat.card K = 2 ^ f := hcard
  have : CharP K 2 := charP_two_of_card_pow hK'
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard' : Fintype.card K = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card (α := GaloisField 2 f), GaloisField.card 2 f (by omega), hKf]
  let r : K ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hcard'
  exact ⟨(e.trans (antiProjEquiv K).symm).trans (antiSpCongr r)⟩

@[expose] noncomputable def piOf {F : Type} [Field F] (L : Subgroup (GLV V))
    (φ : ↥L ≃* antiSp F) : antiSp F →* (V ≃ₗ[ZMod 2] V) :=
  L.subtype.comp φ.symm.toMonoidHom

theorem piOf_apply {F : Type} [Field F] (L : Subgroup (GLV V)) (φ : ↥L ≃* antiSp F)
    (g : antiSp F) : piOf L φ g = ((φ.symm g : ↥L) : GLV V) := rfl

theorem piOf_injective {F : Type} [Field F] (L : Subgroup (GLV V)) (φ : ↥L ≃* antiSp F) :
    Function.Injective (piOf L φ) := fun _ _ h =>
  φ.symm.injective (Subtype.ext h)

theorem repOf_piOf_isIrreducible {F : Type} [Field F] {L : Subgroup (GLV V)}
    (φ : ↥L ≃* antiSp F) (hL : CFSG.Quasithin.G11.IsIrr L ⊤) :
    (CFSG.Quasithin.B42Sp4.repOf (piOf L φ)).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  obtain ⟨-, hlt, hirr⟩ := hL
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨⟨v, 0, fun h => hv (h ▸ Submodule.zero_mem _)⟩⟩
  · have hinv : CFSG.Quasithin.G11.Invariant L U := fun l hl u hu => by
      have := hU (φ ⟨l, hl⟩) u hu
      simpa [CFSG.Quasithin.B42Sp4.repOf_apply, piOf_apply] using this
    exact hirr U hinv bot_le le_top

end CFSG.Quasithin.G11.Harris.Sp4
