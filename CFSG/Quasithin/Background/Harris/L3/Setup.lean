module

public import CFSG.Quasithin.Background.Harris.Interfaces
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Open
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def repOfHom {G : Type*} [Monoid G] (L : Subgroup (GLV V)) (π : G →* ↥L) :
    Representation (ZMod 2) G V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (L.subtype.comp π)

theorem repOfHom_apply {G : Type*} [Monoid G] (L : Subgroup (GLV V)) (π : G →* ↥L) (g : G)
    (v : V) : repOfHom L π g v = ((π g : ↥L) : GLV V) v := rfl

theorem repOfHom_isIrreducible {G : Type*} [Monoid G] {L : Subgroup (GLV V)} (π : G →* ↥L)
    (hπ : Function.Surjective π) (hL : IsIrr L ⊤) : (repOfHom L π).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
  obtain ⟨-, hlt, hirr⟩ := hL
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨⟨v, 0, fun h => hv (h ▸ Submodule.zero_mem _)⟩⟩
  · have hinv : Invariant L U := fun l hl u hu => by
      obtain ⟨g, hg⟩ := hπ ⟨l, hl⟩
      have := hU g u hu
      rw [repOfHom_apply, hg] at this
      exact this
    exact hirr U hinv bot_le le_top

theorem repOfHom_nontrivial {G : Type*} [Monoid G] {L : Subgroup (GLV V)} (π : G →* ↥L)
    (hπ : Function.Surjective π) (hL : ∃ l ∈ L, l ≠ 1) : ∃ g, repOfHom L π g ≠ 1 := by
  obtain ⟨l, hl, hl1⟩ := hL
  obtain ⟨g, hg⟩ := hπ ⟨l, hl⟩
  refine ⟨g, fun h => hl1 ?_⟩
  apply LinearEquiv.ext
  intro v
  have := congrArg (fun f : Module.End (ZMod 2) V => f v) h
  simp only [repOfHom_apply, hg, Module.End.one_apply] at this
  exact this

theorem exists_cover_famL3 {X : Type} [Group X] (h : FamL3 X) :
    ∃ f : ℕ, 1 ≤ f ∧ ∃ π : SL(3, GaloisField 2 f) →* X, Function.Surjective π ∧
      ∀ g, π g = 1 → g ∈ Subgroup.center SL(3, GaloisField 2 f) := by
  obtain ⟨-, f, hf, hm⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField X 3 2 f hm
  refine ⟨f, hf, e.symm.toMonoidHom.comp (QuotientGroup.mk' _), ?_, fun g hg => ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · have h1 : (QuotientGroup.mk' (Subgroup.center SL(3, GaloisField 2 f)) g) = 1 := by
      have := congrArg e hg
      simpa using this
    exact (QuotientGroup.eq_one_iff g).mp h1

theorem exists_cover_famCoverSL3Two {X : Type} [Group X] (h : FamCoverSL3Two X) :
    ∃ e : ℕ, 1 ≤ e ∧ Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) 1 ∧
      Nonempty (SL(3, GaloisField 2 e) ≃* X) := by
  obtain ⟨-, e, he, hmod, K, _, _, hK, ⟨φ⟩⟩ := h
  refine ⟨e, he, hmod, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ e := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hKf
  let _ : Fintype (GaloisField 2 e) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 e) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 e (by omega)]
  let r : K ≃+* GaloisField 2 e := FiniteField.ringEquivOfCardEq hcard
  exact ⟨(CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 3) r).symm.trans
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).trans φ.symm)⟩

end CFSG.Quasithin.G11.Harris.L3
