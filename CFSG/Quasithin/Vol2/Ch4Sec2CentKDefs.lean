module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G]

abbrev matOf {F : Type} [Field F] (g : ↥(StatedSL 3 F)) : Matrix (Fin 3) (Fin 3) F :=
  ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

abbrev coord {Q : Subgroup G} {F : Type} [Field F]
    (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)) (q : ↥Q) (i : Fin 2) : Fin 3 → F :=
  Multiplicative.toAdd (β q) i

structure CoordData (K Q : Subgroup G) (F : Type) [Field F]
    (α : ↥K →* ↥(StatedSL 3 F)) (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)) : Prop where
  KQ : K ≤ Subgroup.normalizer (Q : Set G)
  inj : Function.Injective β
  surj : Function.Surjective β
  eq : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
    coord β v i = (matOf (α a)).mulVec (coord β u i)

structure VStruct (K Q V : Subgroup G) (F : Type) [Field F] [Fintype F]
    (α : ↥K →* ↥(StatedSL 3 F)) : Prop where
  VQ : V ≤ Q
  exists_g₀ : ∃ (g₀ : G) (hg : g₀ ∈ K), α ⟨g₀, hg⟩ ≠ 1 ∧
    ∀ q ∈ Q, q ∈ V ↔ g₀ * q = q * g₀
  card : Nat.card ↥V = Fintype.card F ^ 4

theorem CoordData.of_isSumOfNaturalModulesVia {K Q : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} (h : IsSumOfNaturalModulesVia K Q ⊥ α false 2) :
    ∃ β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F), CoordData K Q F α β := by
  obtain ⟨hKQ, -, β, hβ, hβker, hβeq⟩ := h
  refine ⟨β, hKQ, ?_, hβ, fun a u v huv i => ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  · have h1 := hβeq a u v huv i
    simpa [moduleAct, coord, matOf] using h1

end CFSG.Quasithin.H13.Ch4.CentK
