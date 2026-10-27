module

public import CFSG.Quasithin.H13.A7Nat1238Ke

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup

structure Setting1233Four {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V) : Prop where
  alt : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
    alternatingGroup (Fin 7))
  card : Nat.card V = 2 ^ 4
  act : ∃ φ : ↥L →* ↥(alternatingGroup (Fin 7)), Function.Surjective φ ∧
    φ.ker = (centralizer (V : Set G)).subgroupOf L

@[expose] def Insp1233Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V),
    Setting1233Four hyp → ∀ z : G, z ∈ V → z ≠ 1 → z ∈ quasithinOmegaOneCenter T →
      (∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, v = l * z * l⁻¹) ∧
      pCoreOf 2 (autOn (hyp.Lv z ⊔ hyp.Tv z) V) = ⊥ ∧
      autOn (hyp.Lv z) V = perfectCore (autOn (hyp.Lv z) V) ∧
      V = ⁅V, hyp.Lv z⁆ ∧
      quasithinIsFaithfulLocal T (Kv hyp z)

@[expose] def Insp1233K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (hyp : Hyp1223 G T L V),
    Setting1233Four hyp → ∀ z : G, z ∈ V → z ≠ 1 → z ∈ quasithinOmegaOneCenter T →
      HypC28 (hyp.Gv z) hyp.Q (hyp.Mv z) (Kv hyp z) V →
      ∀ K : Subgroup G, K ∈ cComp (hyp.Gv z) → Kv hyp z ≤ K → Kv hyp z = K

end CFSG.Quasithin.H13.A7
