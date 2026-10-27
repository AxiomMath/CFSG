module

public import CFSG.Quasithin.Vol2.Ch12Sec7IdentMain
public import CFSG.Quasithin.Vol2.Ch12Sec7I77a

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin S127 S127.I77

@[expose] def KtLine1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Set77 G T L V t →
    ∃ U : Subgroup G, U ≤ Kt L t ∧ IsElemAbelian 2 U ∧ Nat.card U = 64 ∧ U ≠ V ∧
      Nat.card ↥(U ⊓ V) = 16 ∧ U ≤ Subgroup.normalizer (V : Set G) ∧
      ∃ k : Fin 5 → G, k 0 = 1 ∧ (∀ i, k i ∈ Kt L t ⊓ Subgroup.normalizer (U : Set G)) ∧
        ∀ i j, i ≠ j → V.map (MulAut.conj (k i)).toMonoidHom ⊓
          V.map (MulAut.conj (k j)).toMonoidHom ⊓ U = Vt L t

@[expose] def MLine1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Set77 G T L V t →
    ∀ W : Subgroup G, IsElemAbelian 2 W → Nat.card W = 64 → W ≤ Subgroup.normalizer (L : Set G) →
      W ≠ V → Nat.card ↥(W ⊓ V) = 16 → Vt L t ≤ W ⊓ V →
      (∀ W' : Subgroup G, W' ≤ Subgroup.normalizer (L : Set G) ⊓
          Subgroup.centralizer ((W ⊓ V : Subgroup G) : Set G) →
          IsElemAbelian 2 W' → Nat.card W' = 64 → W' = V ∨ W' = W) ∧
      (∃ g ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G),
          g * t * g⁻¹ ∈ W ⊓ V ∧ g * t * g⁻¹ ∉ Vt L t) ∧
      ∃ z₀ ∈ W ⊓ V, (Subgroup.centralizer ({z₀} : Set G)).relIndex L = 45 ∧
        9 ≤ (Subgroup.centralizer ({z₀} : Set G)).relIndex
          (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer ((W ⊓ V : Subgroup G) : Set G))

@[expose] def GzNotLeM1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∀ z ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 →
          ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def StructOfNotLe1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∀ z ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 →
          ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) →
            StructAt G z

theorem struct1277_of (hG : GzNotLeM1277) (hS : StructOfNotLe1277) : Struct1277 := by
  intro G _ _ T L V h t ht h18 hGt z hz hz45
  exact hS G T L V h t ht h18 hGt z hz hz45 (hG G T L V h t ht h18 hGt z hz hz45)

end CFSG.Quasithin.H13.I1277
