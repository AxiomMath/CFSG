module

public import CFSG.Quasithin.H13.A5S136d
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3
open CFSG.Blueprint

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

structure Concl136 : Prop where
  hab : IsElemAbelian 2 (conjClosure V S.G1)
  h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
    (∃ u : ↥V, u ≠ 1 ∧ IsSing (S.frame.ψ u) ∧
      V ⊓ conjSub g⁻¹ V = Subgroup.zpowers (u : G)) ∧ ⁅V, conjSub g⁻¹ V⁆ = ⊥
  hr : rParam V = 3
  hw : 1 < wParam T V
  hn : ∀ H : Subgroup G, InH T H → ¬ H ≤ Subgroup.normalizer (L : Set G) → 1 < E1.nParam H
  hsolv : ∀ H : Subgroup G, InH T H → Group.IsSolvable ↥H →
    H ≤ Subgroup.normalizer (L : Set G)
  h2661 : ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ¬ K ≤ Subgroup.normalizer (L : Set G)

@[expose] def Case13627J2 (K : Subgroup G) : Prop :=
  S.G1 = K ⊔ T ∧ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* NativeSporadic.J2)

@[expose] def Case13627M23 (K : Subgroup G) : Prop :=
  S.G1 = K ⊔ T ∧ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* NativeSporadic.M23)

@[expose] def Case13627L34 (K : Subgroup G) : Prop :=
  LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 2 ∧ E2.IsDiagramNontrivial T K (T ⊓ K) ∧
    S.G1 = oPrimeResidualOf 3 S.G1 ⊔ T ∧
    (K = oPrimeResidualOf 3 S.G1 ∨
      IsPGLEps3 true 4
        (↥(oPrimeResidualOf 3 S.G1) ⧸ CFSG.pCore 2 ↥(oPrimeResidualOf 3 S.G1)))

end Setting

@[expose] def Lemma13627 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Concl136 →
    ∃ K ∈ cComp S.G1, S.Case13627J2 K ∨ S.Case13627M23 K ∨ S.Case13627L34 K

@[expose] def End13627J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Concl136 →
    HypF98 T V L S.V1 S.V3 S.G1 → ∀ K ∈ cComp S.G1, S.Case13627J2 K →
    (∀ hE : IsElemAbelian 2 (tildeOf S.V1 (conjClosure S.V3 S.G1)),
      qInt (tildeOf S.V1 S.G1) (tildeOf S.V1 (conjClosure S.V3 S.G1)) hE ≤ 2) →
      False

@[expose] def End13627M23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Concl136 →
    HypF98 T V L S.V1 S.V3 S.G1 → ∀ K ∈ cComp S.G1, S.Case13627M23 K →
    (∀ hE : IsElemAbelian 2 (tildeOf S.V1 (conjClosure S.V3 S.G1)),
      qInt (tildeOf S.V1 S.G1) (tildeOf S.V1 (conjClosure S.V3 S.G1)) hE ≤ 2) →
      False

@[expose] def End13627L34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Concl136 →
    HypF98 T V L S.V1 S.V3 S.G1 → ∀ K ∈ cComp S.G1, S.Case13627L34 K →
    (∀ hE : IsElemAbelian 2 (tildeOf S.V1 (conjClosure S.V3 S.G1)),
      qInt (tildeOf S.V1 S.G1) (tildeOf S.V1 (conjClosure S.V3 S.G1)) hE ≤ 2) →
      False

theorem fin136_of (h1323 : Input1323Two) (h1336 : Input1336) (h27 : Lemma13627)
    (hJ2 : End13627J2) (hM23 : End13627M23) (hL34 : End13627L34) : Fin136 := by
  intro G _ _ T L V S hab h24 hr hw hn hsolv h2661 hq
  have hC : S.Concl136 := ⟨hab, h24, hr, hw, hn, hsolv, h2661⟩
  have hF98 := S.hypF98_G1 h1323 h1336 fun g hg hne => (h24 g hg hne).2
  obtain ⟨K, hK, hJ | hM | hL⟩ := h27 G T L V S hC
  · exact hJ2 G T L V S hC hF98 K hK hJ hq
  · exact hM23 G T L V S hC hF98 K hK hM hq
  · exact hL34 G T L V S hC hF98 K hK hL hq

end CFSG.Quasithin.H13.A5
