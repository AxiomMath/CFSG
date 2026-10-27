module

public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit
public import CFSG.LocalAnalysis.StandardType.FS81.FrameEm
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Assembly CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Blueprint.Chevalley

@[expose] def E7FrameAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.E7 → ∀ B : Basis3 G (Row.E7.n + 1), Adapted B b₀ K E →
      RecOut Row.E7 B b₀ →
      ∃ (U : Fin 8 → Subgroup G) (g : G),
        (∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
          ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a) ∧
        (∀ i j : Fin 8, edgeE 8 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) ∧
        K ≤ ⨆ k, U k ∧ b₀ ∈ ⨆ k, U k ∧ g * b₀ * g⁻¹ ∈ K ∧
        (∃ (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) (r : ↥(adjointGroup .E7 (ZMod 2))),
          (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
            ((ψ r : ↥K) : G) = g⁻¹ * b₀ * g) ∧
        g ∈ K ⊔ Subgroup.normalizer (E : Set G) ∧
        ∀ k, U k ≤ K ∨ U k ≤ K.map (MulAut.conj g).toMonoidHom

@[expose] def E7RootCoreAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.E7 → ∀ B : Basis3 G (Row.E7.n + 1), Adapted B b₀ K E →
      RecOut Row.E7 B b₀ → ∀ g : G, g * b₀ * g⁻¹ ∈ K →
        (∃ (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) (r : ↥(adjointGroup .E7 (ZMod 2))),
          (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
            ((ψ r : ↥K) : G) = g⁻¹ * b₀ * g) →
        ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (K : Set G) ∧
            R ≤ Subgroup.centralizer (K.map (MulAut.conj g).toMonoidHom : Set G)

@[expose] def E7CapAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.E7 → ∀ B : Basis3 G (Row.E7.n + 1), Adapted B b₀ K E →
      RecOut Row.E7 B b₀ → ∀ Y : Subgroup G, K ≤ Y → b₀ ∈ Y →
        Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥ →
        (∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (Y : Set G)) →
        Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K

theorem l2ConstructYGenAt_E7_of (hF : E7FrameAt) (hR : E7RootCoreAt) (hC : E7CapAt) :
    L2ConstructYGenAt Row.E7 := by
  intro G _ _ b₀ K E hstd B hB hrec
  obtain ⟨U, g, hcomm, hpair, hKY, hb₀Y, hx, hroot, hgN, hUK⟩ := hF G b₀ K E hstd B hB hrec
  obtain ⟨hEm, hZ⟩ := isEm_eight_of_frame U hcomm hpair
  have hRY : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
      R ≤ Subgroup.centralizer ((⨆ k, U k : Subgroup G) : Set G) := by
    intro R hRC hRn h3
    obtain ⟨h1, h2⟩ := hR G b₀ K E hstd B hB hrec g hx hroot R hRC hRn h3
    rw [Subgroup.le_centralizer_iff] at h1 h2 ⊢
    exact iSup_le fun k => (hUK k).elim (fun h => h.trans h1) (fun h => h.trans h2)
  exact ⟨⨆ k, U k, hEm, hC G b₀ K E hstd B hB hrec _ hKY hb₀Y hZ hRY, hRY,
    iSup_le_sup_normalizer_of_frame hUK hgN⟩

theorem l2ConstructYAt_E7_of (hF : E7FrameAt) (hR : E7RootCoreAt) (hC : E7CapAt) :
    L2ConstructYAt Row.E7 :=
  l2ConstructYAt_of_gen (l2ConstructYGenAt_E7_of hF hR hC)

end CFSG.StandardType.FrameRoute.FS81
