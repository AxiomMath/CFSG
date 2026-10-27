module

public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit
public import CFSG.LocalAnalysis.StandardType.FS81.FrameEm

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Assembly CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

@[expose] def D6FrameAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.D6 → ∀ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E →
      RecOut Row.D6 B b₀ →
      ∃ (U : Fin 7 → Subgroup G) (g : G),
        (∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
          ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a) ∧
        (∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) ∧
        K ≤ ⨆ k, U k ∧ b₀ ∈ ⨆ k, U k ∧ g * b₀ * g⁻¹ ∈ K ∧ g⁻¹ * b₀ * g ∈ K ∧
        g ∈ Subgroup.normalizer (E : Set G) ∧
        ∀ k, U k ≤ K ∨ U k ≤ K.map (MulAut.conj g).toMonoidHom

@[expose] def D6RootCoreAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.D6 → ∀ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E →
      RecOut Row.D6 B b₀ → ∀ g : G, g * b₀ * g⁻¹ ∈ K → g⁻¹ * b₀ * g ∈ K →
        ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (K : Set G) ∧
            R ≤ Subgroup.centralizer (K.map (MulAut.conj g).toMonoidHom : Set G)

@[expose] def D6CapAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.D6 → ∀ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E →
      RecOut Row.D6 B b₀ → ∀ Y : Subgroup G, K ≤ Y → b₀ ∈ Y →
        Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥ →
        (∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (Y : Set G)) →
        Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K

theorem l2ConstructYGenAt_D6_of (hF : D6FrameAt) (hR : D6RootCoreAt) (hC : D6CapAt) :
    L2ConstructYGenAt Row.D6 := by
  intro G _ _ b₀ K E hstd B hB hrec
  obtain ⟨U, g, hcomm, hpair, hKY, hb₀Y, hx, hx', hgE, hUK⟩ := hF G b₀ K E hstd B hB hrec
  obtain ⟨hEm, hZ⟩ := isEm_seven_of_frame U hcomm hpair
  have hRY : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
      R ≤ Subgroup.centralizer ((⨆ k, U k : Subgroup G) : Set G) := by
    intro R hRC hRn h3
    obtain ⟨h1, h2⟩ := hR G b₀ K E hstd B hB hrec g hx hx' R hRC hRn h3
    rw [Subgroup.le_centralizer_iff] at h1 h2 ⊢
    exact iSup_le fun k => (hUK k).elim (fun h => h.trans h1) (fun h => h.trans h2)
  exact ⟨⨆ k, U k, hEm, hC G b₀ K E hstd B hB hrec _ hKY hb₀Y hZ hRY, hRY,
    iSup_le_sup_normalizer_of_frame hUK (Subgroup.mem_sup_right hgE)⟩

theorem l2ConstructYAt_D6_of (hF : D6FrameAt) (hR : D6RootCoreAt) (hC : D6CapAt) :
    L2ConstructYAt Row.D6 :=
  l2ConstructYAt_of_gen (l2ConstructYGenAt_D6_of hF hR hC)

end CFSG.StandardType.FrameRoute.FS81
