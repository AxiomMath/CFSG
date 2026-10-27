module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CoreProjection
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentDecomp
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7TorusSwap

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def twD7BetaHost {G : Type} [Group G] (b₀ : G) (K E : Subgroup G)
    (B : Basis3 G 8) : Subgroup G :=
  ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ⊔
    (centralizer ({b₀ * B.b 1} : Set G) ⊓ normalizer (E : Set G))

theorem le_twD7BetaHost_of_std {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) : E ≤ twD7BetaHost b₀ K E B := by
  have hE : IsElemAbelian 3 E := hstd.2.1.2.1.2.1
  have hβE : b₀ * B.b 1 ∈ E :=
    E.mul_mem hstd.2.1.2.2.1 (hB.1 ▸ B.b_mem_span 1)
  have hEC : E ≤ centralizer ({b₀ * B.b 1} : Set G) := by
    intro e he
    rw [mem_centralizer_iff]
    rintro x rfl
    exact congrArg (fun y : E => (y : G))
      (hE.1.is_comm.comm (⟨b₀ * B.b 1, hβE⟩ : E) (⟨e, he⟩ : E))
  exact (le_inf hEC (le_normalizer : E ≤ normalizer (E : Set G))).trans le_sup_right

theorem twD7BetaHost_le_of_std {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} :
    twD7BetaHost b₀ K E B ≤ centralizer ({b₀ * B.b 1} : Set G) ∧
      twD7BetaHost b₀ K E B ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G) := by
  obtain ⟨hMK, hMβ⟩ := commutator_centralizer_le_beta_of_std_twD7 hstd B
  have hKC : K ≤ centralizer ({b₀} : Set G) := hstd.2.1.1.2.1
  exact ⟨sup_le hMβ inf_le_left,
    sup_le (hMK.trans (hKC.trans le_sup_left)) (inf_le_right.trans le_sup_right)⟩

theorem centralizer_inf_le_twD7BetaHost_of_std {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    centralizer ({B.b 1} : Set G) ⊓ K ≤ twD7BetaHost b₀ K E B := by
  have hC := (centralizer_inf_eq_zpowers_sup_commutator_twD7 hstd hB hrec).1
  exact hC.le.trans
    (sup_le (zpowers_le.mpr (le_twD7BetaHost_of_std hstd hB (hB.1 ▸ B.b_mem_span 1)))
      le_sup_left)

theorem mem_normalizer_twD7BetaHost {G : Type} [Group G]
    (b₀ : G) (K E : Subgroup G) (B : Basis3 G 8) {g : G}
    (hgβ : g ∈ normalizer (zpowers (b₀ * B.b 1) : Set G))
    (hgE : g ∈ normalizer (E : Set G))
    (hgM : g ∈ normalizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
      centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G)) :
    g ∈ normalizer (twD7BetaHost b₀ K E B : Set G) := by
  have hCeq : centralizer (zpowers (b₀ * B.b 1) : Set G) =
      centralizer ({b₀ * B.b 1} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCN : normalizer (zpowers (b₀ * B.b 1) : Set G) ≤
      normalizer (centralizer (zpowers (b₀ * B.b 1) : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hgC : g ∈ normalizer (centralizer ({b₀ * B.b 1} : Set G) : Set G) :=
    hCeq ▸ hCN hgβ
  have hgH : g ∈ normalizer ((centralizer ({b₀ * B.b 1} : Set G) ⊓
      normalizer (E : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hgC, Subgroup.le_normalizer hgE⟩
  exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hgM, hgH⟩

theorem exists_attached_e7_of_twD7BetaHost_projection
    {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (π : twD7BetaHost b₀ K E B →* CFSG.Blueprint.Chevalley.adjointGroup .E7 (ZMod 2))
    (hπ : Function.Surjective π)
    (hker : ∃ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) ∧
      (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R₁ ∧
      π.ker ≤ R₁.subgroupOf (twD7BetaHost b₀ K E B) ⊔
        (zpowers (b₀ * B.b 1)).subgroupOf (twD7BetaHost b₀ K E B))
    (τ : G) (hτE : τ ∈ normalizer (E : Set G))
    (hτβ : τ ∈ centralizer ({b₀ * B.b 1} : Set G))
    (hτ0 : τ * B.b 0 * τ⁻¹ = B.b 1) :
    ∃ J : Subgroup G, J ≤ twD7BetaHost b₀ K E B ∧
      J ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G) ∧
      J ≤ centralizer ({b₀ * B.b 1} : Set G) ∧
      Nonempty (J ≃* CFSG.Blueprint.Chevalley.adjointGroup .E7 (ZMod 2)) ∧
      Adapted B.twD7Beta (b₀ * B.b 1) J E ∧
      ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J ∧
      (∀ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) →
        (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R₁ →
        R₁ ≤ centralizer (J : Set G)) ∧
      (normalizer (zpowers (b₀ * B.b 1) : Set G) ⊓ normalizer (E : Set G)) ⊓
        normalizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
          centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ≤
        normalizer (J : Set G) ∧
      IsSimpleGroup J ∧
      ∃ η : J ≃* CFSG.Blueprint.Chevalley.adjointGroup .E7 (ZMod 2),
        ∀ j : J, ∀ hj : (j : G) ∈ twD7BetaHost b₀ K E B, η j = π ⟨(j : G), hj⟩ := by
  have hτH : τ ∈ twD7BetaHost b₀ K E B :=
    (le_sup_right : centralizer ({b₀ * B.b 1} : Set G) ⊓ normalizer (E : Set G) ≤
      twD7BetaHost b₀ K E B) ⟨hτβ, hτE⟩
  obtain ⟨hHβ, hHH₀⟩ := twD7BetaHost_le_of_std hstd
  obtain ⟨J, hJH, hJH₀, hJβ, hmodel, hAdapt, hMJ, hcore, hNJ, hJs, hGraph⟩ :=
    exists_attached_e7_of_std_twD7_projection b₀ K E hstd B hB hrec
    (twD7BetaHost b₀ K E B) (le_twD7BetaHost_of_std hstd hB)
    (centralizer_inf_le_twD7BetaHost_of_std hstd hB hrec) hHβ hHH₀ π hπ hker
    ⟨τ, hτH⟩ hτ0
  refine ⟨J, hJH, hJH₀, hJβ, hmodel, hAdapt, hMJ, hcore, ?_, hJs, hGraph⟩
  intro g hg
  exact hNJ ⟨mem_normalizer_twD7BetaHost b₀ K E B hg.1.1 hg.1.2 hg.2, hg.1.2⟩

end CFSG.StandardType.FrameRoute.FS81
