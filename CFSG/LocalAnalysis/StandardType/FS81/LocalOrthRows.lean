module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.LieType.Universal.Spin

private theorem disjoint_zpowers_of_center {G : Type} [Group G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) (hcenter : Subgroup.center K = ⊥) :
    Disjoint (Subgroup.zpowers b₀) K := by
  rw [Subgroup.disjoint_def]
  intro x hx hxK
  have hxcenter : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute b₀ (y : G) := (Subgroup.mem_centralizer_singleton_iff.mp (hKC y.2)).symm
    exact (hcomm.zpow_left m).eq.symm
  rw [hcenter] at hxcenter
  simpa using hxcenter

theorem exists_basis_localOrth_of_data
    {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) V, finrank (ZMod 2) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hind : OmegaAutIsometric Q) {n : ℕ} (hn : 2 ≤ n) {b₀ : G} {K E : Subgroup G}
    (φ : ↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hKs : IsSimpleGroup ↥K) (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hcenter : Subgroup.center K = ⊥)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E) (hmax : IsMaxElemAb3 K (E ⊓ K))
    (hcard : Nat.card ↥(E ⊓ K) = 3 ^ n) :
    ∃ B : Basis3 G (n + 1), Adapted B b₀ K E ∧ (LocalOrthI B b₀ ∨ LocalOrthII B b₀) ∧
      evenFix0 n ⊆ B.realized K := by
  have hA3 : IsPGroup 3 ↥(E ⊓ K) :=
    CFSG.StandardType.TableB.isPGroup_of_isElemAbelian hmax.2.1
  have hAnc : ¬ IsCyclic ↥(E ⊓ K) := by
    refine CFSG.StandardType.TableB.not_isCyclic_of_card (p := 3) (by norm_num) hmax.2.1.2 ?_
    rw [hcard]
    exact Nat.pow_le_pow_of_le (a := 3) (by norm_num) hn
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  have hKN : Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    normalizer_zpowers_le_normalizer hKs hKC hKn hcyc (A := E ⊓ K) inf_le_right hA3 hAnc
  exact exists_basis_localOrth_of_model (n := n) hQ hT hind (by omega) φ hb₀ hKC hdisj hKN
    hsup hmax hcard

theorem exists_basis_localOrth_even_D6 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6) :
    ∃ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E ∧ (LocalOrthI B b₀ ∨ LocalOrthII B b₀) ∧
      evenFix0 Row.D6.n ⊆ B.realized K := by
  obtain ⟨_, hHyp, hCanon⟩ := hstd
  obtain ⟨hrow, _, hsup, hmax, hcard, _⟩ := hCanon
  obtain ⟨hA, _, _, _, _, _⟩ := hHyp
  obtain ⟨hb₀, hKC, hKn, hcenter, _, hcyc, _, _⟩ := hA
  obtain ⟨hKs, ⟨φ⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_D6 hrow hcenter
  exact exists_basis_localOrth_of_data (n := 6)
    (nondegenerate_polarBilin_quadPlus 6 (ZMod 2))
    exists_totallySingular_three_quadPlus_six omegaAutIsometric_quadPlus_six
    (by norm_num) φ hKs hb₀ hKC hKn hcenter hcyc hsup hmax hcard

theorem l1LocalAt_D6 : L1LocalAt Row.D6 := by
  intro G _ _ b₀ K E hstd
  obtain ⟨B, hB, hloc, -⟩ := exists_basis_localOrth_even_D6 hstd.toLoc
  exact ⟨B, hB, hloc⟩

theorem exists_basis_localOrth_even_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) :
    ∃ B : Basis3 G (Row.twD7.n + 1), Adapted B b₀ K E ∧
      (LocalOrthI B b₀ ∨ LocalOrthII B b₀) ∧ evenFix0 7 ⊆ B.realized K := by
  obtain ⟨_, hHyp, hCanon⟩ := hstd
  obtain ⟨hrow, _, hsup, hmax, hcard, _⟩ := hCanon
  obtain ⟨hA, _, _, _, _, _⟩ := hHyp
  obtain ⟨hb₀, hKC, hKn, hcenter, _, hcyc, _, _⟩ := hA
  obtain ⟨hKs, ⟨φ⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hrow hcenter
  obtain ⟨B, hB, hloc, heven⟩ := exists_basis_localOrth_of_data (n := 7)
    (nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0))
    exists_totallySingular_three_quadMinus_seven omegaAutIsometric_quadMinus_seven
    (by norm_num) φ hKs hb₀ hKC hKn hcenter hcyc hsup hmax hcard
  exact ⟨B, hB, hloc, heven⟩

theorem l1LocalAt_twD7 : L1LocalAt Row.twD7 := by
  intro G _ _ b₀ K E hstd
  obtain ⟨B, hB, hloc, -⟩ := exists_basis_localOrth_even_twD7 hstd
  exact ⟨B, hB, hloc⟩

end CFSG.StandardType.FrameRoute.FS81
