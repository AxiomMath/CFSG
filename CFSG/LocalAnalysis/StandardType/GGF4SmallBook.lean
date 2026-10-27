module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4SmallDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLang
import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGSecFiveBMaxToPair

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly

theorem ggF4Small_card_A3 {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (h : GGWeylOfType p (CoxeterMatrix.A 3) A) :
    Nat.card ↥A = 24 := by
  obtain ⟨e, -⟩ := h
  rw [← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA 3]
  norm_num [Nat.factorial]

theorem ggF4Small_weylOfType_F4 {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (hP : GGCoxeterPres p A M e) (hF : GGIsWeylMatrixF4 M) :
    GGWeylOfType p CoxeterMatrix.F₄ A := by
  have hW : GGWeylOfType p M A := ⟨e, hP.2⟩
  obtain ⟨e', rfl⟩ := hF
  exact hW.of_reindex

theorem ggF4Small_ks_nonempty
    {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G} {ks : Finset (Subgroup G)}
    (hW4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs ks))
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) : ks.Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  subst hne
  have h1 : ggAutomizerJoin L Bs (∅ : Finset (Subgroup G)) = ggAutomizer L Bs := by
    simp [ggAutomizerJoin]
  have h2 := ggF4Orig_card_weylOfType_F4 hW4
  have h3 := ggF4Small_card_A3 hA3
  rw [h1] at h2
  omega

theorem ggF4Small_join_induced {G : Type} [Group G] {Bs : Subgroup G} (L : Subgroup G)
    (ks : Finset (Subgroup G)) :
    ∀ φ ∈ ggAutomizerJoin L Bs ks, ∃ g : G, ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by
  intro φ hφ
  rw [ggAutomizerJoin] at hφ
  have h : φ ∈ ggAutomizer (⊤ : Subgroup G) Bs :=
    sup_le (ggAutomizer_mono Bs le_top)
      (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top) hφ
  obtain ⟨g, -, -, hg⟩ := mem_ggInduced_top_of_mem_ggAutomizer h
  exact ⟨g, hg⟩

theorem ggF4Small_card_Bs
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ks : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J ks)
    (hW4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs ks)) (hne : ks.Nonempty) :
    Nat.card ↥Bs = p ^ 4 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  have hleJoin : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs ks :=
    sup_le le_sup_left (le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl))
  have hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizerJoin L Bs ks, φ b = b) → b = 1 :=
    fun b hb => GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR.1 hR.2.1 hN b
      (fun φ hφ => hb φ (hleJoin hφ))
  have hle : Nat.card ↥Bs ≤ p ^ Fintype.card (Fin 4) :=
    SpJoinRefl.card_le_pow_of_weylOfType hW4 hfix
  rw [Fintype.card_fin] at hle
  obtain ⟨-, -, -, -, h4⟩ := hR.1.1.tableB_facts
  exact le_antisymm hle h4

theorem ggF4Small_eq_Bs {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = p ^ 4) : B = Bs := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hcfg.1
  apply Subgroup.eq_of_le_of_card_ge hcfg.2.1.1
  rw [hcard]
  exact pow_four_le_card_of_bmax hβ.1 hS.1 hβ.2.2.2

theorem ggF4Small_markingK
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hNb : GGNbr p B x D J y K)
    (hlab : GGHasLabel ⟨.A, 5, 1⟩ (K ⧸ Subgroup.center K)) :
    LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1) := by
  have hq : CFSG.Assembly.IsQuasisimple ↥K :=
    isQuasisimple_of_largeEvenMarking (hR.2.2.1.2 y K hNb)
  have hΛ : LargeEvenInLambda2 (⟨.A, 5, 1⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    decide
  refine largeEvenMarking_mono (fun lab R _ I F θ h => ?_)
    (largeEvenMarking_of_hasLabel hq hΛ hlab)
  subst h
  exact ⟨rfl, rfl, rfl⟩

end CFSG.StandardType

end
