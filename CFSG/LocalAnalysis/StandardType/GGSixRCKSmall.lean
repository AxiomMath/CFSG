module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallCompType
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33B0
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33InnCoprime
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynOrders
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.StandardType.RCKSmall

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

theorem rck_false_of_smallLabel
    (hC : CompTypeLie2Small) :
    ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ)
      (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    RCKSmallLabel ↥J →
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      CFSG.Assembly.LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    p ^ 4 ≤ Nat.card B₁ →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      CFSG.Assembly.LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ CFSG.Assembly.IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) → False := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hJs hpres hp hp2 hA hB₁A hDB₁ hD hAN hc1 hB₁ hB₁J hAG₀ hB₁L
    hHL hLG₀ hLx hDL hJ
  have hJsm : ∃ t' r' e', RCKSmallLieTag t' ∧
      CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t' r' 2 e' := by
    obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_markedModel hJs
    obtain ⟨R, _, I, F, -, -, θ, hP, hm⟩ := largeEvenRawDatum_exists hraw
    have hm' := MarkedModel.of_mulEquiv θ.symm hm
    obtain ⟨tg, rk, m⟩ := lab
    dsimp only [RCKSmallTag] at hP
    unfold MarkedModel at hm'
    rcases hP with rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, _, by simp [RCKSmallLieTag, markTag], hm'⟩
  obtain ⟨t', r', e', ht', hM'⟩ := hJsm
  obtain ⟨x, hxD, hx1, hLc⟩ := hLx
  have hLc' := CFSG.Assembly.isComponentOf_iff_open.1 hLc
  have hLq : CFSG.Open.IsQuasisimple ↥L := hLc'.2.2
  have hxL : x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.1 (hLc'.1 hl).2) x rfl).symm
  obtain ⟨d, hdD, hdL⟩ := Set.not_subset.1 hDL
  have hJ' := CFSG.Assembly.isComponentOf_iff_open.1 hJ
  have hK : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set X)) := by
    rw [← RCKU33.u33_inf_centralizer_eq hp hD hxD hx1 hxL hdD hdL]; exact hJ'
  have hJL : J ≤ L := hJ'.1.trans inf_le_left
  have hB₁el : IsElemAbelian p B₁ :=
    ⟨⟨⟨fun a b => by
      have := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, hB₁A a.2⟩ ⟨b, hB₁A b.2⟩)
      exact Subtype.ext this⟩⟩, fun y hy => hA.2 y (hB₁A hy)⟩
  have hpL := RCKU33.dvd_card_of_marking RCKU33.ggInnCoprimeRankInput hp hp2 hB₁el hB₁L hHL
    (RCKU33.card_inf_centralizer_bound hp hD hB₁J hJL hdD hdL hB₁)
  have hpG₀ : p ∣ Nat.card ↥G₀ := hpL.trans (Subgroup.card_dvd_of_le hLG₀)
  rcases notSmall_or_360_of_step1 hC hpres hp hp2 hA hAN hc1 hAG₀ hpG₀ (hB₁A (hDB₁ hxD)) hx1
    hLc with hLns | h360
  ·
    obtain ⟨tL, rL, eL, htL, hML⟩ := hLns
    have hInn : CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn p B₁ L := by
      rcases RCKU33.innDiagOn_or_derived hp hLq hpL hB₁L hHL with h | ⟨lab, hd, hm⟩
      · exact h
      · exfalso
        rcases hd with hg | hg
        · exact CFSG.LocalAnalysis.GLTheoremA.I141F.Ord.card_ne_6048_of_lieModel hML
            (CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der hg hm)
        · refine CFSG.LocalAnalysis.GLTheoremA.MI.evenLieOrder_ne_ordTits
            (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hML)
            (fun h => htL (Or.inr (Or.inr (Or.inr h)))) ?_
          rw [← CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hML]
          exact CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_twF4der hg hm
    have hyC : ¬ CentMod p L d := fun h => hdL
      (RCKU33.u33_mem_centralizer_of_centMod hp hLq hpL h.1
        fun l hl => h.2 (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers d)))
    rcases i141DynkinAt_notSmall_comp hC hp hp2 hLq ⟨tL, rL, eL, htL, hML⟩ hB₁el hInn
      (hDB₁ hdD) hyC hK with ⟨t₁, r₁, e₁, ht₁, hM₁⟩ | h
    · exact false_of_lieModel_small hM₁ ht₁ hM' ht'
    · exact false_of_card_360_small hM' ht' h.le
  ·
    have hdvd := RCKU33.card_centerQuot_dvd hJL
    rw [h360] at hdvd
    exact false_of_card_360_small hM' ht' (Nat.le_of_dvd (by norm_num) hdvd)

theorem rckSmallEmpty_of_compTypeLie2Small
    (hC : CompTypeLie2Small) : RCKSmallEmpty := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L hJ hpres _ hp hp2 hA hB₁A hDB₁ hD hAN hc1 _ hB₁J hB₁ _ _
    hAG₀ hB₁L hHL _ _ hLG₀ hLx hDL hJL _
  exact rck_false_of_smallLabel hC X t n f ψ p G₀ A B₁ D J L hJ hpres hp hp2 hA hB₁A hDB₁ hD hAN
    hc1 hB₁ hB₁J hAG₀ hB₁L hHL hLG₀ hLx hDL hJL

theorem rckSmallEmpty_holds :
    RCKSmallEmpty :=
  rckSmallEmpty_of_compTypeLie2Small compTypeLie2Small_holds

end CFSG.StandardType.RCKSmall
