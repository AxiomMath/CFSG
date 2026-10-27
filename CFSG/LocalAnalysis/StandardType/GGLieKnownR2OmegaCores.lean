module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
import CFSG.LieType.Universal.Spin.Generation.Eichler
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCoresPlus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCoresMinus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

namespace CFSG.StandardType.LieKnownR2.POmega

private theorem cores_coreOne_POmegaPlus_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hn3⟩)
    {β : Fin L.D.rank → ℤ} (hl : GGLongRoot L.D β) (u : L.K) {Rr Rm Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hRm : Rm = ggRootSub L.D (MonoidHom.id L.K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  subst hL
  exact Cores.spinPlus_coreOne hn hl u hRr hRm hQ

private theorem cores_coreFour_POmegaPlus_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hn3⟩)
    {β : Fin L.D.rank → ℤ} (hl : GGLongRoot L.D β) (u : L.K) {Rr Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set L.K) := by
  subst hL
  exact Cores.spinPlus_coreFour hn hl u hRr hQ

private theorem cores_coreOne_POmegaMinus_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadMinus n F b c), Spin.Twisted.minusDatum n hirr⟩)
    {β : Fin L.D.rank → ℤ} (hl : GGLongRoot L.D β) (u : L.K) {Rr Rm Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hRm : Rm = ggRootSub L.D (MonoidHom.id L.K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  subst hL
  exact Cores.spinMinus_coreOne hn hirr hl u hRr hRm hQ

private theorem cores_coreFour_POmegaMinus_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadMinus n F b c), Spin.Twisted.minusDatum n hirr⟩)
    {β : Fin L.D.rank → ℤ} (hl : GGLongRoot L.D β) (u : L.K) {Rr Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set L.K) := by
  subst hL
  exact Cores.spinMinus_coreFour hn hirr hl u hRr hQ

private theorem glue_rootGroup_isPGroup_POmegaPlus_of_eq {F : Type} [Field F]
    [CharP F 2] {n : ℕ} (hn : 3 ≤ n) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hn⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (u : L.K) {Rr : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u) : IsPGroup 2 Rr := by
  subst hL
  have h : IsPGroup 2 ((Spin.plusDatum n F hn).rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_of_isParametrization
      (CFSG.LieType.Steinberg.SpinPlus.isParametrization (K := F) hn) hβ
  subst hRr
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

private theorem glue_rootSub_ne_bot_POmegaPlus_of_eq {F : Type} [Field F] {n : ℕ}
    (hn : 3 ≤ n) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hn⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (u : L.K) :
    ggRootSub L.D (MonoidHom.id L.K) β u ≠ ⊥ := by
  subst hL
  intro hbot
  have hroot : (Spin.plusDatum n F hn).rootGroup β ≠ ⊥ :=
    CFSG.LieType.Universal.Spin.plusDatum_ne_bot hn β hβ
  exact hroot (by
    rw [ggRootSub] at hbot
    simp only [Subgroup.map_id] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hbot)

private theorem glue_rootGroup_isPGroup_POmegaMinus_of_eq {F : Type} [Field F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) {n : ℕ}
    (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadMinus n F bq cq), Spin.Twisted.minusDatum n hirr⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (u : L.K) {Rr : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u) : IsPGroup 2 Rr := by
  subst hL
  have h : IsPGroup 2 ((Spin.Twisted.minusDatum n hirr).rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_minusRootGroup (n := n) (K := F) hirr (p := 2) hβ
  subst hRr
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

private theorem glue_rootSub_ne_bot_POmegaMinus_of_eq {F : Type} [Field F]
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) {n : ℕ}
    (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadMinus n F bq cq), Spin.Twisted.minusDatum n hirr⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (u : L.K) :
    ggRootSub L.D (MonoidHom.id L.K) β u ≠ ⊥ := by
  subst hL
  intro hbot
  have hroot : (Spin.Twisted.minusDatum n hirr).rootGroup β ≠ ⊥ :=
    CFSG.LieType.Universal.Spin.Twisted.minusDatum_ne_bot n hirr β hβ
  exact hroot (by
    rw [ggRootSub] at hbot
    simp only [Subgroup.map_id] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hbot)

theorem coreOne_POmegaPlus_long
    {n f : ℕ} (hn : 4 ≤ n)
    {β : Fin (ggU .POmegaPlus n f).D.rank → ℤ} (hl : GGLongRoot (ggU .POmegaPlus n f).D β)
    (u : (ggU .POmegaPlus n f).K) {Rr Rm Q : Subgroup (ggU .POmegaPlus n f).K}
    (hRr : Rr = ggRootSub (ggU .POmegaPlus n f).D (MonoidHom.id (ggU .POmegaPlus n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .POmegaPlus n f).D (MonoidHom.id (ggU .POmegaPlus n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .POmegaPlus n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  have hn3 : 3 ≤ n := by omega
  have e : ggU .POmegaPlus n f =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  exact cores_coreOne_POmegaPlus_of_eq hn hn3 (ggU .POmegaPlus n f) e hl u hRr hRm hQ

theorem coreFour_POmegaPlus_long
    {n f : ℕ} (hn : 4 ≤ n)
    {β : Fin (ggU .POmegaPlus n f).D.rank → ℤ} (hl : GGLongRoot (ggU .POmegaPlus n f).D β)
    (u : (ggU .POmegaPlus n f).K) {Rr Q : Subgroup (ggU .POmegaPlus n f).K}
    (hRr : Rr = ggRootSub (ggU .POmegaPlus n f).D (MonoidHom.id (ggU .POmegaPlus n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .POmegaPlus n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .POmegaPlus n f).K) := by
  have hn3 : 3 ≤ n := by omega
  have e : ggU .POmegaPlus n f =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  exact cores_coreFour_POmegaPlus_of_eq hn hn3 (ggU .POmegaPlus n f) e hl u hRr hQ

theorem coreOne_POmegaMinus_long
    {n f : ℕ} (hn : 4 ≤ n)
    {β : Fin (ggU .POmegaMinus n f).D.rank → ℤ} (hl : GGLongRoot (ggU .POmegaMinus n f).D β)
    (u : (ggU .POmegaMinus n f).K) {Rr Rm Q : Subgroup (ggU .POmegaMinus n f).K}
    (hRr : Rr = ggRootSub (ggU .POmegaMinus n f).D (MonoidHom.id (ggU .POmegaMinus n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .POmegaMinus n f).D (MonoidHom.id (ggU .POmegaMinus n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .POmegaMinus n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  have e : ggU .POmegaMinus n f =
      ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal]
  exact cores_coreOne_POmegaMinus_of_eq (minusCoeffs_irr 2 f) hn (ggU .POmegaMinus n f) e
    hl u hRr hRm hQ

theorem coreFour_POmegaMinus_long
    {n f : ℕ} (hn : 4 ≤ n)
    {β : Fin (ggU .POmegaMinus n f).D.rank → ℤ} (hl : GGLongRoot (ggU .POmegaMinus n f).D β)
    (u : (ggU .POmegaMinus n f).K) {Rr Q : Subgroup (ggU .POmegaMinus n f).K}
    (hRr : Rr = ggRootSub (ggU .POmegaMinus n f).D (MonoidHom.id (ggU .POmegaMinus n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .POmegaMinus n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .POmegaMinus n f).K) := by
  have e : ggU .POmegaMinus n f =
      ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal]
  exact cores_coreFour_POmegaMinus_of_eq (minusCoeffs_irr 2 f) hn (ggU .POmegaMinus n f) e
    hl u hRr hQ

theorem ggSixLieKnown_of_pos_POmegaPlus
    (h : GGSixLieKnownPos .POmegaPlus) : GGSixLieKnown .POmegaPlus := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
    hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
    hE6c hA6 hField hN hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .POmegaPlus n 2 f := hmodel.admissible
  have hn : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have e : ggU .POmegaPlus n f =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  have hcenter : Subgroup.center (ggU .POmegaPlus n f).K = ⊥ := by
    rw [e]
    exact CFSG.SeitzReduction.SeitzQ2.center_spinGroup_quadPlus_eq_bot_of_charTwo hn3
      (GaloisField 2 f)
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
  have hoddker : Odd (Nat.card ψ.ker) := by
    rw [hkerbot, Subgroup.card_bot]
    exact odd_one
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, h2, h3⟩ :=
    h X n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB hcardD
      hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3 hE6c
      hA6 hField hN hE
  obtain ⟨β, hβ, hls, u, hR, hRm⟩ := hpos
  have hl : GGLongRoot (ggU .POmegaPlus n f).D β := by
    rcases hls with hl | hs
    · exact hl
    · exact absurd hs.1 (by
        rintro (h | h | ⟨h, -⟩) <;> exact absurd h (by decide))
  have hRleG₀ : R ≤ G₀ := hRJ.trans (hJL.trans hLG₀)
  have hRmap : R =
      (ggRootSub (ggU .POmegaPlus n f).D (MonoidHom.id (ggU .POmegaPlus n f).K) β u).map ψ :=
    hR.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRmmap : Rm =
      (ggRootSub (ggU .POmegaPlus n f).D (MonoidHom.id (ggU .POmegaPlus n f).K) (-β) u).map ψ :=
    hRm.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRp : IsPGroup 2 R := by
    rw [hRmap]
    exact (glue_rootGroup_isPGroup_POmegaPlus_of_eq hn3 _ e hβ u rfl).map ψ
  have hRne : R ≠ ⊥ := by
    rw [hRmap]
    intro hbot
    exact glue_rootSub_ne_bot_POmegaPlus_of_eq hn3 _ e hβ u
      ((Subgroup.map_eq_bot_iff_of_injective _ hψinj).mp hbot)
  have hbase : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ (R ⊔ Rm) = G₀ := by
    have h1 := Short.itemOne_of_core hker hoddker
      (glue_rootGroup_isPGroup_POmegaPlus_of_eq hn3 _ e hβ u rfl)
      (coreOne_POmegaPlus_long hn hl u rfl rfl rfl)
    rw [hψ, ← hRmap, ← hRmmap] at h1
    exact h1
  have hRle_pcore : R ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) :=
    GGRootNorm.le_pCoreOf_of_normalized
      (fun r hr => ⟨hRleG₀ hr, Subgroup.le_normalizer hr⟩)
      hRp
      (Subgroup.le_normalizer_iff.mp inf_le_right)
  have hitem1 : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ Rm = G₀ := by
    rw [← sup_assoc, sup_eq_left.mpr hRle_pcore] at hbase
    exact hbase
  have hitem4 : (⁅pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)),
        pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))⁆ ≤ R ∧
      pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ≤
        Subgroup.centralizer (R : Set X)) ∨
      ∀ V : Subgroup X,
        ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) ≤ V →
        V ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
        V ≠ ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) →
        V ≠ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
        G₀ ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (V : Set X) →
        J ⊔ V = G₀ := by
    have hcore := coreFour_POmegaPlus_long hn hl u rfl rfl
    have h1 := Short.itemFour_of_core hker hoddker
      (glue_rootGroup_isPGroup_POmegaPlus_of_eq hn3 _ e hβ u rfl) hcore.1 hcore.2
    rw [hψ, ← hRmap] at h1
    exact Or.inl h1
  exact ⟨R, Rm, hRJ, hRne, hRp, hRmJ, hitem1, h2, h3, hitem4⟩

theorem ggSixLieKnown_of_pos_POmegaMinus
    (h : GGSixLieKnownPos .POmegaMinus) : GGSixLieKnown .POmegaMinus := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
    hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
    hE6c hA6 hField hN hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .POmegaMinus n 2 f := hmodel.admissible
  have hn : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have e : ggU .POmegaMinus n f =
      ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal]
  have hcenter : Subgroup.center (ggU .POmegaMinus n f).K = ⊥ := by
    rw [e]
    exact CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn (minusCoeffs_irr 2 f)
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
  have hoddker : Odd (Nat.card ψ.ker) := by
    rw [hkerbot, Subgroup.card_bot]
    exact odd_one
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, h2, h3⟩ :=
    h X n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB hcardD
      hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3 hE6c
      hA6 hField hN hE
  obtain ⟨β, hβ, hls, u, hR, hRm⟩ := hpos
  have hl : GGLongRoot (ggU .POmegaMinus n f).D β := by
    rcases hls with hl | hs
    · exact hl
    · exact absurd hs.1 (by
        rintro (h | h | ⟨h, -⟩) <;> exact absurd h (by decide))
  have hRleG₀ : R ≤ G₀ := hRJ.trans (hJL.trans hLG₀)
  have hRmap : R =
      (ggRootSub (ggU .POmegaMinus n f).D (MonoidHom.id (ggU .POmegaMinus n f).K) β u).map ψ :=
    hR.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRmmap : Rm =
      (ggRootSub (ggU .POmegaMinus n f).D (MonoidHom.id (ggU .POmegaMinus n f).K) (-β) u).map ψ :=
    hRm.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRp : IsPGroup 2 R := by
    rw [hRmap]
    exact (glue_rootGroup_isPGroup_POmegaMinus_of_eq (minusCoeffs_irr 2 f) _ e hβ u rfl).map ψ
  have hRne : R ≠ ⊥ := by
    rw [hRmap]
    intro hbot
    exact glue_rootSub_ne_bot_POmegaMinus_of_eq (minusCoeffs_irr 2 f) _ e hβ u
      ((Subgroup.map_eq_bot_iff_of_injective _ hψinj).mp hbot)
  have hbase : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ (R ⊔ Rm) = G₀ := by
    have h1 := Short.itemOne_of_core hker hoddker
      (glue_rootGroup_isPGroup_POmegaMinus_of_eq (minusCoeffs_irr 2 f) _ e hβ u rfl)
      (coreOne_POmegaMinus_long hn hl u rfl rfl rfl)
    rw [hψ, ← hRmap, ← hRmmap] at h1
    exact h1
  have hRle_pcore : R ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) :=
    GGRootNorm.le_pCoreOf_of_normalized
      (fun r hr => ⟨hRleG₀ hr, Subgroup.le_normalizer hr⟩)
      hRp
      (Subgroup.le_normalizer_iff.mp inf_le_right)
  have hitem1 : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ Rm = G₀ := by
    rw [← sup_assoc, sup_eq_left.mpr hRle_pcore] at hbase
    exact hbase
  have hitem4 : (⁅pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)),
        pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))⁆ ≤ R ∧
      pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ≤
        Subgroup.centralizer (R : Set X)) ∨
      ∀ V : Subgroup X,
        ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) ≤ V →
        V ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
        V ≠ ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) →
        V ≠ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
        G₀ ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (V : Set X) →
        J ⊔ V = G₀ := by
    have hcore := coreFour_POmegaMinus_long hn hl u rfl rfl
    have h1 := Short.itemFour_of_core hker hoddker
      (glue_rootGroup_isPGroup_POmegaMinus_of_eq (minusCoeffs_irr 2 f) _ e hβ u rfl)
      hcore.1 hcore.2
    rw [hψ, ← hRmap] at h1
    exact Or.inl h1
  exact ⟨R, Rm, hRJ, hRne, hRp, hRmJ, hitem1, h2, h3, hitem4⟩

end CFSG.StandardType.LieKnownR2.POmega
