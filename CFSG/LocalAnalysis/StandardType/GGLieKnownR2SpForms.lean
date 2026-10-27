module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ItemThree
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSp
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus

public section

namespace CFSG.StandardType.LieKnownR2.PSp

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem

private theorem l10sbsp_inner_range
    {n f : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    (φ : (ggU .PSp n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (u : (ggU .PSp n f).K) :
    GGRootNormInner ((ggRootSub (ggU .PSp n f).D φ β u).subgroupOf φ.range) := by
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hZ : Subgroup.center (ggU .PSp n f).K = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := GaloisField 2 f) n
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hZ))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have hI : GGRootNormInner
      (((ggU .PSp n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    ggRootNormInner_sp (F := GaloisField 2 f) hn hβ u
  have hmap := ggRootNormInner_map_mulEquiv (MonoidHom.ofInjective hinj) hI
  have hRbar : (((ggU .PSp n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (MonoidHom.ofInjective hinj).toMonoidHom =
      ((((ggU .PSp n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        φ).subgroupOf φ.range := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro hr
      exact ⟨(MonoidHom.ofInjective hinj).symm x, hr,
        MonoidHom.apply_ofInjective_symm hinj x⟩
    · rintro ⟨r, hr, hx⟩
      have hx' : MonoidHom.ofInjective hinj r = x := by
        apply Subtype.ext
        simpa only [MonoidHom.ofInjective_apply hinj] using hx
      rw [← hx']
      simpa using hr
  rw [hRbar] at hmap
  exact hmap

theorem ggRootInnerAt_ggU_psp
    {n f : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    (φ : (ggU .PSp n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (u : (ggU .PSp n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .PSp n f).D φ β u) := by
  have hI := l10sbsp_inner_range hn φ hker hβ u
  intro Y hY2 hYK hYR hNY
  exact ggRootNormInner_le_sup_centralizer (Subgroup.map_le_range _ _) hYK hYR hY2 hNY hI

theorem itemThree_ggU_psp
    {n f : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    (ψ : (ggU .PSp n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (u : (ggU .PSp n f).K) {R : Subgroup X} (hR : R = ggRootSub (ggU .PSp n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hI := l10sbsp_inner_range hn ψ hker hβ u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

theorem ggRootNoCentralAt_ggU_psp
    {n f : ℕ} (hadm : StatedLieAdmissible .PSp n 2 f) {X : Type} [Group X] [Finite X]
    (φ : (ggU .PSp n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (u : (ggU .PSp n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .PSp n f).D φ β u) := by
  have hn : 2 ≤ n := hadm.2.2.1
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hZ : Subgroup.center (ggU .PSp n f).K = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := GaloisField 2 f) n
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hZ))
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hkerbot, Subgroup.card_bot]
    exact odd_one
  have hR : IsPGroup 2
      (((ggU .PSp n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    (GGRootSp.isPGroup_rootGroup hβ).map (MulAut.conj u).toMonoidHom
  have hNC : GGRootNoCentralAt (⊤ : Subgroup (ggU .PSp n f).K)
      (((ggU .PSp n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    ggRootNoCentral_sp (F := GaloisField 2 f) hn hβ u
  exact CFSG.StandardType.LieKnownR2.SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker
    φ hker hodd hR hNC

private lemma l10sbsp_map_ne_bot_of_isPGroup_two_of_odd_ker
    {U X : Type} [Group U] [Group X] {ψ : U →* X} (hodd : Odd (Nat.card ψ.ker))
    {S : Subgroup U} (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) : S.map ψ ≠ ⊥ := by
  intro hbot
  rw [Subgroup.map_eq_bot_iff] at hbot
  have hdisj : S ⊓ ψ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxS, hxK⟩ := hx
    obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp hS) ⟨x, hxS⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard ψ.ker hxK
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left k) hk hdvd)
  have hle : S ≤ ⊥ := by
    rw [← hdisj]
    exact fun x hx => ⟨hx, hbot hx⟩
  exact hSne (le_bot_iff.mp hle)

theorem ggSixLieKnown_of_pos_PSp
    (h : GGSixLieKnownPos .PSp) : GGSixLieKnown .PSp := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
    hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
    hE6c hA6 hField hN hE
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hZ : Subgroup.center (ggU .PSp n f).K = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := GaloisField 2 f) n
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hZ))
  have hoddker : Odd (Nat.card ψ.ker) := by
    rw [hkerbot, Subgroup.card_bot]
    exact odd_one
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, h2, h3⟩ :=
    h X n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB hcardD
      hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3 hE6c
      hA6 hField hN hE
  obtain ⟨β, hβ, _, u, hR, hRm⟩ := hpos
  have hRleG₀ : R ≤ G₀ := hRJ.trans (hJL.trans hLG₀)
  have hRmap : R = (ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u).map ψ :=
    hR.trans (CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map _ _ _ _)
  have hRmmap : Rm =
      (ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) (-β) u).map ψ :=
    hRm.trans (CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map _ _ _ _)
  have hRp : IsPGroup 2 R := by
    rw [hRmap]
    exact (CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_PSp hβ u rfl).map ψ
  have hSne : ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u ≠ ⊥ := by
    intro hbot
    have hroot : (ggU .PSp n f).D.rootGroup β ≠ ⊥ :=
      (CFSG.LieType.Universal.Symplectic.steinbergExtras n (GaloisField 2 f)).ne_bot β hβ
    apply hroot
    rw [ggRootSub] at hbot
    simp only [Subgroup.map_id] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hbot
  have hRne : R ≠ ⊥ := by
    rw [hRmap]
    exact l10sbsp_map_ne_bot_of_isPGroup_two_of_odd_ker hoddker
      (CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_PSp hβ u rfl) hSne
  have hbase : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ (R ⊔ Rm) = G₀ := by
    by_cases hl : GGLongRoot (ggU .PSp n f).D β
    · have h1 := CFSG.StandardType.LieKnownR2.Short.itemOne_of_core hker hoddker
        (CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_PSp hβ u rfl)
        (coreOne_PSp_long hl u rfl rfl rfl)
      rw [hψ, ← hRmap, ← hRmmap] at h1
      exact h1
    · have hs : ¬ GGLongRoot (ggU .PSp n f).D β := hl
      have h1 := CFSG.StandardType.LieKnownR2.Short.itemOne_PSp ψ hker hoddker hβ hs u hR hRm rfl
      rw [hψ] at h1
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
    by_cases hl : GGLongRoot (ggU .PSp n f).D β
    · have hcore := coreFour_PSp_long hl u rfl rfl
      have h1 := CFSG.StandardType.LieKnownR2.Short.itemFour_of_core hker hoddker
        (CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_PSp hβ u rfl) hcore.1 hcore.2
      rw [hψ, ← hRmap] at h1
      exact Or.inl h1
    · have hs : ¬ GGLongRoot (ggU .PSp n f).D β := hl
      have h1 :=
        CFSG.StandardType.LieKnownR2.Short.itemFour_PSp ψ hker hoddker hβ hs u hR hRm rfl
      rw [hψ] at h1
      exact Or.inl h1
  exact ⟨R, Rm, hRJ, hRne, hRp, hRmJ, hitem1, h2, h3, hitem4⟩

end CFSG.StandardType.LieKnownR2.PSp
