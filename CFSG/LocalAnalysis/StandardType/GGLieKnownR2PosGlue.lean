module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSixKnownRemainingDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.StandardType.LieKnownR2.OddCenter
open scoped commutatorElement

private lemma map_ne_bot_of_isPGroup_two_of_odd_ker
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

theorem ggSixLieKnown_of_pos_F4
    (h : GGSixLieKnownPos .F4) : GGSixLieKnown .F4 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
    hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
    hE6c hA6 hField hN hE
  have hadm : StatedLieAdmissible .F4 n 2 f := hmodel.admissible
  have hoddker : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat
      (odd_card_center_ggU (by decide) hadm)
      (Subgroup.card_dvd_of_le hker)
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, h2, h3⟩ :=
    h X n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB hcardD
      hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3 hE6c
      hA6 hField hN hE
  obtain ⟨β, hβ, hls, u, hR, hRm⟩ := hpos
  have hRleG₀ : R ≤ G₀ := hRJ.trans (hJL.trans hLG₀)
  have hRmap : R = (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  have hRmmap : Rm =
      (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  have hRp : IsPGroup 2 R := by
    rw [hRmap]
    exact (rootGroup_isPGroup_F4 hβ u rfl).map ψ
  have hSne : ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u ≠ ⊥ := by
    intro hbot
    have hroot : (ggU .F4 n f).D.rootGroup β ≠ ⊥ :=
      (f4_steinbergExtras_exact (GaloisField 2 f)).ne_bot β hβ
    apply hroot
    rw [ggRootSub] at hbot
    simp only [Subgroup.map_id] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hbot
  have hRne : R ≠ ⊥ := by
    rw [hRmap]
    exact map_ne_bot_of_isPGroup_two_of_odd_ker hoddker
      (rootGroup_isPGroup_F4 hβ u rfl) hSne
  have hbase : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ (R ⊔ Rm) = G₀ := by
    by_cases hl : GGLongRoot (ggU .F4 n f).D β
    · have h1 := itemOne_of_core hker hoddker (rootGroup_isPGroup_F4 hβ u rfl)
        (coreOne_F4_long hl u rfl rfl rfl)
      rw [hψ, ← hRmap, ← hRmmap] at h1
      exact h1
    · have hs : ¬ GGLongRoot (ggU .F4 n f).D β := hl
      have h1 := itemOne_F4 hadm ψ hker hoddker hβ hs u hR hRm rfl
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
    by_cases hl : GGLongRoot (ggU .F4 n f).D β
    · have hcore := coreFour_F4_long hl u rfl rfl
      have h1 := itemFour_of_core hker hoddker (rootGroup_isPGroup_F4 hβ u rfl)
        hcore.1 hcore.2
      rw [hψ, ← hRmap] at h1
      exact Or.inl h1
    · have hs : ¬ GGLongRoot (ggU .F4 n f).D β := hl
      have h1 := itemFour_F4 hadm ψ hker hoddker hβ hs u hR hRm rfl
      rw [hψ] at h1
      exact Or.inl h1
  exact ⟨R, Rm, hRJ, hRne, hRp, hRmJ, hitem1, h2, h3, hitem4⟩

theorem ggSixLieKnown_of_pos_twistedE6
    (h : GGSixLieKnownPos .twistedE6) : GGSixLieKnown .twistedE6 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
    hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
    hE6c hA6 hField hN hE
  have hadm : StatedLieAdmissible .twistedE6 n 2 f := hmodel.admissible
  have hf1 : 1 ≤ f := hadm.2.1
  have hoddker : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat
      (odd_card_center_ggU (by decide) hadm)
      (Subgroup.card_dvd_of_le hker)
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, h2, h3⟩ :=
    h X n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB hcardD
      hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3 hE6c
      hA6 hField hN hE
  obtain ⟨β, hβ, hls, u, hR, hRm⟩ := hpos
  have hRleG₀ : R ≤ G₀ := hRJ.trans (hJL.trans hLG₀)
  have hRmap : R =
      (ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  have hRmmap : Rm =
      (ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  have hRp : IsPGroup 2 R := by
    rw [hRmap]
    exact (rootGroup_isPGroup_twistedE6 hβ u rfl).map ψ
  have hSne :
      ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u ≠ ⊥ := by
    intro hbot
    have hθ : ∀ c : GaloisField 2 (2 * f), frobQ 2 f (frobQ 2 f c) = c :=
      frobQ_frobQ 2 f hf1
    have hroot : (ggU .twistedE6 n f).D.rootGroup β ≠ ⊥ :=
      (twistedDatum_steinbergExtras (k := GaloisField 2 (2 * f)) (θ := frobQ 2 f) hθ).ne_bot β hβ
    apply hroot
    rw [ggRootSub] at hbot
    simp only [Subgroup.map_id] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hbot
  have hRne : R ≠ ⊥ := by
    rw [hRmap]
    exact map_ne_bot_of_isPGroup_two_of_odd_ker hoddker
      (rootGroup_isPGroup_twistedE6 hβ u rfl) hSne
  have hbase : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ (R ⊔ Rm) = G₀ := by
    by_cases hl : GGLongRoot (ggU .twistedE6 n f).D β
    · have h1 := itemOne_of_core hker hoddker (rootGroup_isPGroup_twistedE6 hβ u rfl)
        (coreOne_twistedE6_long hf1 hl u rfl rfl rfl)
      rw [hψ, ← hRmap, ← hRmmap] at h1
      exact h1
    · have hs : ¬ GGLongRoot (ggU .twistedE6 n f).D β := hl
      have hpdvd : p ∣ 2 ^ f - 1 := by
        rcases (hls.resolve_left hl).1 with h | h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact h.2
      have hf2 : 2 ≤ f := by
        by_contra hf
        have hf_eq : f = 1 := by omega
        have hpdvd1 : p ∣ 1 := by simpa [hf_eq] using hpdvd
        exact hp.ne_one (Nat.dvd_one.mp hpdvd1)
      have h1 := itemOne_twistedE6 ψ hker hoddker hβ hs hf2 u hR hRm rfl
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
    by_cases hl : GGLongRoot (ggU .twistedE6 n f).D β
    · have hcore := coreFour_twistedE6_long hf1 hl u rfl rfl
      have h1 := itemFour_of_core hker hoddker (rootGroup_isPGroup_twistedE6 hβ u rfl)
        hcore.1 hcore.2
      rw [hψ, ← hRmap] at h1
      exact Or.inl h1
    · have hs : ¬ GGLongRoot (ggU .twistedE6 n f).D β := hl
      have hpdvd : p ∣ 2 ^ f - 1 := by
        rcases (hls.resolve_left hl).1 with h | h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact h.2
      have hf2 : 2 ≤ f := by
        by_contra hf
        have hf_eq : f = 1 := by omega
        have hpdvd1 : p ∣ 1 := by simpa [hf_eq] using hpdvd
        exact hp.ne_one (Nat.dvd_one.mp hpdvd1)
      have h1 := itemFourIrred_twistedE6 ψ hker hoddker hβ hs hf2 u hR hRm rfl
      rw [hψ] at h1
      exact Or.inr fun V hV1 hV2 hV3 hV4 hVN => absurd hVN (h1 V hV1 hV2 hV3 hV4)
  exact ⟨R, Rm, hRJ, hRne, hRp, hRmJ, hitem1, h2, h3, hitem4⟩

theorem ggSixLieKnownRemaining_of_pos
    (h : GGSixLieKnownRemainingPos) : GGSixLieKnownRemaining :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    ggSixLieKnown_of_pos_F4 h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    ggSixLieKnown_of_pos_twistedE6 h.2.2.2.2.2.2.2.2.2⟩

end CFSG.StandardType.LieKnownR2.Short
