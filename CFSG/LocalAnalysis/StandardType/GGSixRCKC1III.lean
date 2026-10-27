module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryFour
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Transport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIFixedUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryOrthBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeLinear
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIPSpField
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8Prime
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8Five
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8Three
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8SevenE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE7LabelEnd
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Label
public import Certificates.Certificate14972
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeOrthogonalPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAssembly
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Helpers
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIF4
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE7

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.RCKK1IIISp

@[expose] def RCKRowK2AtField
    (i : GGSixRCKRow) (Pos : RCKPos) (f : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGSixRCKJRow i J →
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ (rb : ↥J ⧸ Subgroup.center ↥J) (Vb : Subgroup (↥J ⧸ Subgroup.center ↥J)),
      RCKK1Data rb Vb → Pos ↥J rb Vb →
      ∀ (V : Subgroup X) (r : ↥J), (r : X) ∈ V → V ≤ J → IsElemAbelian 2 V → Nat.card V = 4 →
        QuotientGroup.mk' (Subgroup.center ↥J) r = rb →
        (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) = Vb →
        (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) →
        (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
          Y ≤ Subgroup.centralizer {(r : X)} →
          (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
          ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
            v * y * v⁻¹ * y⁻¹ = (r : X) ^ k * z) →
        RCKK2 G₀ D J V r

@[expose] def RCKRowK2IIIAtTwoRemaining :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n : ℕ) (ψ : (ggU t n 1).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGSixRCKJRow .III J →
    GGPresentsG0 G₀ (ggU t n 1).D t n 1 ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ (rb : ↥J ⧸ Subgroup.center ↥J) (Vb : Subgroup (↥J ⧸ Subgroup.center ↥J)),
      RCKK1Data rb Vb → RCKPosShort ↥J rb Vb →
      ∀ (V : Subgroup X) (r : ↥J), (r : X) ∈ V → V ≤ J → IsElemAbelian 2 V → Nat.card V = 4 →
        QuotientGroup.mk' (Subgroup.center ↥J) r = rb →
        (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) = Vb →
        (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) →
        (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
          Y ≤ Subgroup.centralizer {(r : X)} →
          (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
          ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
            v * y * v⁻¹ * y⁻¹ = (r : X) ^ k * z) →
        ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X,
          IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
          J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) → K ≠ J →
          (∀ (m : ℕ) (η : ↥K ≃* CFSG.Open.StatedSp m (GaloisField 2 1)),
            3 ≤ m → ¬ (∀ v ∈ (V.subgroupOf K).map η.toMonoidHom, v ≠ 1 →
              ∃ x y : Fin m ⊕ Fin m → GaloisField 2 1,
                spB m x y = 0 ∧ SpSiegel x y v)) →
          (LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 → ¬ OmegaSixEmbed K J) →
          ¬ FixedSpBlockAt K J → ¬ FixedSUBlockAt K J → ¬ FixedOrthBlockAt K J →
          B₁ ≤ Subgroup.normalizer (K : Set X) →
          (∃ d ∈ D, d ∉ Subgroup.zpowers e ∧ IsComponentOf J (K ⊓ Subgroup.centralizer {d})) →
          (RCKRP.RCKClassicalTag t → ∃ s : StatedLieTag,
            RCKRP.RCKClassicalTag s ∧ s ≠ .PSU ∧ s ≠ .PSL ∧ s ≠ .PSp ∧ s ≠ .POmegaMinus ∧
              RCKRP.RCKClassicalModelIDAt s K B₁) →
          (¬ ∃ (m : ℕ) (φ : (ggU .PSp m 1).K →* X), φ.range = K ∧
            φ.ker ≤ Subgroup.center (ggU .PSp m 1).K ∧
            ∀ b ∈ B₁, GGPsiInnerDiag (ggU .PSp m 1).D φ b) →
          t ≠ .E6 → t ≠ .F4 → t ≠ .twistedE6 →
          t ≠ .E7 → t ≠ .E8 →
          (¬ RCKRP.RCKClassicalModelIDAt .POmegaPlus K B₁) → K2At K V r

section Certificates

theorem rckRowK2AtField_III_one_E6 :
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (ψ : (ggU .E6 n 1).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGSixRCKJRow .III J →
    GGPresentsG0 G₀ (ggU .E6 n 1).D .E6 n 1 ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ (rb : ↥J ⧸ Subgroup.center ↥J) (Vb : Subgroup (↥J ⧸ Subgroup.center ↥J)),
      RCKK1Data rb Vb → RCKPosShort ↥J rb Vb →
      ∀ (V : Subgroup X) (r : ↥J), (r : X) ∈ V → V ≤ J → IsElemAbelian 2 V → Nat.card V = 4 →
        QuotientGroup.mk' (Subgroup.center ↥J) r = rb →
        (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) = Vb →
        (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) →
        (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
          Y ≤ Subgroup.centralizer {(r : X)} →
          (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
          ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
            v * y * v⁻¹ * y⁻¹ = (r : X) ^ k * z) →
        RCKK2 G₀ D J V r := by
  intro X _ _ n ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
  have hr1 : (r : X) ≠ 1 := by
    intro hr1
    apply hK1.2.1
    rw [← hr_eq, show r = 1 from Subtype.ext hr1, map_one]
  have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
  have hCore : CoreCommAt J V (r : X) :=
    rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
  have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
  intro e heD hene K hKcomp hJK hOddK
  have hcfg : RCKRP.RCKCompConfig .E6 n 1 ψ p G₀ A B₁ D J L K e :=
    ⟨hG0, hOddCent, hprime, hpne2, hA, hB1A, hDB1, hDcard, hAnorm, hMarkG,
      hB1norm, hB1cap, hB1card, hApow, hAcap, hAcapBot, hB1L, hMarkL,
      hCompJ, hOddCenJ, hLG0, hExists, hNotCent, hCompL, hNoA6,
      heD, hene, hKcomp, hJK, hOddK⟩
  exact k2At_of_e6_two_compConfig hcfg hJrow hFour hCore hShort

theorem rckRowK2AtField_III_one_of_remaining (h : RCKRowK2IIIAtTwoRemaining) :
    RCKRowK2AtField .III RCKPosShort 1 := by
  intro X _ _ t n ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
  by_cases htE6 : t = .E6
  · subst t
    exact rckRowK2AtField_III_one_E6 X n ψ p G₀ A B₁ D J L
      hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
      hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
      hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
  intro e heD hene K hKcomp hJK hOddK
  by_cases hKJ : K = J
  · subst K
    exact rck_K2_self hOddCenJ hrV hVJ hVab hVcard hK1'
  have hr1 : (r : X) ≠ 1 := by
    intro hr1
    apply hK1.2.1
    rw [← hr_eq, show r = 1 from Subtype.ext hr1, map_one]
  classical
  by_cases hSp : ∃ (m : ℕ) (η : ↥K ≃* CFSG.Open.StatedSp m (GaloisField 2 1)),
      3 ≤ m ∧ ∀ v ∈ (V.subgroupOf K).map η.toMonoidHom, v ≠ 1 →
        ∃ x y : Fin m ⊕ Fin m → GaloisField 2 1, spB m x y = 0 ∧ SpSiegel x y v
  · obtain ⟨m, η, hm, hpure⟩ := hSp
    exact k2At_of_pure_sp_model hm η (hJK r.2) hrV hr1 (hVJ.trans hJK) hVab hVcard hpure
  by_cases hOm : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 ∧ OmegaSixEmbed K J
  · have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
    have hCore : CoreCommAt J V (r : X) :=
      rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
    have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
    exact k2At_of_omegaSixEmbed_shortAt_psu_four hOddCenJ hOddK hFour hCore hOm.1 hShort hOm.2
  by_cases hBlock : FixedSpBlockAt K J
  · have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
    have hCore : CoreCommAt J V (r : X) :=
      rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
    have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
    exact k2At_of_fixedSpBlockAt hBlock hJK hFour hCore hShort hNoA6
  by_cases hSUBlock : FixedSUBlockAt K J
  · have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
    have hCore : CoreCommAt J V (r : X) :=
      rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
    have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
    exact k2At_of_fixedSUBlockAt hSUBlock hJK hFour hCore hShort
  by_cases hOrthBlock : FixedOrthBlockAt K J
  · have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
    have hCore : CoreCommAt J V (r : X) :=
      rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
    have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
    exact k2At_of_fixedOrthBlockAt hOrthBlock hJK hFour hCore hShort
  obtain ⟨hB1K, hJd⟩ := RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hprime hA hB1A hDB1 hDcard hAnorm hB1norm hCompJ heD hene hKcomp hJK
  by_cases hminus : RCKRP.RCKClassicalModelIDAt .POmegaMinus K B₁
  · obtain ⟨d, hdD, _, hJdK⟩ := hJd
    have hdB₁ : d ∈ B₁ := hDB1 hdD
    have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
    have hCore : CoreCommAt J V (r : X) :=
      rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
    have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
    have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤
        Nat.card B₁ := by
      rw [hB1cap, hDcard]
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card B₁ := hB1card
    exact k2At_of_row_III_of_minus_modelID hprime hpne2
      (CFSG.Open.IsElemAbelian.mono hA hB1A) hdB₁ hB1K hrank hminus hJdK hJrow
      hOddCenJ hOddK hJK hFour hCore hShort
  have hcfg : RCKRP.RCKCompConfig t n 1 ψ p G₀ A B₁ D J L K e :=
    ⟨hG0, hOddCent, hprime, hpne2, hA, hB1A, hDB1, hDcard, hAnorm, hMarkG,
      hB1norm, hB1cap, hB1card, hApow, hAcap, hAcapBot, hB1L, hMarkL,
      hCompJ, hOddCenJ, hLG0, hExists, hNotCent, hCompL, hNoA6,
      heD, hene, hKcomp, hJK, hOddK⟩
  by_cases hE8five : t = .E8 ∧ p = 5
  · rcases hE8five with ⟨rfl, rfl⟩
    have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
    have hCore : CoreCommAt J V (r : X) :=
      rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
    have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
    exact k2At_of_e8_five_compConfig hcfg hJrow hFour hCore hShort
  by_cases hE8seven : t = .E8 ∧ p = 7
  · rcases hE8seven with ⟨rfl, rfl⟩
    have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
    have hCore : CoreCommAt J V (r : X) :=
      rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
    have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
    exact k2At_of_e8_seven_compConfig hcfg hJrow hFour hCore hShort
  have hModel : RCKRP.RCKClassicalTag t → ∃ s : StatedLieTag,
      RCKRP.RCKClassicalTag s ∧ s ≠ .PSU ∧ s ≠ .PSL ∧ s ≠ .PSp ∧ s ≠ .POmegaMinus ∧
        RCKRP.RCKClassicalModelIDAt s K B₁ := by
    intro ht
    have hAll := RCKRP.rckCompModel_holds X t n 1 ψ p G₀ A B₁ D J L K e ht hcfg hKJ
    have hJdB : ∃ d ∈ B₁, IsComponentOf J (K ⊓ Subgroup.centralizer {d}) := by
      obtain ⟨d, hdD, -, hJd⟩ := hJd
      exact ⟨d, hDB1 hdD, hJd⟩
    obtain ⟨s, hs, hsU, hAt⟩ := exists_nonunitary_modelID_of_not_fixedSUBlockAt hprime hpne2
      (fun b hb => hA.2 b (hB1A hb)) hB1K hJdB hJrow hSUBlock hAll
    exact ⟨s, hs, hsU, ne_PSL_of_row_III_of_modelID hprime hpne2
      (fun b hb => hA.2 b (hB1A hb)) hB1K hJdB hJrow hAt,
      ne_PSp_of_row_III_of_modelID hprime hpne2 (fun b hb => hA.2 b (hB1A hb))
        hB1K hJdB hJrow hNoA6 hBlock hAt,
      fun hsM => hminus (hsM ▸ hAt), hAt⟩
  have hNoNativeSp : ¬ ∃ (m : ℕ) (φ : (ggU .PSp m 1).K →* X), φ.range = K ∧
      φ.ker ≤ Subgroup.center (ggU .PSp m 1).K ∧
      ∀ b ∈ B₁, GGPsiInnerDiag (ggU .PSp m 1).D φ b := by
    rintro ⟨m, φ, hφr, hφk, hφID⟩
    obtain ⟨d, hdD, _, hJcomp⟩ := hJd
    have hdB₁ : d ∈ B₁ := hDB1 hdD
    exact hBlock (fixedSpBlockAt_of_native_PSp_two_of_jRow_III hprime hpne2
      (hA.2 d (hB1A hdB₁)) φ hφr hφk (hB1K hdB₁) (hφID d hdB₁) hJcomp hJrow)
  have htF4 : t ≠ .F4 := by
    intro ht
    subst t
    exact hNoNativeSp ⟨3, rckF4_exists_native_PSp_three n ψ p G₀ A B₁ D J L K e hcfg⟩
  by_cases hNativePlus : RCKRP.RCKClassicalModelIDAt .POmegaPlus K B₁
  ·
    have hModelOriginal : RCKRP.RCKClassicalTag t → ∃ s : StatedLieTag,
        RCKRP.RCKClassicalTag s ∧ s ≠ .PSU ∧ s ≠ .PSL ∧
          RCKRP.RCKClassicalModelIDAt s K B₁ := by
      intro ht
      obtain ⟨s, hs, hsU, hsL, _, _, hAt⟩ := hModel ht
      exact ⟨s, hs, hsU, hsL, hAt⟩
    exact k2At_of_row_III_of_plus_modelID X t n ψ p G₀ A B₁ D J L
      hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
      hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
      hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
      e heD hene K hKcomp hJK hOddK hKJ
      (fun m η hm hpure => hSp ⟨m, η, hm, hpure⟩) (fun hJ hE => hOm ⟨hJ, hE⟩)
      hBlock hSUBlock hOrthBlock hB1K hJd hModelOriginal hNativePlus
  have hE8prime : t = .E8 → p = 3 := by
    intro ht
    subst t
    rcases prime_eq_three_or_five_or_seven_of_e8_two_compConfig hcfg with h3 | h5 | h7
    · exact h3
    · exact (hE8five ⟨rfl, h5⟩).elim
    · exact (hE8seven ⟨rfl, h7⟩).elim
  have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hr1, hConj⟩
  have hCore : CoreCommAt J V (r : X) :=
    rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
  have hShort : ShortAt J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
  by_cases htTw : t = .twistedE6
  · subst t
    exact k2At_of_twistedE6_compConfig hcfg hJrow hFour hCore hShort
  by_cases hK2 : K2At K V r
  · exact hK2
  have hTwE6 : ¬ GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
    intro hlab
    obtain ⟨d, hdD, -, hJd'⟩ := hJd
    have hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁ := by
      rw [hB1cap, hDcard, ← pow_add]
      exact hB1card
    exact hK2 (k2At_of_row_III_of_twistedE6_label hprime hpne2 (hA.mono hB1A) (hDB1 hdD) hB1K
      hrank hKcomp.2.2 hlab hJd' hJrow hOddCenJ hOddK hJK hFour hCore hShort)
  have htE8 : t ≠ .E8 := by
    rintro rfl
    obtain rfl := hE8prime rfl
    exact hTwE6 (((k2At_or_exceptional_of_e8_three_compConfig hcfg hJrow hFour hCore
      hShort).resolve_left hK2).resolve_right fun hlabel =>
        hK2 (k2At_of_e8_three_e7_label_compConfig hcfg hJrow hFour hCore hShort hlabel))
  have htE7 : t ≠ .E7 := by
    rintro rfl
    exact hTwE6 (((k2At_of_e7_two_compConfig hcfg hJrow hFour hCore hShort
      hSUBlock).resolve_left hK2).resolve_left hNativePlus)
  exact h X t n ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
    e heD hene K hKcomp hJK hOddK hKJ
    (fun m η hm hpure => hSp ⟨m, η, hm, hpure⟩) (fun hJ hE => hOm ⟨hJ, hE⟩)
    hBlock hSUBlock hOrthBlock hB1K hJd hModel hNoNativeSp htE6 htF4 htTw htE7 htE8 hNativePlus

theorem rckRowK2_III_of_field_two (h : RCKRowK2AtField .III RCKPosShort 1) :
    RCKRowK2 .III RCKPosShort := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
  obtain ⟨x, hxD, hx1, hLcomp⟩ := hExists
  have hf : f = 1 := ambient_field_eq_one_of_small_field_row hG0.2.2.2 (Or.inl hJrow) hprime hpne2 hA
    hB1A hDB1 hDcard hxD hx1 hAnorm hMarkG hB1L hMarkL hLcomp hNotCent hCompL
  subst f
  exact h X t n ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0
    ⟨x, hxD, hx1, hLcomp⟩ hNotCent hCompL hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard
    hr_eq hVmap hConj hK1'

end Certificates

end CFSG.StandardType.RCKC1
