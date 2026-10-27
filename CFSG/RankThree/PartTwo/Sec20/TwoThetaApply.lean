module

public import CFSG.RankThree.PartTwo.Sec20.TwoThetaStatement
public import CFSG.RankThree.PartTwo.Sec20.TwoThetaNormalizer
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

section Apply

variable {G : Type} [Group G] [Finite G]

theorem TwoTheta.theta_hyps (hG : TheoremFourHyp G) (h3G : 3 ∣ Nat.card G) {F Θ : Subgroup G}
    (hF2 : IsPGroup 2 F) (hF1 : F ≠ ⊥) (hΘF : Θ ≤ Subgroup.normalizer (F : Set G))
    (hΘ3 : Nat.Coprime 3 (Nat.card Θ)) :
    CFSG.IsKGroup ↥Θ ∧ ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p Θ ≤ 2 := by
  constructor
  · have hΘtop : Θ ≠ ⊤ := by
      intro htop
      rw [htop, Subgroup.card_top] at hΘ3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hΘ3 h3G
    exact (hG.sectionFourHyp hΘtop).kGroup
  · intro p hp hp5
    have hM : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (F : Set G)) := ⟨F, hF1, hF2, rfl⟩
    have h1 := CFSG.RankThree.PartTwo.Sec18.pRank_le_localRank_of_isTwoLocal hp hM
    have h2 : CFSG.Open.pRank p Θ ≤ CFSG.Open.pRank p (Subgroup.normalizer (F : Set G)) :=
      CFSG.SectionRank.pRank_mono hp.one_lt hΘF
    have h3 := hG.localRank_lt p hp (by omega)
    omega

theorem TwoTheta.y_le_normalizer (hKF : KF207ThetaTwo) (hG : TheoremFourHyp G)
    (h3G : 3 ∣ Nat.card G) {F L Y : Subgroup G} (hF2 : IsPGroup 2 F) (hF1 : F ≠ ⊥)
    (hYF : Y ≤ Subgroup.normalizer (F : Set G)) (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hLL : ⁅L, L⁆ = L) (hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)))
    (h1 : ⁅L, Y⁆ ≤ inSubgroup (CFSG.pPrimeCore 3) Y)
    (h3 : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (L : Set G)) :
    Y ≤ Subgroup.normalizer (L : Set G) := by
  set Θ := inSubgroup (CFSG.pPrimeCore 3) Y with hΘ
  have hΘY : Θ ≤ Y := Subgroup.map_subtype_le _
  have hnorm : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (Θ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pPrimeCore 3 ↥Y)
  have hLΘ : L ≤ Subgroup.normalizer (Θ : Set G) := hLY.trans hnorm
  have h3Θ : Nat.Coprime 3 (Nat.card Θ) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y)
    rwa [← Subgroup.card_map_of_injective Y.subtype_injective] at h
  obtain ⟨hK, hrank⟩ := TwoTheta.theta_hyps hG h3G hF2 hF1 (hΘY.trans hYF) h3Θ
  have h2 := hKF G Θ L hK h3Θ hrank hLΘ hLL hq
  exact le_normalizer_of_comm_theta L Y hLY hLL hq h1 h2 h3


theorem TwoTheta.le_of_struct {K N C I R : Subgroup G} {g : G}
    (hK : K ≤ (Late.normalClosureIn (K ⊓ C) g ⊔ I) ⊔ R) (hY : Late.normalClosureIn C g ≤ N)
    (hI : I ≤ N) (hR : R ≤ N) : K ≤ N := by
  refine hK.trans (sup_le (sup_le ?_ hI) hR)
  refine le_trans ?_ hY
  exact Subgroup.closure_mono (fun x ⟨m, hm, hx⟩ => ⟨m, hm.2, hx⟩)

end Apply

end CFSG.RankThree.PartTwo.Sec20
