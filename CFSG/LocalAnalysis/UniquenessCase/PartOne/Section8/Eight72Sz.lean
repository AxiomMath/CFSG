module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Single
public import CFSG.Quasithin.Background.F1Models
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2 calC IsSz)
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3 (KFactSuzukiThreeFree)
open CFSG.Blueprint (SuzukiModel)

theorem center_eq_bot_and_suzukiModel_of_kFactSuzuki (hSz : KFactSuzukiThreeFree)
    {K : Type} [Group K] [Finite K] (hKq : CFSG.Open.IsQuasisimple K)
    (hKK : CFSG.Open.IsKGroup K) (hZ : Odd (Nat.card (center K))) (h3 : ¬ 3 ∣ Nat.card K) :
    center K = ⊥ ∧ ∃ f : ℕ, SuzukiModel K 2 f := by
  have hKq' : CFSG.IsQuasisimple K := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKq
  have : Group.IsPerfect K := hKq'.1
  have : IsSimpleGroup (K ⧸ center K) := hKq'.2.1
  obtain ⟨x, y, hxy⟩ := hKq'.2.2
  have hnab : ¬ (∀ a b : K ⧸ center K, a * b = b * a) := fun h => hxy (h x y)
  obtain ⟨f, -, a, ha, F, _, _, rfl, hF, ⟨φ⟩⟩ :=
    hSz (K ⧸ center K) hKq'.2.1 hnab (hKK.quotient (center K))
      (fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card (center K))))
  let φ' := φ.trans
    (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hF)
  let π := φ'.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : π.ker = center K := CFSG.SectionRank.center_eq_ker_of_mulEquiv φ'
  have hbot := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) π
    (φ'.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (hker ▸ hZ)
  rw [hker] at hbot
  exact ⟨hbot, 2 * a + 1, rfl, a, ha, F, inferInstance, inferInstance, rfl, hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans φ⟩⟩

theorem eight72_isSz_of_suzukiModel {X : Type} [Group X] {f : ℕ} (h : SuzukiModel X 2 f) :
    IsSz X f :=
  CFSG.Blueprint.LieModel.twistedB2_iff.2 ⟨rfl, h⟩

theorem eight72_five_dvd_of_suzukiModel {X : Type} [Group X]
    {f : ℕ} (h : SuzukiModel X 2 f) : 5 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 4 * a + 2 by ring, pow_add, pow_mul]
    norm_num
    ring
  rw [h4]
  have h16 : 16 ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem eight72_sylow_isCyclic_of_suzukiModel {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : SuzukiModel X 2 f) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (S : Sylow r X) :
    IsCyclic (S : Subgroup X) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  let e' : X ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
  let S' : Sylow r (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    Sylow.mapSurjective (f := e'.toMonoidHom) e'.surjective S
  have hS' : IsCyclic (S' : Subgroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a)) :=
    CFSG.SectionRank.suzuki_sylow_isCyclic a (by omega) hr2 S'
  have hcoe : (S' : Subgroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a)) =
      (S : Subgroup X).map e'.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e'.toMonoidHom) e'.surjective S
  rw [hcoe] at hS'
  exact (e'.subgroupMap (S : Subgroup X)).isCyclic.mpr hS'

theorem eight72_card_le_of_isElemAbelian {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : SuzukiModel X 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : Subgroup X)
    (hQ : IsElemAbelian p Q) : Nat.card Q ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hQ).exists_card_eq
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_le_one_of_isL2_or_isSz
      (Or.inr (eight72_isSz_of_suzukiModel h)) hp hp2
  have hk1 : k ≤ 1 :=
    (CFSG.SectionRank.le_pRank hp.one_lt (le_top : Q ≤ ⊤) hQ hk).trans hrank
  calc Nat.card Q = p ^ k := hk
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

variable {G : Type} [Group G] [Finite G]

theorem eight72_center_eq_bot_and_suzukiModel (hSz : KFactSuzukiThreeFree)
    (hKP : CFSG.Open.IsKProper G) {M K : Subgroup G} (hK : K ∈ calC M) (hKtop : K ≠ ⊤)
    (h3 : ¬ 3 ∣ Nat.card K) :
    center (Bar2 K) = ⊥ ∧ ∃ f : ℕ, SuzukiModel (Bar2 K) 2 f := by
  have hodd := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥K
  have h3' : ¬ 3 ∣ Nat.card (Bar2 K) := fun h =>
    h3 (h.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K)))
  exact center_eq_bot_and_suzukiModel_of_kFactSuzuki hSz hK.2.2
    ((hKP.isKGroup K hKtop).quotient (CFSG.pCore 2 ↥K)) hodd h3'

theorem eight72_pRank_le_one_of_suzukiModel {K : Subgroup G} {f : ℕ}
    (h : SuzukiModel (Bar2 K) 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q K ≤ 1 := by
  have htop : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K)) ≤ 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_le_one_of_isL2_or_isSz
      (Or.inr (eight72_isSz_of_suzukiModel h)) hq hq2
  rwa [CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd (Y := K) hq hq2] at htop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
