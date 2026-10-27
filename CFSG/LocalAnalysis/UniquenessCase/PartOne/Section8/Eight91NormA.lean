module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Quot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.LieModelSimple
public import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL
public import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
public import CFSG.CGT.PushingUpLit.NineContent
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621Glue
public import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import Certificates.Certificate19762
public import Certificates.Certificate19763
public import Certificates.Certificate9530
public import Certificates.Certificate9681

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R72)

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (mem_centOverO2_iff)
open scoped commutatorElement

private theorem k891norma_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have h2 : 2 ≤ p := hp.two_le
  omega

private theorem k891norma_inf_centOverO2_eq_pCore {G : Type} [Group G] [Finite G]
    {D : Data G} {L : Subgroup G} (hL : L ≤ D.M) (hZ : center (Bar2 L) = ⊥) :
    L ⊓ F08.CentOverO2 D.M L = pCoreOf 2 L := by
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) ?_)
  · rintro x ⟨hxL, hxC⟩
    have hxcent : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
        have hcoe : (((l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) : ↥L) : G) = (x * l * x⁻¹ * l⁻¹)⁻¹ := by
          simp [div_eq_mul_inv, mul_assoc]
        have hG : (((l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) : ↥L) : G) ∈ pCoreOf 2 L := by
          rw [hcoe]
          exact (pCoreOf 2 L).inv_mem ((mem_centOverO2_iff.mp hxC).2 l l.2)
        obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp hG
        have hp_eq : p = (l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) := L.subtype_injective hpeq
        rwa [← hp_eq]
    rw [hZ] at hxcent
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hxcent)
    exact Subgroup.mem_map_of_mem (f := L.subtype) (K := CFSG.pCore 2 ↥L) h1
  · intro x hx
    rw [mem_centOverO2_iff]
    refine ⟨hL (CFSG.LieType.BorelTits.pCoreOf_le 2 L hx), ?_⟩
    intro l hl
    have h1 : l * x * l⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) x).1 hx
    have h2 : l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L :=
      (pCoreOf 2 L).mul_mem h1 ((pCoreOf 2 L).inv_mem hx)
    have h3 : x * l * x⁻¹ * l⁻¹ = (l * x * l⁻¹ * x⁻¹)⁻¹ := by group
    rw [h3]
    exact (pCoreOf 2 L).inv_mem h2

private theorem k891norma_le_pRank_two_of_comm {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {H P Q : Subgroup G}
    (hPH : P ≤ H) (hQH : Q ≤ H) (hP : Nat.card P = p) (hQ : Nat.card Q = p)
    (hPab : ∀ a b : ↥P, a * b = b * a) (hQab : ∀ a b : ↥Q, a * b = b * a)
    (hPp : ∀ x ∈ P, x ^ p = 1) (hQp : ∀ x ∈ Q, x ^ p = 1)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hdis : ∀ x ∈ P, x ∈ Q → x = 1) :
    2 ≤ CFSG.Open.pRank p H := by
  classical
  let f : ↥P →* G := P.subtype
  let g : ↥Q →* G := Q.subtype
  have hcomm' : ∀ (m : ↥P) (n : ↥Q), Commute (f m) (g n) := fun m n => hc m m.2 n n.2
  have hdisj : Disjoint P Q := by
    rw [Subgroup.disjoint_def]
    exact fun {x} hx hy => hdis x hx hy
  have hinj : Function.Injective (MonoidHom.noncommCoprod f g hcomm') := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨P.subtype_injective, Q.subtype_injective, by simpa [f, g] using hdisj⟩
  have hrange : (MonoidHom.noncommCoprod f g hcomm').range = P ⊔ Q := by
    rw [MonoidHom.noncommCoprod_range]
    simp [f, g]
  have hcomm : ∀ a b : ↥P × ↥Q, a * b = b * a := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact Prod.ext (hPab a₁ b₁) (hQab a₂ b₂)
  have hpow : ∀ a : ↥P × ↥Q, a ^ p = 1 := by
    rintro ⟨x, y⟩
    exact Prod.ext (Subtype.ext (hPp x x.2)) (Subtype.ext (hQp y y.2))
  have hcard : Nat.card (↥P × ↥Q) = p ^ 2 := by
    rw [Nat.card_prod, hP, hQ, pow_two]
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hcard
    (MonoidHom.noncommCoprod f g hcomm') hinj (by rw [hrange]; exact sup_le hPH hQH)

private theorem k891norma_dvd_card_bar2_J {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (hPrime : R891PrimeCore) (L S R A : Subgroup G) (n : ℕ)
    (hset : R891Set D L S n) (hctx : R891Ctx D L S n R A) (hrank : R891Rank893 D L) :
    ∀ p ∈ D.sig,
      p ∣ Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) := by
  intro p hpσ
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hset.mem
  have hp3 : p ≠ 3 := by
    intro h
    exact hset.notStrong (h ▸ (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hpσ))
  have hp5 : 5 ≤ p := k891norma_five_le hp hp2 hp3
  have : Fact p.Prime := ⟨hp⟩
  have hpCore : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p)
      (CFSG.pCore_isPGroup (G := ↥L) (p := 2)) hp hp2
  have hbar : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) = 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (p := p) (CFSG.pCore 2 ↥L) hpCore,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact (hrank p hpσ).1
  have h6 : p ∣ 2 ^ (6 * n) - 1 :=
    ((hPrime.1 (Bar2 L) n hset.d4).2 p hp hp5).2.1.mp hbar
  let J : Subgroup G := F08.DerInf8 (L ⊓ centralizer (A : Set G))
  have hLie : LieModel (Bar2 J) .PSL 2 2 (3 * n) := hctx.x1Shape.1
  have hexp : 2 ^ (2 * (3 * n)) - 1 = 2 ^ (6 * n) - 1 := by
    rw [show 2 * (3 * n) = 6 * n by ring]
  exact ((hPrime.2.2 (Bar2 J) (3 * n) hLie p hp hp2).2).mpr (hexp ▸ h6)

private theorem k891norma_dvd_card_J {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (hPrime : R891PrimeCore) (L S R A : Subgroup G) (n : ℕ)
    (hset : R891Set D L S n) (hctx : R891Ctx D L S n R A) (hrank : R891Rank893 D L) :
    ∀ p ∈ D.sig, p ∣ Nat.card (F08.DerInf8 (L ⊓ centralizer (A : Set G))) :=
  fun p hpσ => (k891norma_dvd_card_bar2_J D hSg hPrime L S R A n hset hctx hrank p hpσ).trans
    (Subgroup.card_quotient_dvd_card (s := CFSG.pCore 2 ↥(F08.DerInf8
      (L ⊓ centralizer (A : Set G)))))

private theorem k891norma_isPerfect_derInf8 {G : Type} [Group G] [Finite G]
    (X : Subgroup G) : ⁅F08.DerInf8 X, F08.DerInf8 X⁆ = F08.DerInf8 X := by
  have hperf : Group.IsPerfect ↥((⨅ n : ℕ, derivedSeries ↥X n) : Subgroup ↥X) :=
    CFSG.perfect_residual_characterization.2.2.1
  have : Group.IsPerfect ↥((⨅ n : ℕ, derivedSeries ↥X n) : Subgroup ↥X) := hperf
  have hmap : Group.IsPerfect ↥((⨅ n : ℕ, derivedSeries ↥X n).map X.subtype) :=
    Group.IsPerfect.map X.subtype
  rw [F08.DerInf8]
  exact Subgroup.isPerfect_iff.mp hmap

private theorem k891norma_mem_sup_of_le_normalizer {G : Type} [Group G] {s t : Subgroup G}
    (h : s ≤ normalizer (t : Set G)) {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, x, hx, by simp⟩
    · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, s.mul_mem hy₁ hy₂, (y₂⁻¹ * z₁ * y₂) * z₂, ?_, by simp [mul_assoc]⟩
      refine t.mul_mem ?_ hz₂
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem (normalizer (t : Set G)) (h hy₂)) z₁).mp hz₁
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨y⁻¹, s.inv_mem hy, y * z⁻¹ * y⁻¹,
        (Subgroup.mem_normalizer_iff.mp (h hy) z⁻¹).mp (t.inv_mem hz), by simp [mul_assoc]⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

private theorem k891norma_two_le_pRank_centralizer {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (hPrime : R891PrimeCore) (L S R A : Subgroup G) (n : ℕ)
    (hset : R891Set D L S n) (hbasic : R891Basic D L S) (hctx : R891Ctx D L S n R A)
    (hrank : R891Rank893 D L) :
    ∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (A : Set G)) := by
  intro p hpσ
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have : Fact p.Prime := ⟨hp⟩
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hset.mem
  have hp3 : p ≠ 3 := by
    intro h
    exact hset.notStrong (h ▸ (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hpσ))
  have hp5 : 5 ≤ p := k891norma_five_le hp hp2 hp3
  have hLM : L ≤ D.M := hset.mem.1.le
  have hAM : A ≤ L := hctx.classes.aLe
  have hcardA : Nat.card A = 3 := hctx.classes.aOrder
  have hZ : center (Bar2 L) = ⊥ := hbasic.centerBot
  obtain ⟨U, hUle, hUea, hUcard0⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (F08.CentOverO2 D.M L)
  have hUcard : Nat.card U = p := by rw [hUcard0, (hrank p hpσ).2, pow_one]
  have hUpg : IsPGroup p U := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hUcard)
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hcardA)
  have hCenM : F08.CentOverO2 D.M L ≤ D.M := fun x hx => (mem_centOverO2_iff.mp hx).1
  have hUN : U ≤ normalizer (pCoreOf 2 L : Set G) :=
    (hUle.trans hCenM).trans (hbasic.normal.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hEN : A ≤ normalizer (pCoreOf 2 L : Set G) :=
    hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hO2pg : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hcomm1 : ∀ e ∈ A, ∀ a ∈ U, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 L := by
    intro e he a ha
    have h1 : a * e * a⁻¹ * e⁻¹ ∈ pCoreOf 2 L :=
      (mem_centOverO2_iff.mp (hUle ha)).2 e (hAM he)
    have h2 : e * a * e⁻¹ * a⁻¹ = (a * e * a⁻¹ * e⁻¹)⁻¹ := by group
    rw [h2]
    exact (pCoreOf 2 L).inv_mem h1
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_centralizing_copy
      (ℓ := 3) (p := p) Nat.prime_three (by norm_num) hp hp2 (pCoreOf 2 L) U A
      hO2pg hUN hEN hUpg hA3 hcomm1
  have hA'card : Nat.card A' = p := by rw [Nat.card_congr eA.toEquiv, hUcard]
  have hA'pg : IsPGroup p A' := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA'card)
  have hA'ab : ∀ a b : ↥A', a * b = b * a := by
    intro a b
    apply eA.injective
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff.mp hUea.1) (eA a) (eA b)
  have hO2cen : pCoreOf 2 L ≤ F08.CentOverO2 D.M L := by
    intro o ho
    rw [mem_centOverO2_iff]
    refine ⟨hLM (CFSG.LieType.BorelTits.pCoreOf_le 2 L ho), fun l hl => ?_⟩
    have h1 : l * o * l⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) o).1 ho
    have h2 : l * o * l⁻¹ * o⁻¹ ∈ pCoreOf 2 L :=
      (pCoreOf 2 L).mul_mem h1 ((pCoreOf 2 L).inv_mem ho)
    have h3 : o * l * o⁻¹ * l⁻¹ = (l * o * l⁻¹ * o⁻¹)⁻¹ := by group
    rw [h3]
    exact (pCoreOf 2 L).inv_mem h2
  have hpcore_cop : ¬ p ∣ Nat.card (pCoreOf 2 L) := by
    rw [show pCoreOf 2 L = (CFSG.pCore 2 ↥L).map L.subtype from rfl,
      Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p)
      (CFSG.pCore_isPGroup (G := ↥L) (p := 2)) hp hp2
  let J : Subgroup G := F08.DerInf8 (L ⊓ centralizer (A : Set G))
  have hdvdJ : p ∣ Nat.card J := k891norma_dvd_card_J D hSg hPrime L S R A n hset hctx hrank p hpσ
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) p hdvdJ
  have hyJ : (y : G) ∈ J := y.2
  have hyordG : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe, hyord]
  have hyX : (y : G) ∈ L ⊓ centralizer (A : Set G) := (Subgroup.map_subtype_le _) hyJ
  have hyL : (y : G) ∈ L := hyX.1
  have hyC : (y : G) ∈ centralizer (A : Set G) := hyX.2
  have hPcard : Nat.card (Subgroup.zpowers (y : G)) = p := by
    rw [Nat.card_zpowers, hyordG]
  have hPpg : IsPGroup p (Subgroup.zpowers (y : G)) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hPcard)
  have hPp : ∀ x ∈ Subgroup.zpowers (y : G), x ^ p = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ p := by
      rw [← hPcard]
      exact Subgroup.orderOf_dvd_natCard _ hx
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hA'N : A' ≤ normalizer ((pCoreOf 2 L ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact hA'le.trans (sup_le hUN (pCoreOf 2 L).le_normalizer)
    · exact hA'C.trans (centralizer (A : Set G)).le_normalizer
  have hyN : Subgroup.zpowers (y : G) ≤
      normalizer ((pCoreOf 2 L ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hyL)
    · exact Subgroup.zpowers_le.mpr ((centralizer (A : Set G)).le_normalizer hyC)
  have hcomm2 : ∀ e ∈ Subgroup.zpowers (y : G), ∀ a ∈ A',
      e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 L ⊓ centralizer (A : Set G) := by
    intro e he a ha
    have heL : e ∈ L := (Subgroup.zpowers_le.mpr hyL) he
    have heC : e ∈ centralizer (A : Set G) := (Subgroup.zpowers_le.mpr hyC) he
    refine ⟨?_, ?_⟩
    · obtain ⟨u, huU, o, hoO, huo⟩ := (k891norma_mem_sup_of_le_normalizer hUN).mp (hA'le ha)
      have hoOe : e * o * e⁻¹ ∈ pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L heL) o).1 hoO
      have hoO' : o * e * o⁻¹ * e⁻¹ ∈ pCoreOf 2 L := by
        have h2 : e * o * e⁻¹ * o⁻¹ ∈ pCoreOf 2 L :=
          (pCoreOf 2 L).mul_mem hoOe ((pCoreOf 2 L).inv_mem hoO)
        have h3 : o * e * o⁻¹ * e⁻¹ = (e * o * e⁻¹ * o⁻¹)⁻¹ := by group
        rw [h3]
        exact (pCoreOf 2 L).inv_mem h2
      have hmemO : a * e * a⁻¹ * e⁻¹ ∈ pCoreOf 2 L := by
        rw [← huo]
        change ⁅u * o, e⁆ ∈ pCoreOf 2 L
        rw [commutatorElement_mul_left_eq_conj_mul u o e]
        refine (pCoreOf 2 L).mul_mem ?_ ((mem_centOverO2_iff.mp (hUle huU)).2 e heL)
        exact (Subgroup.mem_normalizer_iff.mp (hUN huU) (o * e * o⁻¹ * e⁻¹)).mp hoO'
      have h2 : e * a * e⁻¹ * a⁻¹ = (a * e * a⁻¹ * e⁻¹)⁻¹ := by group
      rw [h2]
      exact (pCoreOf 2 L).inv_mem hmemO
    · exact (centralizer (A : Set G)).mul_mem
        ((centralizer (A : Set G)).mul_mem
          ((centralizer (A : Set G)).mul_mem heC (hA'C ha))
          ((centralizer (A : Set G)).inv_mem heC))
        ((centralizer (A : Set G)).inv_mem (hA'C ha))
  have hO2pg' : IsPGroup 2 ↥(pCoreOf 2 L ⊓ centralizer (A : Set G)) :=
    IsPGroup.to_inf_left hO2pg
  obtain ⟨B', hB'C, hB'le, ⟨eB⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_centralizing_copy
      (ℓ := p) (p := p) hp hp2 hp hp2 (pCoreOf 2 L ⊓ centralizer (A : Set G)) A'
      (Subgroup.zpowers (y : G)) hO2pg' hA'N hyN hA'pg hPpg hcomm2
  have hB'card : Nat.card B' = p := by rw [Nat.card_congr eB.toEquiv, hA'card]
  have hB'pg : IsPGroup p B' := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hB'card)
  have hB'ab : ∀ a b : ↥B', a * b = b * a := by
    intro a b
    apply eB.injective
    rw [map_mul, map_mul]
    exact hA'ab (eB a) (eB b)
  have hB'p : ∀ x ∈ B', x ^ p = 1 := by
    intro x hx
    have hdvd : orderOf x ∣ p := by
      rw [← hB'card]
      exact Subgroup.orderOf_dvd_natCard _ hx
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hPB' : Subgroup.zpowers (y : G) ≠ B' := by
    intro hEq
    have hyB' : (y : G) ∈ B' := hEq ▸ Subgroup.mem_zpowers (y : G)
    have hB'leUO : B' ≤ U ⊔ pCoreOf 2 L := hB'le.trans (sup_le hA'le (inf_le_left.trans le_sup_right))
    have hyUO : (y : G) ∈ U ⊔ pCoreOf 2 L := hB'leUO hyB'
    have hyCen : (y : G) ∈ F08.CentOverO2 D.M L := (sup_le hUle hO2cen) hyUO
    have hypc : (y : G) ∈ pCoreOf 2 L := by
      have hEq2 := k891norma_inf_centOverO2_eq_pCore hLM hZ
      have hmem : (y : G) ∈ L ⊓ F08.CentOverO2 D.M L := ⟨hyL, hyCen⟩
      rwa [hEq2] at hmem
    have hdvdpc : p ∣ Nat.card (pCoreOf 2 L) := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hypc)
    exact hpcore_cop hdvdpc
  have hdis : ∀ x ∈ Subgroup.zpowers (y : G), x ∈ B' → x = 1 := by
    intro x hxP hxQ
    by_contra hxne
    have hxord : orderOf x = p := by
      have hdvd : orderOf x ∣ p := by
        rw [← hPcard]
        exact Subgroup.orderOf_dvd_natCard _ hxP
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpe
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne
      · exact hpe
    apply hPB'
    have hPx : Subgroup.zpowers x = Subgroup.zpowers (y : G) := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hyordG]
    rw [← hPx]
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxQ) ?_
    rw [Nat.card_zpowers, hxord, hB'card]
  have hPab : ∀ a b : ↥(Subgroup.zpowers (y : G)), a * b = b * a :=
    fun a b => mul_comm' a b
  have hB'M : B' ≤ D.M :=
    hB'le.trans (sup_le (hA'le.trans (sup_le (hUle.trans hCenM)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)))
      (inf_le_left.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)))
  have hB'CA : B' ≤ centralizer (A : Set G) :=
    hB'le.trans (sup_le hA'C inf_le_right)
  have hB'CM : B' ≤ D.M ⊓ centralizer (A : Set G) := le_inf hB'M hB'CA
  have hPH : Subgroup.zpowers (y : G) ≤ D.M ⊓ centralizer (A : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hLM hyL, hyC⟩
  have hcommPB : ∀ x ∈ Subgroup.zpowers (y : G), ∀ z ∈ B', x * z = z * x := by
    intro x hx z hz
    exact Subgroup.mem_centralizer_iff.mp (hB'C hz) x hx
  exact k891norma_le_pRank_two_of_comm hp hPH hB'CM hPcard hB'card hPab hB'ab hPp hB'p hcommPB hdis

private theorem k891norma_normalizer_le {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (h72 : R72 D) (hKF7 : KStrongEmbedded72) (hPrime : R891PrimeCore)
    (L S R A : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hctx : R891Ctx D L S n R A) (hrank : R891Rank893 D L) :
    normalizer (A : Set G) ≤ D.M := by
  by_contra hNM
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup G := D.standing.simple
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hset.mem
  have hsp : IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hpσ
  have hLM : L ≤ D.M := hset.mem.1.le
  have hcardA : Nat.card A = 3 := hctx.classes.aOrder
  have hA_ne_bot : A ≠ ⊥ := by
    intro h
    have h1 : Nat.card A = 1 := by rw [h, Subgroup.card_bot]
    omega
  have hA_ne_top : A ≠ ⊤ := by
    intro h
    have hcardG : Nat.card G = 3 := by rw [← hcardA, h, Subgroup.card_top]
    obtain ⟨a, b, hab⟩ := D.standing.nonab
    have : IsCyclic G := isCyclic_of_card_dvd_prime (p := 3) (by rw [hcardG])
    exact hab (mul_comm a b)
  have hHne : normalizer (A : Set G) ≠ ⊤ := by
    intro htop
    have : A.Normal := normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with hbot | htop'
    · exact hA_ne_bot hbot
    · exact hA_ne_top htop'
  have hrankC : 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (A : Set G)) :=
    k891norma_two_le_pRank_centralizer D hSg hPrime L S R A n hset hbasic hctx hrank p hpσ
  have hrankH : 1 < CFSG.Open.pRank p (normalizer (A : Set G) ⊓ D.M) := by
    have hle : D.M ⊓ centralizer (A : Set G) ≤ normalizer (A : Set G) ⊓ D.M :=
      le_inf (inf_le_right.trans (Subgroup.centralizer_le_normalizer (A : Set G))) inf_le_left
    have hmono := CFSG.SectionRank.pRank_mono hp.one_lt hle
    omega
  have hsec : F07.Sec7Hyp D p (normalizer (A : Set G)) :=
    ⟨hp, hp2, hsp, hHne, hNM, hrankH⟩
  let J : Subgroup G := F08.DerInf8 (L ⊓ centralizer (A : Set G))
  have hJleX : J ≤ L ⊓ centralizer (A : Set G) := Subgroup.map_subtype_le _
  have hJperf : ⁅J, J⁆ = J := k891norma_isPerfect_derInf8 (L ⊓ centralizer (A : Set G))
  have hJN : J ≤ normalizer (A : Set G) ⊓ D.M :=
    le_inf (hJleX.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer (A : Set G))))
      (hJleX.trans (inf_le_left.trans hLM))
  rcases solvable_or_altTen_of_sec7Hyp h72 hKF7 hsec with hsol | ⟨hp5, hNorm, hF, hAlt, hA5all⟩
  · have hJcore : J ≤ F07.PPrimeCoreIn p (normalizer (A : Set G)) :=
      le_pPrimeCoreIn_of_isSolvable inf_le_left hJN hJperf hsol
    have hcop : ¬ p ∣ Nat.card (F07.PPrimeCoreIn p (normalizer (A : Set G))) := by
      rw [show F07.PPrimeCoreIn p (normalizer (A : Set G)) =
          (CFSG.pPrimeCore p ↥(normalizer (A : Set G))).map (normalizer (A : Set G)).subtype
          from rfl,
        Subgroup.card_map_of_injective (normalizer (A : Set G)).subtype_injective]
      exact hp.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card
    have hdvdJ := k891norma_dvd_card_J D hSg hPrime L S R A n hset hctx hrank p hpσ
    exact hcop (hdvdJ.trans (Subgroup.card_dvd_of_le hJcore))
  · have hLie : LieModel (Bar2 J) .PSL 2 2 (3 * n) := hctx.x1Shape.1
    have hsimp : IsSimpleGroup (Bar2 J) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLie
    have hJbar : p ∣ Nat.card (Bar2 J) :=
      k891norma_dvd_card_bar2_J D hSg hPrime L S R A n hset hctx hrank p hpσ
    obtain ⟨e⟩ := isAlt_five_bar2_of_perfect hp inf_le_left hJN hJperf hsimp hJbar hA5all
    have hcard : Nat.card (Bar2 J) = 2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1) :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
        (hLie.statedClassicalModel (by decide))
    have h60 : Nat.card (Bar2 J) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num
    have hn1 : 1 ≤ n := hset.d4.admissible.2.1
    have hge : 60 < Nat.card (Bar2 J) := by
      rw [hcard]
      have hq : 8 ≤ 2 ^ (3 * n) := by
        have h3n : 3 ≤ 3 * n := by omega
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) h3n
      have hq2 : 63 ≤ (2 ^ (3 * n)) ^ 2 - 1 := by
        rw [pow_two]
        have := Nat.mul_le_mul hq hq
        omega
      have h504 : 504 ≤ 2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1) := by
        calc 504 = 8 * 63 := by norm_num
          _ ≤ 2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1) := Nat.mul_le_mul hq hq2
      omega
    omega

theorem s891_norm_a
    {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (h72 : R72 D) (hPrime : R891PrimeCore)
    (L S R A : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hctx : R891Ctx D L S n R A) (hrank : R891Rank893 D L) :
    R891NormA D A := by
  have hKF7 := kStrongEmbedded72_holds
  refine ⟨k891norma_normalizer_le D hSg h72 hKF7 hPrime L S R A n hset hbasic hctx hrank, ?_⟩
  intro p hpσ
  exact lt_of_lt_of_le (by norm_num) (k891norma_two_le_pRank_centralizer D hSg hPrime L S R A n
    hset hbasic hctx hrank p hpσ)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
