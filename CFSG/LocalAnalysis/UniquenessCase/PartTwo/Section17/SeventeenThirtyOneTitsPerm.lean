module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ImageOTwoQuotNormalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PermutableOrderThree
public import CFSG.GroupTheory.BarImageConj
public import CFSG.LocalAnalysis.RankThreeUC.Section12.IntermediateSylow.IntermediateSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalParabolicsGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaPrimePullback
public import CFSG.GroupTheory.PermutesConjSupElemAbelian
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Two
public import CFSG.Quasithin.Vol2.Ch10SecB6Bar
public import CFSG.Quasithin.H13.L32NLem1444d
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.GroupTheory
open CFSG.LocalAnalysis.RankThreeUC.Section12.IntermediateSylow
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem map_pCoreQuotMulAut_sylow_of_mem_normalizer {D : Data G} {L : Subgroup G}
    {t : G} (ht : t ∈ D.T) (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    (UC22.barImage L (D.T ⊓ L)).map
        (CFSG.pCoreQuotMulAut ↥L
          (Subgroup.normalizerMonoidHom L ⟨t, htL⟩)).toMonoidHom =
      UC22.barImage L (D.T ⊓ L) := by
  have h1 : D.T.map (MulAut.conj t).toMonoidHom = D.T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  have h2 : L.map (MulAut.conj t).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
  rw [S18.barImage_map_pCoreQuotMulAut _ inf_le_right,
    Subgroup.map_inf_eq _ _ (MulAut.conj t).toMonoidHom (MulAut.conj t).injective, h1, h2]

theorem map_pCoreQuotMulAut_sylow {D : Data G} {L : Subgroup G}
    (hMN : D.M ≤ Subgroup.normalizer (L : Set G)) (t : G) (ht : t ∈ D.T) :
    (UC22.barImage L (D.T ⊓ L)).map
        (CFSG.pCoreQuotMulAut ↥L
          (Subgroup.normalizerMonoidHom L ⟨t, hMN (D.sylowM.le ht)⟩)).toMonoidHom =
      UC22.barImage L (D.T ⊓ L) :=
  map_pCoreQuotMulAut_sylow_of_mem_normalizer ht (hMN (D.sylowM.le ht))

theorem exists_tits_parabolic {D : Data G} {K : Subgroup G}
    (hTi : Inputs1719.K_TitsParabolicGen) (hK : K ∈ calC D.M)
    (hTits : LieModel (Bar2 K) .Tits 0 2 1) :
    ∃ P : Subgroup G, D.T ⊓ K ≤ P ∧ P ≤ K ∧ Nat.card ↥P = 3 * Nat.card ↥(D.T ⊓ K) ∧
      ∀ t ∈ D.T, K.map (MulAut.conj t).toMonoidHom = K →
        P.map (MulAut.conj t).toMonoidHom = P := by
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hK.1
  have hsubK : (K.subgroupOf D.M).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hKM).mp hK.1
  have hTM : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM
  have hSylK : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTM hKM hsubK
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (UC22.barImage K (D.T ⊓ K)) ⊤ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.isSylowTwoOf_modO2Image hSylK
  obtain ⟨P₁, P₂, hSle, -, hcard, -, -, hinv⟩ :=
    hTi (Bar2 K) hTits (UC22.barImage K (D.T ⊓ K)) hS
  refine ⟨UC22.barPreimage K P₁, ?_, UC22.uc22p21c_barPreimage_le K P₁, ?_, ?_⟩
  · intro x hx
    rw [UC22.uc22p21c_mem_barPreimage]
    exact ⟨hx.2, hSle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))⟩
  · rw [UC22.uc22p22u_card_barPreimage, hcard]
    have hScard :=
      CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul K (D.T ⊓ K) inf_le_right
    have hO2le : CFSG.Open.pCoreOf 2 K ≤ D.T ⊓ K := by
      have h := CFSG.Quasithin.pCore_two_le_subgroupOf hSylK
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      exact hyx ▸ Subgroup.mem_subgroupOf.mp (h hy)
    have hinf : D.T ⊓ K ⊓ CFSG.Open.pCoreOf 2 K = CFSG.Open.pCoreOf 2 K :=
      inf_eq_right.mpr hO2le
    rw [hinf] at hScard
    have hbar : UC22.barImage K (D.T ⊓ K) = CFSG.Quasithin.imageOTwoQuot K (D.T ⊓ K) := rfl
    rw [hbar, hScard]
    ring
  · intro t ht htK
    have htN : t ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr htK
    have hfix : (UC22.barImage K (D.T ⊓ K)).map
        (CFSG.pCoreQuotMulAut ↥K
          (Subgroup.normalizerMonoidHom K ⟨t, htN⟩)).toMonoidHom =
        UC22.barImage K (D.T ⊓ K) :=
      map_pCoreQuotMulAut_sylow_of_mem_normalizer ht htN
    have hP : P₁.map (CFSG.pCoreQuotMulAut ↥K
        (Subgroup.normalizerMonoidHom K ⟨t, htN⟩)).toMonoidHom = P₁ :=
      (hinv _ hfix).1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (S18.mem_normalizer_barPreimage htN hP)

theorem center_K1Nine_eq_bot
    {D : Data G} {K : Subgroup G} (hK : K ∈ calC D.M)
    (hTits : LieModel (Bar2 K) .Tits 0 2 1) :
    Subgroup.center ↥(K1Nine D K) = ⊥ := by
  have hsimple : IsSimpleGroup (Bar2 K) := by
    obtain ⟨-, hRT⟩ := CFSG.Blueprint.LieModel.reeTitsModel hTits (by decide)
    exact (CFSG.LieType.Simplicity.fam_tits_simplicity (Bar2 K) 2 1 hRT).2
  have hperfect : Group.IsPerfect (Bar2 K) := Group.isPerfect_def.mpr hK.2.2.1
  have hcen : Subgroup.center (Bar2 K) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (Bar2 K)) with h | h
    · exact h
    · exfalso
      have hcomm : IsMulCommutative (Bar2 K) := ⟨⟨fun a b => by
        have hb : b ∈ Subgroup.center (Bar2 K) := h ▸ Subgroup.mem_top b
        exact Subgroup.mem_center_iff.mp hb a⟩⟩
      have hsub : Subsingleton (Bar2 K) := hperfect.subsingleton_of_isMulCommutative
      exact absurd hsub (not_subsingleton (Bar2 K))
  obtain ⟨e⟩ : Nonempty (Bar2 K ≃* ↥(K1Nine D K)) := nonempty_bar2_mulEquiv_K1 hK
  exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e.symm hcen

private theorem inf_eq_bot_of_card_three_of_two {A U : Subgroup G} (hA : Nat.card ↥A = 3)
    (hU : IsPGroup 2 U) : A ⊓ U = ⊥ := by
  rw [inf_comm]
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.inf_eq_bot_of_isPGroup_two_of_card_three
    hU hA

theorem tits_three_permutes {D : Data G} {K P A : Subgroup G}
    (hK : K ∈ calC D.M) (hPK : P ≤ K) (hSP : D.T ⊓ K ≤ P)
    (hPcard : Nat.card ↥P = 3 * Nat.card ↥(D.T ⊓ K))
    (hPinv : ∀ t ∈ D.T, K.map (MulAut.conj t).toMonoidHom = K →
      P.map (MulAut.conj t).toMonoidHom = P)
    (hAP : A ≤ P) (hAcard : Nat.card ↥A = 3) :
    (UC22.barImage D.M A : Set (Mbar9 D)) * (S1Nine D K : Set (Mbar9 D)) =
      (S1Nine D K : Set (Mbar9 D)) * (UC22.barImage D.M A) := by
  classical
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hK.1
  have hAM : A ≤ D.M := hAP.trans (hPK.trans hKM)
  have hPM : P ≤ D.M := hPK.trans hKM
  have hO2K_le : CFSG.Open.pCoreOf 2 K ≤ D.T ⊓ K := by
    have h := CFSG.Quasithin.pCore_two_le_subgroupOf
      (CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
        (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM) hKM
        ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hKM).mp hK.1))
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    exact hyx ▸ Subgroup.mem_subgroupOf.mp (h hy)
  have hO2P : P ⊓ CFSG.Open.pCoreOf 2 D.M = CFSG.Open.pCoreOf 2 K := by
    apply le_antisymm
    · refine (le_inf inf_le_right (inf_le_left.trans hPK)).trans ?_
      exact uc22p2214_pCoreOf_inf_le hKM
    · exact le_inf (hO2K_le.trans hSP)
        (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hK.1)
  have hO2S : (D.T ⊓ K) ⊓ CFSG.Open.pCoreOf 2 D.M = CFSG.Open.pCoreOf 2 K := by
    apply le_antisymm
    · refine (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans ?_
      exact uc22p2214_pCoreOf_inf_le hKM
    · exact le_inf hO2K_le
        (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hK.1)
  have hAcard' : Nat.card ↥(UC22.barImage D.M A) = 3 := by
    have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M A hAM
    have hAO2 : A ⊓ CFSG.Open.pCoreOf 2 D.M = ⊥ :=
      inf_eq_bot_of_card_three_of_two hAcard (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
    rw [hAO2, Subgroup.card_bot, mul_one, hAcard] at h
    exact h.symm
  have hPbar_card : Nat.card ↥(UC22.barImage D.M P) =
      3 * Nat.card ↥(UC22.barImage D.M (D.T ⊓ K)) := by
    have hP := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M P hPM
    have hS := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M (D.T ⊓ K)
      (inf_le_left.trans D.sylowM.le)
    rw [hO2P] at hP
    rw [hO2S] at hS
    have hpos : 0 < Nat.card ↥(CFSG.Open.pCoreOf 2 K) := Nat.card_pos
    have hgoal : Nat.card ↥(CFSG.Quasithin.imageOTwoQuot D.M P) =
        3 * Nat.card ↥(CFSG.Quasithin.imageOTwoQuot D.M (D.T ⊓ K)) := by
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      calc Nat.card ↥(CFSG.Quasithin.imageOTwoQuot D.M P) *
            Nat.card ↥(CFSG.Open.pCoreOf 2 K)
          = Nat.card ↥P := hP.symm
        _ = 3 * Nat.card ↥(D.T ⊓ K) := hPcard
        _ = 3 * (Nat.card ↥(CFSG.Quasithin.imageOTwoQuot D.M (D.T ⊓ K)) *
              Nat.card ↥(CFSG.Open.pCoreOf 2 K)) := by rw [hS]
        _ = 3 * Nat.card ↥(CFSG.Quasithin.imageOTwoQuot D.M (D.T ⊓ K)) *
              Nat.card ↥(CFSG.Open.pCoreOf 2 K) := by ring
    exact hgoal
  have hPT : UC22.barImage D.M P ⊓ Tbar9 D = UC22.barImage D.M (D.T ⊓ K) := by
    apply le_antisymm
    · refine (le_inf (inf_le_left.trans (CFSG.Quasithin.imageOTwoQuot_mono hPK))
        inf_le_right).trans (le_of_eq ?_)
      exact (inf_comm _ _).trans
        (S18.imageBar2_inf_of_isSylowIn (TwelveShort.isSylowIn_of_le D D.sylowM.le))
    · exact le_inf (CFSG.Quasithin.imageOTwoQuot_mono hSP)
        (CFSG.Quasithin.imageOTwoQuot_mono inf_le_left)
  let U : Subgroup G := D.T ⊓ Subgroup.normalizer (K : Set G)
  have hUbar : UC22.barImage D.M U = S1Nine D K :=
    imageOTwoQuot_inf_normalizer (D := D) (L := K) hK
  have hU2 : IsPGroup 2 ↥(S1Nine D K) := by
    rw [← hUbar]
    exact ((D.sylowM.isPGroup.to_le inf_le_left).comap_subtype (K := D.M)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
  have hTPbar : S1Nine D K ≤
      Subgroup.normalizer (UC22.barImage D.M P : Set (Mbar9 D)) := by
    rw [← hUbar]
    intro s hs
    obtain ⟨t, htM, htU, hts⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp hs
    have htT : t ∈ D.T := htU.1
    have htN : t ∈ Subgroup.normalizer (K : Set G) := htU.2
    have htK : K.map (MulAut.conj t).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
    have hPN : P.map (MulAut.conj t).toMonoidHom = P := hPinv t htT htK
    have hconj : MulAut.conj (QuotientGroup.mk ⟨t, htM⟩ : Mbar9 D) =
        CFSG.pCoreQuotMulAut ↥D.M
          (Subgroup.normalizerMonoidHom D.M ⟨t, Subgroup.le_normalizer htM⟩) := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [CFSG.pCoreQuotMulAut_mk]
        rfl
    have himg : (UC22.barImage D.M P).map (MulAut.conj s).toMonoidHom =
        UC22.barImage D.M P := by
      rw [← hts, hconj,
        S18.barImage_map_pCoreQuotMulAut (Subgroup.le_normalizer htM) hPM, hPN]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact himg
  have hSbar_le_S1 : UC22.barImage D.M (D.T ⊓ K) ≤ S1Nine D K :=
    le_inf (CFSG.Quasithin.imageOTwoQuot_mono inf_le_left)
      ((CFSG.Quasithin.imageOTwoQuot_mono inf_le_right).trans Subgroup.le_normalizer)
  have hS1inf : S1Nine D K ⊓ UC22.barImage D.M P = UC22.barImage D.M (D.T ⊓ K) := by
    apply le_antisymm
    · refine (le_inf (inf_le_left.trans (show S1Nine D K ≤ Tbar9 D from inf_le_left))
        inf_le_right).trans (le_of_eq ?_)
      rw [inf_comm]
      exact hPT
    · exact le_inf hSbar_le_S1 (CFSG.Quasithin.imageOTwoQuot_mono hSP)
  have hPsup : Nat.card ↥(UC22.barImage D.M P ⊔ S1Nine D K) =
      3 * Nat.card ↥(S1Nine D K) := by
    have h := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
      (H := S1Nine D K) (K := UC22.barImage D.M P) hTPbar
    rw [hS1inf, hPbar_card] at h
    have hpos : 0 < Nat.card ↥(UC22.barImage D.M (D.T ⊓ K)) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [sup_comm, h]
    ring
  have hAU : UC22.barImage D.M A ⊓ S1Nine D K = ⊥ :=
    inf_eq_bot_of_card_three_of_two hAcard' hU2
  set X : Subgroup (Mbar9 D) := UC22.barImage D.M P ⊔ S1Nine D K with hX
  have hAX : UC22.barImage D.M A ≤ X :=
    (CFSG.Quasithin.imageOTwoQuot_mono hAP).trans le_sup_left
  have hSX : S1Nine D K ≤ X := le_sup_right
  have hcardc : Nat.card ↥((UC22.barImage D.M A).subgroupOf X) *
      Nat.card ↥((S1Nine D K).subgroupOf X) = Nat.card ↥X := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv,
      hAcard', hX, hPsup]
  have hdisj : Disjoint ((UC22.barImage D.M A).subgroupOf X) ((S1Nine D K).subgroupOf X) := by
    rw [disjoint_iff]
    ext x
    constructor
    · intro hx
      have h1 : (x : Mbar9 D) ∈ UC22.barImage D.M A :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1
      have h2 : (x : Mbar9 D) ∈ S1Nine D K :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subgroup.mem_bot.mp (by rw [← hAU]; exact ⟨h1, h2⟩))
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hprod : ∀ (Y Z : Subgroup (Mbar9 D)) (hY : Y ≤ X) (hZ : Z ≤ X),
      Nat.card ↥(Y.subgroupOf X) * Nat.card ↥(Z.subgroupOf X) = Nat.card ↥X →
      Disjoint (Y.subgroupOf X) (Z.subgroupOf X) →
      (Y : Set (Mbar9 D)) * (Z : Set (Mbar9 D)) = (X : Set (Mbar9 D)) := by
    intro Y Z hY hZ hc hd
    have hcomp := Subgroup.isComplement'_of_card_mul_and_disjoint hc hd
    have hmul := hcomp.mul_eq
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, z, hz, rfl⟩
      exact X.mul_mem (hY hy) (hZ hz)
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥X) ∈
          ((Y.subgroupOf X : Subgroup ↥X) : Set ↥X) *
            ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
        rw [hmul]
        trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
      exact ⟨(a : Mbar9 D), Subgroup.mem_subgroupOf.mp ha, (b : Mbar9 D),
        Subgroup.mem_subgroupOf.mp hb, congrArg Subtype.val hab⟩
  have hset1 := hprod (UC22.barImage D.M A) (S1Nine D K) hAX hSX hcardc hdisj
  have hcardc' : Nat.card ↥((S1Nine D K).subgroupOf X) *
      Nat.card ↥((UC22.barImage D.M A).subgroupOf X) = Nat.card ↥X := by
    rw [mul_comm]; exact hcardc
  have hdisj' : Disjoint ((S1Nine D K).subgroupOf X) ((UC22.barImage D.M A).subgroupOf X) := by
    rw [disjoint_comm]; exact hdisj
  have hset2 := hprod (S1Nine D K) (UC22.barImage D.M A) hSX hAX hcardc' hdisj'
  rw [hset1, hset2]

theorem exists_permutes_of_barImage {D : Data G} {X : Subgroup G} {Xbar : Subgroup (Mbar9 D)}
    (hXM : X ≤ D.M) (hTX : D.T ≤ Subgroup.normalizer (X : Set G))
    (hXbar : Xbar ≤ UC22.barImage D.M X)
    (hEl : CFSG.Open.IsElemAbelian 3 Xbar)
    (hPerm : (Xbar : Set (Mbar9 D)) * (Tbar9 D : Set (Mbar9 D)) =
      (Tbar9 D : Set (Mbar9 D)) * Xbar)
    (hRank : 2 ≤ CFSG.Open.pRank 3 Xbar) :
    ∃ E : Subgroup G, E ≤ X ∧ CFSG.Open.IsElemAbelian 3 E ∧ Permutes E D.T ∧
      2 ≤ CFSG.Open.pRank 3 E := by
  classical
  have hTM : D.T ≤ D.M := D.sylowM.le
  set H : Subgroup G := X ⊔ D.T with hH
  have hTH : D.T ≤ H := le_sup_right
  have hHM : H ≤ D.M := sup_le hXM hTM
  have hXH : X ≤ H := le_sup_left
  have hHnormX : H ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hTX
  have hXnormal : (Subgroup.subgroupOf X H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHnormX
  set Hbar : Subgroup (Mbar9 D) := UC22.barImage D.M H with hHbar
  have hXbarH : Xbar ≤ Hbar := hXbar.trans (CFSG.Quasithin.imageOTwoQuot_mono hXH)
  have hTbarH : Tbar9 D ≤ Hbar := CFSG.Quasithin.imageOTwoQuot_mono hTH
  let f : ↥H →* ↥Hbar :=
    { toFun := fun h => ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(h : G), hHM h.2⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨y', hy', hyH, rfl⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp hy
    refine ⟨⟨y', hyH⟩, Subtype.ext ?_⟩
    exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) (Subtype.ext rfl)
  have hker : f.ker ≤ Subgroup.subgroupOf D.T H := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(h : G), hHM h.2⟩ = 1 :=
      congrArg Subtype.val hh
    have h2 : (⟨(h : G), hHM h.2⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M :=
      (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mpr (pCoreOf_le_sylow D.sylowM ⟨_, h2, rfl⟩)
  have hS : IsPGroup 2 (Subgroup.subgroupOf D.T H) :=
    D.sylowM.isPGroup.comap_subtype (K := H)
  have hSmap : (Subgroup.subgroupOf D.T H).map f =
      Subgroup.subgroupOf (Tbar9 D) Hbar := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hh))
    · intro hx
      obtain ⟨t, htM, htT, htx⟩ :=
        CFSG.Quasithin.mem_imageOTwoQuot_iff.mp (Subgroup.mem_subgroupOf.mp hx)
      exact ⟨⟨t, hTH htT⟩, Subgroup.mem_subgroupOf.mpr htT, Subtype.ext htx⟩
  have hPermH : ((Xbar.subgroupOf Hbar : Subgroup ↥Hbar) : Set ↥Hbar) *
      (((Subgroup.subgroupOf D.T H).map f : Subgroup ↥Hbar) : Set ↥Hbar) =
      (((Subgroup.subgroupOf D.T H).map f : Subgroup ↥Hbar) : Set ↥Hbar) *
        ((Xbar.subgroupOf Hbar : Subgroup ↥Hbar) : Set ↥Hbar) := by
    rw [hSmap]
    apply Set.Subset.antisymm
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      have ha' : (a : Mbar9 D) ∈ Xbar := Subgroup.mem_subgroupOf.mp ha
      have hb' : (b : Mbar9 D) ∈ Tbar9 D := Subgroup.mem_subgroupOf.mp hb
      have hab : (a : Mbar9 D) * (b : Mbar9 D) ∈
          (Xbar : Set (Mbar9 D)) * (Tbar9 D : Set (Mbar9 D)) := ⟨_, ha', _, hb', rfl⟩
      rw [hPerm] at hab
      obtain ⟨c, hc, d, hd, hcd⟩ := hab
      have hdH : d ∈ Hbar := hXbarH hd
      have hcH : c ∈ Hbar := by
        have h1 : c = (a : Mbar9 D) * (b : Mbar9 D) * d⁻¹ := by
          rw [← hcd]
          group
        rw [h1]
        exact Hbar.mul_mem (Hbar.mul_mem a.2 b.2) (Hbar.inv_mem hdH)
      exact ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hc, ⟨d, hdH⟩,
        Subgroup.mem_subgroupOf.mpr hd, Subtype.ext hcd⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      have ha' : (a : Mbar9 D) ∈ Tbar9 D := Subgroup.mem_subgroupOf.mp ha
      have hb' : (b : Mbar9 D) ∈ Xbar := Subgroup.mem_subgroupOf.mp hb
      have hab : (a : Mbar9 D) * (b : Mbar9 D) ∈
          (Tbar9 D : Set (Mbar9 D)) * (Xbar : Set (Mbar9 D)) := ⟨_, ha', _, hb', rfl⟩
      rw [← hPerm] at hab
      obtain ⟨c, hc, d, hd, hcd⟩ := hab
      have hcH : c ∈ Hbar := hXbarH hc
      have hdH : d ∈ Hbar := hTbarH hd
      exact ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hc, ⟨d, hdH⟩,
        Subgroup.mem_subgroupOf.mpr hd, Subtype.ext hcd⟩
  have hEbarP : IsPGroup 3 (Xbar.subgroupOf Hbar) := by
    exact hEl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXbarH).symm
  obtain ⟨E, hEP, hEf, ⟨eE⟩, hEperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift f hf hS hker (p := 3) (by norm_num) hEbarP hPermH
  set E' : Subgroup G := E.map H.subtype with hE'
  have hE'X : E' ≤ X := by
    have hle : E ≤ X.subgroupOf H := by
      have hidx : ¬ 3 ∣ (X.subgroupOf H).index := by
        have h1 : (X.subgroupOf H).index = X.relIndex H := rfl
        rw [h1]
        have h2 := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
          (H := D.T) (K := X) hTX).2
        rw [show D.T ⊔ X = H from by rw [hH, sup_comm]] at h2
        rw [h2]
        have hdvd : (D.T ⊓ X).relIndex D.T ∣ Nat.card ↥D.T := by
          rw [inf_comm]
          exact Subgroup.relIndex_dvd_card _ _
        obtain ⟨k, hk⟩ := (D.sylowM.isPGroup).exists_card_eq
        rw [hk] at hdvd
        intro h3
        have h4 : (3 : ℕ) ∣ 2 ^ k := h3.trans hdvd
        exact absurd (Nat.prime_three.dvd_of_dvd_pow h4) (by norm_num)
      exact CFSG.AGLEmbeddingD2.le_of_isPGroup_of_not_dvd_index Nat.prime_three hidx hEP
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hle hy)
  have hE'el : CFSG.Open.IsElemAbelian 3 E' := by
    have h1 : CFSG.IsElementaryAbelian 3 ↥Xbar :=
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).mp hEl
    have e1 : ↥(Xbar.subgroupOf Hbar) ≃* ↥Xbar := Subgroup.subgroupOfEquivOfLe hXbarH
    have e3 : ↥E ≃* ↥E' := Subgroup.equivMapOfInjective E H.subtype H.subtype_injective
    exact (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv (e1.symm.trans (eE.symm.trans e3)) h1)
  have hE'perm : Permutes E' D.T := by
    have h := congrArg (Set.image H.subtype) hEperm
    rw [Set.image_mul, Set.image_mul] at h
    have h1 : H.subtype '' (E : Set ↥H) = (E' : Set G) := by
      rw [← Subgroup.coe_map, hE']
    have h2 : H.subtype '' ((Subgroup.subgroupOf D.T H) : Set ↥H) = (D.T : Set G) := by
      rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH]
    rw [h1, h2] at h
    exact h
  have hE'rank : 2 ≤ CFSG.Open.pRank 3 E' := by
    have e1 : ↥(Xbar.subgroupOf Hbar) ≃* ↥Xbar := Subgroup.subgroupOfEquivOfLe hXbarH
    have e3 : ↥E ≃* ↥E' := Subgroup.equivMapOfInjective E H.subtype H.subtype_injective
    have h1 : CFSG.Open.pRank 3 Xbar = CFSG.Open.pRank 3 (⊤ : Subgroup ↥Xbar) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup Xbar
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Xbar) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥E') :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e1.symm.trans (eE.symm.trans e3))
    have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥E') = CFSG.Open.pRank 3 E' :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup E').symm
    rw [← h3, ← h2, ← h1]
    exact hRank
  exact ⟨E', hE'X, hE'el, hE'perm, hE'rank⟩

theorem conj_member_facts {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hKconj : K ∈ UC22.conjSetOf D.M L) (hTits : LieModel (Bar2 L) .Tits 0 2 1) :
    K ∈ calC D.M ∧ Nonempty (Bar2 L ≃* Bar2 K) ∧ K ≤ UC22.conjClosure D.M L ∧
      LieModel (Bar2 K) .Tits 0 2 1 := by
  obtain ⟨g, hgM, rfl⟩ := hKconj
  refine ⟨?_, bar2_conj_equiv L g, ?_, ?_⟩
  · exact UC6S846.calC_map D.M (MulAut.conj g)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)) hL
  · exact le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf D.M L) => K) _
      ⟨g, hgM, rfl⟩ le_rfl
  · obtain ⟨e⟩ := bar2_conj_equiv L g
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hTits

theorem exists_of_not_normalizes
    {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hKconj : K ∈ UC22.conjSetOf D.M L)
    (hKne : ¬ Tbar9 D ≤ Subgroup.normalizer (K1Nine D K : Set (Mbar9 D)))
    (hTi : Inputs1719.K_TitsParabolicGen) (hTits : LieModel (Bar2 L) .Tits 0 2 1) :
    ∃ E : Subgroup G, E ≤ UC22.conjClosure D.M L ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Permutes E D.T ∧ 2 ≤ CFSG.Open.pRank 3 E := by
  classical
  obtain ⟨hKcal, ⟨eK⟩, hKle, hTitsK⟩ := conj_member_facts hL hKconj hTits
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hKcal.1
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  obtain ⟨P, hSP, hPK, hPcard, hPinv⟩ := exists_tits_parabolic hTi hKcal hTitsK
  obtain ⟨A, hAP, hAcard⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_le_card_three_of_three_dvd (S := P)
      ⟨Nat.card ↥(D.T ⊓ K), hPcard⟩
  let Abar : Subgroup (Mbar9 D) := UC22.barImage D.M A
  have hAM : A ≤ D.M := hAP.trans (hPK.trans hKM)
  have hAcard' : Nat.card ↥Abar = 3 := by
    have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M A hAM
    have hAO2 : A ⊓ CFSG.Open.pCoreOf 2 D.M = ⊥ :=
      inf_eq_bot_of_card_three_of_two hAcard (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
    rw [hAO2, Subgroup.card_bot, mul_one, hAcard] at h
    exact h.symm
  have hAbarK : Abar ≤ K1Nine D K := CFSG.Quasithin.imageOTwoQuot_mono (hAP.trans hPK)
  have hAbarR : Abar ≤ UC22.barImage D.M (UC22.conjClosure D.M L) :=
    CFSG.Quasithin.imageOTwoQuot_mono (hAP.trans (hPK.trans hKle))
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTX : D.T ≤ Subgroup.normalizer (UC22.conjClosure D.M L : Set G) :=
    hTM.trans (uc22p22v_le_normalizer_conjClosure D.M L)
  have hXM : UC22.conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le hLM
  have hTR : Tbar9 D ≤ Subgroup.normalizer
      (UC22.barImage D.M (UC22.conjClosure D.M L) : Set (Mbar9 D)) := by
    intro s hs
    obtain ⟨t, htM, htT, hts⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    erw [← hts, (barImage_map_conj D.M (UC22.conjClosure D.M L) hXM htM).symm]
    congr 1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTX htT)
  have hKne' : ∃ t ∈ Tbar9 D,
      (K1Nine D K).map (MulAut.conj t).toMonoidHom ≠ K1Nine D K := by
    by_contra h
    apply hKne
    intro s hs
    by_contra hs'
    exact h ⟨s, hs, (Subgroup.mem_normalizer_iff_map_conj_eq).not.mp hs'⟩
  have hcomm : ∀ t ∈ Tbar9 D, (K1Nine D K).map (MulAut.conj t).toMonoidHom ≠ K1Nine D K →
      ∀ x ∈ K1Nine D K, ∀ y ∈ (K1Nine D K).map (MulAut.conj t).toMonoidHom, Commute x y := by
    intro s hs hne x hx y hy
    obtain ⟨t, htM, htT, hts⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp hs
    have hKt : K.map (MulAut.conj t).toMonoidHom ∈ calC D.M :=
      UC6S846.calC_map D.M (MulAut.conj t)
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htM)) hKcal
    have hne' : UC22.barImage D.M (K.map (MulAut.conj t).toMonoidHom) ≠ K1Nine D K := by
      intro h
      apply hne
      rw [← hts]
      erw [(barImage_map_conj D.M K hKM htM).symm]
      exact h
    have hne'' : K ≠ K.map (MulAut.conj t).toMonoidHom := by
      intro h
      exact hne' (congrArg (fun X : Subgroup G => UC22.barImage D.M X) h.symm)
    have hy' : y ∈ UC22.barImage D.M (K.map (MulAut.conj t).toMonoidHom) := by
      have hy'' : y ∈ (UC22.barImage D.M K).map (MulAut.conj s).toMonoidHom := hy
      rw [← hts] at hy''
      erw [(barImage_map_conj D.M K hKM htM).symm] at hy''
      exact hy''
    exact uc22p22l_barImage_commute hKcal hKt hne'' x hx y hy'
  have hperm : (Abar : Set (Mbar9 D)) *
      ((Tbar9 D ⊓ Subgroup.normalizer (K1Nine D K : Set (Mbar9 D)) :
        Subgroup (Mbar9 D)) : Set (Mbar9 D)) =
      ((Tbar9 D ⊓ Subgroup.normalizer (K1Nine D K : Set (Mbar9 D)) :
        Subgroup (Mbar9 D)) : Set (Mbar9 D)) * Abar := by
    simpa [Abar, S1Nine] using tits_three_permutes hKcal hPK hSP hPcard hPinv hAP hAcard
  have hAnc : ¬ Abar ≤ (Subgroup.center ↥(K1Nine D K)).map (K1Nine D K).subtype := by
    rw [center_K1Nine_eq_bot hKcal hTitsK, Subgroup.map_bot]
    intro hle
    have hbot : Abar = ⊥ := le_bot_iff.mp hle
    rw [hbot, Subgroup.card_bot] at hAcard'
    exact absurd hAcard' (by norm_num)
  obtain ⟨Xbar, -, hXR, hXperm, hXel, hXrank⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_permutes_sup_conj (r := 3) Nat.prime_three
      hAbarK hcomm hperm hKne' hAnc hAcard' hAbarR hTR
  exact exists_permutes_of_barImage hXM hTX hXR hXel hXperm hXrank

theorem exists_of_fixed_pair
    {D : Data G} {L K₂ : Subgroup G} (hL : L ∈ calC D.M)
    (hK₂conj : K₂ ∈ UC22.conjSetOf D.M L) (hne : K₂ ≠ L)
    (hfixL : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (hfix₂ : Tbar9 D ≤ Subgroup.normalizer (K1Nine D K₂ : Set (Mbar9 D)))
    (hTi : Inputs1719.K_TitsParabolicGen) (hTits : LieModel (Bar2 L) .Tits 0 2 1) :
    ∃ E : Subgroup G, E ≤ UC22.conjClosure D.M L ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Permutes E D.T ∧ 2 ≤ CFSG.Open.pRank 3 E := by
  classical
  obtain ⟨hK₂cal, ⟨e₂⟩, hK₂le, hTits₂⟩ := conj_member_facts hL hK₂conj hTits
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hK₂M : K₂ ≤ D.M := CFSG.Quasithin.A3.subnormal_le hK₂cal.1
  obtain ⟨P₁, hS₁P₁, hP₁L, hP₁card, hP₁inv⟩ := exists_tits_parabolic hTi hL hTits
  obtain ⟨A₁, hA₁P₁, hA₁card⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_le_card_three_of_three_dvd (S := P₁)
      ⟨Nat.card ↥(D.T ⊓ L), hP₁card⟩
  obtain ⟨P₂, hS₂P₂, hP₂K₂, hP₂card, hP₂inv⟩ := exists_tits_parabolic hTi hK₂cal hTits₂
  obtain ⟨A₂, hA₂P₂, hA₂card⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_le_card_three_of_three_dvd (S := P₂)
      ⟨Nat.card ↥(D.T ⊓ K₂), hP₂card⟩
  let A₁bar : Subgroup (Mbar9 D) := UC22.barImage D.M A₁
  let A₂bar : Subgroup (Mbar9 D) := UC22.barImage D.M A₂
  have hA₁card' : Nat.card ↥A₁bar = 3 := by
    have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M A₁
      (hA₁P₁.trans (hP₁L.trans hLM))
    have hAO2 : A₁ ⊓ CFSG.Open.pCoreOf 2 D.M = ⊥ :=
      inf_eq_bot_of_card_three_of_two hA₁card (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
    rw [hAO2, Subgroup.card_bot, mul_one, hA₁card] at h
    exact h.symm
  have hA₂card' : Nat.card ↥A₂bar = 3 := by
    have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M A₂
      (hA₂P₂.trans (hP₂K₂.trans hK₂M))
    have hAO2 : A₂ ⊓ CFSG.Open.pCoreOf 2 D.M = ⊥ :=
      inf_eq_bot_of_card_three_of_two hA₂card (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
    rw [hAO2, Subgroup.card_bot, mul_one, hA₂card] at h
    exact h.symm
  have hA₁K : A₁bar ≤ K1Nine D L := CFSG.Quasithin.imageOTwoQuot_mono (hA₁P₁.trans hP₁L)
  have hA₂K : A₂bar ≤ K1Nine D K₂ := CFSG.Quasithin.imageOTwoQuot_mono (hA₂P₂.trans hP₂K₂)
  have hA₁R : A₁bar ≤ UC22.barImage D.M (UC22.conjClosure D.M L) :=
    CFSG.Quasithin.imageOTwoQuot_mono
      (hA₁P₁.trans (hP₁L.trans (uc22p22v_le_conjClosure D.M L)))
  have hc : ∀ a ∈ A₁bar, ∀ b ∈ A₂bar, a * b = b * a := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hL hK₂cal (Ne.symm hne) a (hA₁K ha) b (hA₂K hb)
  have hdisj : A₁bar ⊓ A₂bar = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hcen : (⟨x, hA₁K hx1⟩ : ↥(K1Nine D L)) ∈ Subgroup.center ↥(K1Nine D L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : Mbar9 D) * x = x * (y : Mbar9 D)
      exact uc22p22l_barImage_commute hL hK₂cal (Ne.symm hne) (y : Mbar9 D) y.2
        x (hA₂K hx2)
    rw [center_K1Nine_eq_bot hL hTits] at hcen
    have hx1' : (⟨x, hA₁K hx1⟩ : ↥(K1Nine D L)) = 1 := Subgroup.mem_bot.mp hcen
    have hx1'' : x = 1 := congrArg Subtype.val hx1'
    rwa [Subgroup.mem_bot]
  have hA₁el : CFSG.Open.IsElemAbelian 3 A₁bar :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime hA₁card'
  have hA₂el : CFSG.Open.IsElemAbelian 3 A₂bar :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime hA₂card'
  have hXel : CFSG.Open.IsElemAbelian 3 (A₁bar ⊔ A₂bar) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hA₁el hA₂el hc
  have hperm₁ : (A₁bar : Set (Mbar9 D)) * (Tbar9 D : Set (Mbar9 D)) =
      (Tbar9 D : Set (Mbar9 D)) * A₁bar := by
    have h := tits_three_permutes hL hP₁L hS₁P₁ hP₁card hP₁inv hA₁P₁ hA₁card
    have hS : S1Nine D L = Tbar9 D := by rw [S1Nine, inf_eq_left.mpr hfixL]
    rwa [hS] at h
  have hperm₂ : (A₂bar : Set (Mbar9 D)) * (Tbar9 D : Set (Mbar9 D)) =
      (Tbar9 D : Set (Mbar9 D)) * A₂bar := by
    have h := tits_three_permutes hK₂cal hP₂K₂ hS₂P₂ hP₂card hP₂inv hA₂P₂ hA₂card
    have hS : S1Nine D K₂ = Tbar9 D := by rw [S1Nine, inf_eq_left.mpr hfix₂]
    rwa [hS] at h
  have hsup_set : ((A₁bar ⊔ A₂bar : Subgroup (Mbar9 D)) : Set (Mbar9 D)) =
      (A₁bar : Set (Mbar9 D)) * (A₂bar : Set (Mbar9 D)) :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁bar A₂bar hc).2
  have hperm : ((A₁bar ⊔ A₂bar : Subgroup (Mbar9 D)) : Set (Mbar9 D)) *
      (Tbar9 D : Set (Mbar9 D)) =
      (Tbar9 D : Set (Mbar9 D)) * ((A₁bar ⊔ A₂bar : Subgroup (Mbar9 D)) : Set (Mbar9 D)) := by
    rw [hsup_set]
    calc (A₁bar : Set (Mbar9 D)) * (A₂bar : Set (Mbar9 D)) * (Tbar9 D : Set (Mbar9 D))
        = (A₁bar : Set (Mbar9 D)) * ((A₂bar : Set (Mbar9 D)) * (Tbar9 D : Set (Mbar9 D))) := by
          rw [mul_assoc]
      _ = (A₁bar : Set (Mbar9 D)) * ((Tbar9 D : Set (Mbar9 D)) * (A₂bar : Set (Mbar9 D))) := by
          rw [hperm₂]
      _ = ((A₁bar : Set (Mbar9 D)) * (Tbar9 D : Set (Mbar9 D))) * (A₂bar : Set (Mbar9 D)) := by
          rw [mul_assoc]
      _ = ((Tbar9 D : Set (Mbar9 D)) * (A₁bar : Set (Mbar9 D))) * (A₂bar : Set (Mbar9 D)) := by
          rw [hperm₁]
      _ = (Tbar9 D : Set (Mbar9 D)) * ((A₁bar : Set (Mbar9 D)) * (A₂bar : Set (Mbar9 D))) := by
          rw [mul_assoc]
  have hrank : 2 ≤ CFSG.Open.pRank 3 (A₁bar ⊔ A₂bar) := by
    have h3₁ : 3 ∣ Nat.card ↥A₁bar := ⟨1, by rw [hA₁card']⟩
    have h3₂ : 3 ∣ Nat.card ↥A₂bar := ⟨1, by rw [hA₂card']⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥A₁bar) 3 h3₁
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥A₂bar) 3 h3₂
    have hxsub : (x : Mbar9 D) ∈ A₁bar ⊔ A₂bar := Subgroup.mem_sup_left x.2
    have hysub : (y : Mbar9 D) ∈ A₁bar ⊔ A₂bar := Subgroup.mem_sup_right y.2
    have hxord' : orderOf (x : Mbar9 D) = 3 := by
      rw [Subgroup.orderOf_coe, hxord]
    have hyord' : orderOf (y : Mbar9 D) = 3 := by
      rw [Subgroup.orderOf_coe, hyord]
    have hcomm' : Commute (x : Mbar9 D) (y : Mbar9 D) := hc _ x.2 _ y.2
    have hyx : (y : Mbar9 D) ∉ Subgroup.zpowers (x : Mbar9 D) := by
      intro hy'
      have hyA₁ : (y : Mbar9 D) ∈ A₁bar := Subgroup.zpowers_le.mpr x.2 hy'
      have hybot : (y : Mbar9 D) ∈ (⊥ : Subgroup (Mbar9 D)) := by
        rw [← hdisj]
        exact ⟨hyA₁, y.2⟩
      have hy1 : (y : Mbar9 D) = 1 := Subgroup.mem_bot.mp hybot
      rw [hy1, orderOf_one] at hyord'
      exact absurd hyord'.symm (by norm_num)
    exact CFSG.GroupTheory.two_le_pRank_of_commute hxsub hysub hxord' hyord' hcomm' hyx
  have hXbar : (A₁bar ⊔ A₂bar) ≤ UC22.barImage D.M (UC22.conjClosure D.M L) :=
    sup_le hA₁R (CFSG.Quasithin.imageOTwoQuot_mono (hA₂P₂.trans (hP₂K₂.trans hK₂le)))
  have hXM : UC22.conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le hLM
  have hTX : D.T ≤ Subgroup.normalizer (UC22.conjClosure D.M L : Set G) :=
    D.sylowM.le.trans (uc22p22v_le_normalizer_conjClosure D.M L)
  exact exists_permutes_of_barImage hXM hTX hXbar hXel hperm hrank

theorem gap17_31_TitsPerm_holds
    (hTi : Inputs1719.K_TitsParabolicGen) (D : Data G) :
    ∀ L ∈ calC D.M, ¬ D.M ≤ normalizer (L : Set G) → LieModel (Bar2 L) .Tits 0 2 1 →
      ∃ E : Subgroup G, E ≤ UC22.conjClosure D.M L ∧ IsElemAbelian 3 E ∧ Permutes E D.T ∧
        2 ≤ CFSG.Open.pRank 3 E := by
  intro L hL hnN hTits
  classical
  have hex : ∃ g ∈ D.M, L.map (MulAut.conj g).toMonoidHom ≠ L := by
    by_contra h
    push Not at h
    exact hnN (fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h x hx))
  by_cases hfixL : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D))
  · obtain ⟨g, hgM, hgne⟩ := hex
    set K₂ : Subgroup G := L.map (MulAut.conj g).toMonoidHom with hK₂def
    have hK₂conj : K₂ ∈ UC22.conjSetOf D.M L := ⟨g, hgM, rfl⟩
    by_cases hfix₂ : Tbar9 D ≤ Subgroup.normalizer (K1Nine D K₂ : Set (Mbar9 D))
    · exact exists_of_fixed_pair hL hK₂conj hgne hfixL hfix₂ hTi hTits
    · exact exists_of_not_normalizes hL hK₂conj hfix₂ hTi hTits
  · refine exists_of_not_normalizes (K := L) hL ?_ hfixL hTi hTits
    refine ⟨1, D.M.one_mem, ?_⟩
    have hconj_one : MulAut.conj (1 : G) = 1 := by
      ext x
      simp [MulAut.conj_apply]
    rw [hconj_one]
    exact (Subgroup.map_id L).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
