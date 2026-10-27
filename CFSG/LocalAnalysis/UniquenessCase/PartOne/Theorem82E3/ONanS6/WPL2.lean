module

public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.GroupTheory.IndexThreeCosets
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.HardMathSupport.Solomon.Coordinator.C25Group
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
public import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G] {D : Data G}

noncomputable abbrev cenOf_wPL2 (e : G) : Subgroup G :=
  Subgroup.centralizer ({e} : Set G)

theorem isHatON_lbar_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
  unfold ThreeCover at hON
  obtain ⟨⟨hcomm, -⟩, hZ, hspor⟩ := hON
  change Nonempty (c.Lbar ⧸ Subgroup.center c.Lbar ≃*
    CFSG.Blueprint.NativeSporadic.Carrier .ONan) at hspor
  obtain ⟨e⟩ := hspor
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact ⟨hcomm, hZ, ⟨e.trans b⟩⟩

theorem card_Lbar_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    Nat.card c.Lbar = 3 * 460815505920 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center c.Lbar)
  obtain ⟨e⟩ := hON.2.2
  have hq : Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.ON = 460815505920
    exact CFSG.Sporadic.ON.card_ON_eq
  rw [h, hq, hON.2.1]

theorem factorization_card_Lbar_wPL2 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    (Nat.card c.Lbar).factorization 3 = 5 := by
  rw [card_Lbar_wPL2 c hON]
  have h : 3 * 460815505920 = 3 ^ 5 * 5689080320 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem factorization_card_L_wPL2 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    (Nat.card ↥c.L).factorization 3 = 5 := by
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  have hN3 : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hcardL : Nat.card ↥c.L = Nat.card c.Lbar * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  rw [hcardL, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN3, add_zero,
    factorization_card_Lbar_wPL2 c hON]

theorem card_PL_wPL2 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card ↥(P ⊓ c.L) = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPL : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ c.L) c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  rw [hPL.card_eq, factorization_card_L_wPL2 c hON]

noncomputable abbrev phiOf_wPL2 (c : Ctx82E3 D) : ↥D.M →* MulAut c.Lbar :=
  CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L

noncomputable abbrev modCenOf_wPL2 (c : Ctx82E3 D) : Subgroup G :=
  (phiOf_wPL2 c).ker.map D.M.subtype

theorem PL_image_data_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∃ Q : Sylow 3 c.Lbar,
      (Q : Subgroup c.Lbar) =
          ((P ⊓ c.L).subgroupOf c.L).map
            (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) ∧
      Nat.card (Q : Subgroup c.Lbar) = 3 ^ 5 ∧
      (∀ x ∈ (Q : Subgroup c.Lbar), x ^ 3 = 1) ∧
      (∀ x ∈ (Q : Subgroup c.Lbar), ∀ y ∈ (Q : Subgroup c.Lbar),
        ⁅x, y⁆ ∈ Subgroup.center c.Lbar) ∧
      (∀ z ∈ (Q : Subgroup c.Lbar),
        (∀ g ∈ (Q : Subgroup c.Lbar), g * z = z * g) → z ∈ Subgroup.center c.Lbar) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let PL : Subgroup ↥c.L := (P ⊓ c.L).subgroupOf c.L
  have hPLsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ c.L) c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  have hPLp : IsPGroup 3 PL := hPLsyl.isPGroup.comap_subtype
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  have hO2 : IsPGroup 2 π.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hdisj : PL ⊓ π.ker = ⊥ := by
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) PL π.ker hPLp hO2).eq_bot
  have hcardPL : Nat.card PL = 3 ^ 5 := by
    rw [← card_PL_wPL2 c hON hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ⊓ c.L ≤ c.L)).toEquiv
  have hcardMap : Nat.card (PL.map π) = 3 ^ 5 := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot π hdisj, hcardPL]
  let Q : Sylow 3 c.Lbar := Sylow.ofCard (PL.map π) (by
    rw [hcardMap, factorization_card_Lbar_wPL2 c hON])
  have hQcoe : (Q : Subgroup c.Lbar) = PL.map π := Sylow.coe_ofCard _ _
  obtain ⟨hQcard, hQexp, hQcomm, hQcenter⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds (X := c.Lbar)
      (isHatON_lbar_wPL2 c hON) Q
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [PL, π, O] using hQcoe
  · exact hQcard
  · exact hQexp
  · exact hQcomm
  · exact hQcenter

theorem mem_center_lbar_iff_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {a : G}
    (ha : a ∈ P ⊓ c.L) :
    QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨a, ha.2⟩ ∈ Subgroup.center c.Lbar ↔
      a ∈ zSub P c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  change π ⟨a, ha.2⟩ ∈ Subgroup.center c.Lbar ↔ a ∈ zSub P c.L
  obtain ⟨Q, hQcoe, -, -, -, hQcenter⟩ := PL_image_data_wPL2 c hON hP
  have haQ : π ⟨a, ha.2⟩ ∈ (Q : Subgroup c.Lbar) := by
    rw [hQcoe]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
  have hPdisjO : P ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ := by
    have hP3 : IsPGroup 3 P := hP.isPGroup
    have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P _ hP3 hO2).eq_bot
  have hcomm_mem : ∀ (t : G) (ht : t ∈ P ⊓ c.L),
      ⁅π ⟨t, ht.2⟩, π ⟨a, ha.2⟩⁆ = 1 → ⁅t, a⁆ = 1 := by
    intro t ht hcomm
    have hPLmem : ⁅t, a⁆ ∈ P ⊓ c.L :=
      ⟨Subgroup.commutator_le_self P (Subgroup.commutator_mem_commutator ht.1 ha.1),
        Subgroup.commutator_le_self c.L (Subgroup.commutator_mem_commutator ht.2 ha.2)⟩
    have hO : (⟨⁅t, a⁆, hPLmem.2⟩ : ↥c.L) ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      have hsub : (⟨⁅t, a⁆, hPLmem.2⟩ : ↥c.L) =
          ⁅(⟨t, ht.2⟩ : ↥c.L), (⟨a, ha.2⟩ : ↥c.L)⁆ := by
        ext
        rfl
      have hmap : π (⟨⁅t, a⁆, hPLmem.2⟩ : ↥c.L) = 1 := by
        rw [hsub, map_commutatorElement]
        exact hcomm
      simpa [π, O] using hmap
    have hmemO : ⁅t, a⁆ ∈ CFSG.Open.pCoreOf 2 c.L :=
      Subgroup.mem_map.mpr ⟨⟨⁅t, a⁆, hPLmem.2⟩, hO, rfl⟩
    have hbot : ⁅t, a⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hPdisjO]
      exact ⟨hPLmem.1, hmemO⟩
    simpa using hbot
  constructor
  · intro hcenter
    refine ⟨ha, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro t ht
    have hcomm_at : ⁅π ⟨a, ha.2⟩, π ⟨t, ht.2⟩⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_center_iff.mp hcenter (π ⟨t, ht.2⟩)).symm
    have hcomm : ⁅π ⟨t, ht.2⟩, π ⟨a, ha.2⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr
        ((commutatorElement_eq_one_iff_commute.mp hcomm_at).symm)
    exact commutatorElement_eq_one_iff_commute.mp (hcomm_mem t ht hcomm)
  · intro haZ
    rw [zSub, Subgroup.mem_inf] at haZ
    obtain ⟨-, hacent⟩ := haZ
    refine hQcenter (π ⟨a, ha.2⟩) haQ ?_
    intro g hg
    rw [hQcoe] at hg
    obtain ⟨t, htPL, rfl⟩ := Subgroup.mem_map.mp hg
    have htPL' : (t : G) ∈ P ⊓ c.L := by
      have h := htPL
      rw [Subgroup.mem_subgroupOf] at h
      exact h
    have ht : (t : G) ∈ P ⊓ c.L := htPL' 
    have hcent := Subgroup.mem_centralizer_iff.mp hacent (t : G) ht
    have hsub : (⟨a, ha.2⟩ : ↥c.L) * t = t * ⟨a, ha.2⟩ :=
      Subtype.ext hcent.symm
    exact (congrArg π hsub).symm

theorem card_centralizer_of_card_three_pow_five_wPL2 {Q : Type*} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 3 ^ 5) (hZ : Nat.card (Subgroup.center Q) = 3)
    (hcomm : ∀ a b : Q, ⁅a, b⁆ ∈ Subgroup.center Q) {g : Q}
    (hg : g ∉ Subgroup.center Q) :
    Nat.card (Subgroup.centralizer ({g} : Set Q)) = 81 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx_le : (Subgroup.centralizer ({g} : Set Q)).index ≤ 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_index_centralizer_le hZ hcomm g
  have hidx_dvd : (Subgroup.centralizer ({g} : Set Q)).index ∣ 3 ^ 5 := by
    rw [← hcard]
    exact Subgroup.index_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hidx_dvd
  have hi_le : i ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ i := by omega
    have h3 : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) h2
    rw [hi] at hidx_le
    norm_num at h3
    omega
  have hidx_ne : (Subgroup.centralizer ({g} : Set Q)).index ≠ 1 := by
    intro hone
    apply hg
    have htop : Subgroup.centralizer ({g} : Set Q) = ⊤ := Subgroup.index_eq_one.mp hone
    refine Subgroup.mem_center_iff.mpr (fun x => ?_)
    have hx : x ∈ Subgroup.centralizer ({g} : Set Q) := by rw [htop]; exact Subgroup.mem_top x
    exact Subgroup.mem_centralizer_singleton_iff.mp hx
  have hidx : (Subgroup.centralizer ({g} : Set Q)).index = 3 := by
    interval_cases i
    · rw [hi] at hidx_ne
      norm_num at hidx_ne
    · simpa [hi] using rfl
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({g} : Set Q))
  rw [hidx, hcard] at hmul
  norm_num at hmul ⊢
  omega

theorem card_inf_centralizer_PL_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {a : G}
    (ha : a ∈ P ⊓ c.L) (haZ : a ∉ zSub P c.L) :
    Nat.card ↥((P ⊓ c.L) ⊓ Subgroup.centralizer ({a} : Set G)) = 81 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let PL : Subgroup ↥c.L := (P ⊓ c.L).subgroupOf c.L
  obtain ⟨Q, hQcoe, hQcard, hQexp, hQcomm, hQcenter⟩ := PL_image_data_wPL2 c hON hP
  have haPL : (⟨a, ha.2⟩ : ↥c.L) ∈ PL := Subgroup.mem_subgroupOf.mpr ha
  have hπaQ : π ⟨a, ha.2⟩ ∈ (Q : Subgroup c.Lbar) := by
    rw [hQcoe]
    exact Subgroup.mem_map_of_mem π haPL
  let aQ : ↥Q := ⟨π ⟨a, ha.2⟩, hπaQ⟩
  have hcenter3 : IsPGroup 3 (Subgroup.center c.Lbar) :=
    IsPGroup.of_card (n := 1) (by rw [hON.2.1]; norm_num)
  have hcenterLeQ : Subgroup.center c.Lbar ≤ (Q : Subgroup c.Lbar) :=
    IsPGroup.le_sylow_of_normal hcenter3 Q
  have hcenterEq : (Subgroup.center ↥Q : Subgroup ↥Q) =
      (Subgroup.center c.Lbar).subgroupOf (Q : Subgroup c.Lbar) := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      refine hQcenter z z.2 ?_
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
    · intro hz
      refine Subgroup.mem_center_iff.mpr (fun w => ?_)
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hz (w : c.Lbar)
  have hcenterQcard : Nat.card (Subgroup.center ↥Q) = 3 := by
    rw [hcenterEq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcenterLeQ).toEquiv).trans hON.2.1
  have hcommQ : ∀ x y : ↥Q, ⁅x, y⁆ ∈ Subgroup.center ↥Q := by
    intro x y
    rw [hcenterEq, Subgroup.mem_subgroupOf]
    change ⁅(x : c.Lbar), (y : c.Lbar)⁆ ∈ Subgroup.center c.Lbar
    exact hQcomm x x.2 y y.2
  have hane : aQ ∉ Subgroup.center ↥Q := by
    intro hcent
    apply haZ
    refine (mem_center_lbar_iff_wPL2 c hON hP ha).mp ?_
    rw [hcenterEq, Subgroup.mem_subgroupOf] at hcent
    change π ⟨a, ha.2⟩ ∈ Subgroup.center c.Lbar
    exact hcent
  have hQcard' : Nat.card ↥Q = 3 ^ 5 := by
    change Nat.card ↥(Q : Subgroup c.Lbar) = 3 ^ 5
    exact hQcard
  have hcardCentQ : Nat.card (Subgroup.centralizer ({aQ} : Set ↥Q)) = 81 :=
    card_centralizer_of_card_three_pow_five_wPL2 hQcard' hcenterQcard hcommQ hane
  have hcentQeq : (Subgroup.centralizer ({aQ} : Set ↥Q)).map (Q : Subgroup c.Lbar).subtype =
      (Q : Subgroup c.Lbar) ⊓
        Subgroup.centralizer ({π ⟨a, ha.2⟩} : Set c.Lbar) := by
    ext g
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.2, (Subgroup.mem_centralizer_singleton_iff (G := c.Lbar)
        (g := π ⟨a, ha.2⟩) (k := (q : c.Lbar))).mpr ?_⟩
      simpa using congrArg Subtype.val
        ((Subgroup.mem_centralizer_singleton_iff (G := ↥Q) (g := aQ) (k := q)).mp hq)
    · intro hg
      refine ⟨⟨g, hg.1⟩, (Subgroup.mem_centralizer_singleton_iff (G := ↥Q)
        (g := aQ) (k := ⟨g, hg.1⟩)).mpr ?_, rfl⟩
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff (G := c.Lbar)
        (g := π ⟨a, ha.2⟩) (k := g)).mp hg.2
  have hcardCentAmbient : Nat.card ↥((Q : Subgroup c.Lbar) ⊓
      Subgroup.centralizer ({π ⟨a, ha.2⟩} : Set c.Lbar)) = 81 := by
    rw [← hcentQeq, Subgroup.card_map_of_injective (Q : Subgroup c.Lbar).subtype_injective]
    exact hcardCentQ
  have hPLp : IsPGroup 3 PL := by
    have hPLsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ c.L) c.L :=
      hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
    exact hPLsyl.isPGroup.comap_subtype
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  have hO2 : IsPGroup 2 π.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hdisjPL : PL ⊓ π.ker = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) PL π.ker hPLp hO2).eq_bot
  have hinjPL : Function.Injective (π.comp PL.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      apply Subtype.ext
      have hxO : (x : ↥c.L) ∈ π.ker := hx
      have hxbot : (x : ↥c.L) ∈ (⊥ : Subgroup ↥c.L) := by
        rw [← hdisjPL]
        exact ⟨x.2, hxO⟩
      simpa using hxbot
    · intro hx
      rw [hx]
      simp
  have hPLmapCent : ((PL ⊓
        Subgroup.centralizer ({⟨a, ha.2⟩} : Set ↥c.L)).map π) =
      (Q : Subgroup c.Lbar) ⊓
        Subgroup.centralizer ({π ⟨a, ha.2⟩} : Set c.Lbar) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hQcoe]
        exact Subgroup.mem_map_of_mem π hx.1
      · have hxcent : x ∈ Subgroup.centralizer ({⟨a, ha.2⟩} : Set ↥c.L) := hx.2
        have hcomm : x * ⟨a, ha.2⟩ = ⟨a, ha.2⟩ * x :=
          Subgroup.mem_centralizer_singleton_iff.mp hxcent
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          rw [← map_mul, ← map_mul, hcomm])
    · intro hy
      rw [hQcoe] at hy
      obtain ⟨x, hxPL, rfl⟩ := Subgroup.mem_map.mp hy.1
      refine ⟨x, ⟨hxPL, ?_⟩, rfl⟩
      have hcommπ : π x * π ⟨a, ha.2⟩ = π ⟨a, ha.2⟩ * π x :=
        (Subgroup.mem_centralizer_singleton_iff (G := c.Lbar)
          (g := π ⟨a, ha.2⟩) (k := π x)).mp hy.2
      have hxa : x * ⟨a, ha.2⟩ ∈ PL := PL.mul_mem hxPL haPL
      have hax : ⟨a, ha.2⟩ * x ∈ PL := PL.mul_mem haPL hxPL
      have hEqSub : (⟨x * ⟨a, ha.2⟩, hxa⟩ : PL) = ⟨⟨a, ha.2⟩ * x, hax⟩ := by
        apply hinjPL
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [map_mul, map_mul]
        exact hcommπ
      exact (Subgroup.mem_centralizer_singleton_iff (G := ↥c.L)
        (g := ⟨a, ha.2⟩) (k := x)).mpr
        (congrArg (fun z : PL => (z : ↥c.L)) hEqSub)
  have hdisjC : ((PL ⊓
      Subgroup.centralizer ({⟨a, ha.2⟩} : Set ↥c.L)) ⊓ π.ker) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    have hzPL : z ∈ PL := hz.1.1
    have hzker : z ∈ π.ker := hz.2
    have hzbot : z ∈ (⊥ : Subgroup ↥c.L) := by
      rw [← hdisjPL]
      exact ⟨hzPL, hzker⟩
    simpa using hzbot
  have hcardImage := CFSG.card_map_eq_card_of_inf_ker_eq_bot π hdisjC
  rw [hPLmapCent, hcardCentAmbient] at hcardImage
  have hcardSub : Nat.card ↥((PL ⊓
      Subgroup.centralizer ({⟨a, ha.2⟩} : Set ↥c.L))) = 81 := hcardImage.symm
  have hGleL : (P ⊓ c.L) ⊓ Subgroup.centralizer ({a} : Set G) ≤ c.L :=
    inf_le_left.trans inf_le_right
  have hsubEq : ((P ⊓ c.L) ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf c.L =
      PL ⊓ Subgroup.centralizer ({⟨a, ha.2⟩} : Set ↥c.L) := by
    ext x
    constructor
    · intro hx
      have hx' : (x : G) ∈ (P ⊓ c.L) ⊓ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mem_subgroupOf.mp hx
      refine ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hx'.1
      · exact (Subgroup.mem_centralizer_singleton_iff (G := ↥c.L)
          (g := ⟨a, ha.2⟩) (k := x)).mpr (by
            apply Subtype.ext
            exact (Subgroup.mem_centralizer_singleton_iff (G := G)
              (g := a) (k := (x : G))).mp hx'.2)
    · intro hx
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mp hx.1
      · exact (Subgroup.mem_centralizer_singleton_iff (G := G)
          (g := a) (k := (x : G))).mpr
          (congrArg (fun z : ↥c.L => (z : G))
            ((Subgroup.mem_centralizer_singleton_iff (G := ↥c.L)
              (g := ⟨a, ha.2⟩) (k := x)).mp hx.2))
  rw [← hsubEq] at hcardSub
  rw [← hcardSub]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGleL).toEquiv).symm

theorem map_P_eq_map_PL_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    (P.subgroupOf D.M).map (phiOf_wPL2 c) = ((P ⊓ c.L).subgroupOf D.M).map (phiOf_wPL2 c) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let A : Subgroup (MulAut c.Lbar) := (P.subgroupOf D.M).map (phiOf_wPL2 c)
  let B : Subgroup (MulAut c.Lbar) := ((P ⊓ c.L).subgroupOf D.M).map (phiOf_wPL2 c)
  have hconj_one_iff : ∀ z : c.Lbar, MulAut.conj z = 1 ↔ z ∈ Subgroup.center c.Lbar := by
    intro z
    constructor
    · intro h
      refine Subgroup.mem_center_iff.mpr (fun w => ?_)
      have hw := congrArg (fun f : MulAut c.Lbar => f w) h
      have hw' : z * w = w * z := by
        calc z * w = (z * w * z⁻¹) * z := by group
          _ = w * z := by rw [show z * w * z⁻¹ = w from by simpa [MulAut.conj_apply] using hw]
      exact hw'.symm
    · intro hz
      ext w
      rw [MulAut.conj_apply, MulAut.one_apply]
      calc z * w * z⁻¹ = (w * z) * z⁻¹ := by rw [Subgroup.mem_center_iff.mp hz w]
        _ = w := by group
  have hφ_eq (x : ↥D.M) (hxL : (x : G) ∈ c.L) :
      phiOf_wPL2 c x = MulAut.conj (QuotientGroup.mk (s := O) ⟨x.1, hxL⟩) := by
    rw [phiOf_wPL2, CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M
      c.le_normalizer_L x.2 hxL]
  have hBcard : Nat.card ↥B = 3 ^ 4 := by
    let PLm : Subgroup ↥D.M := (P ⊓ c.L).subgroupOf D.M
    have hPLmCard : Nat.card ↥PLm = 3 ^ 5 := by
      have h := card_PL_wPL2 c hON hP
      rw [← h]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((inf_le_left : P ⊓ c.L ≤ P).trans hP.le)).toEquiv
    have hkerEq : PLm ⊓ (phiOf_wPL2 c).ker = (zSub P c.L).subgroupOf D.M := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨hxPLm, hxker⟩
        have hxPL : (x : G) ∈ P ⊓ c.L := Subgroup.mem_subgroupOf.mp hxPLm
        have hxL : (x : G) ∈ c.L := hxPL.2
        refine ⟨hxPL, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        have hφ1 : phiOf_wPL2 c x = 1 := hxker
        have hcen : QuotientGroup.mk (s := O) ⟨x.1, hxL⟩ ∈
            Subgroup.center c.Lbar := by
          rw [← hconj_one_iff, ← hφ_eq x hxL]
          exact hφ1
        exact ((mem_center_lbar_iff_wPL2 c hON hP hxPL).mp hcen).2
      · intro hxz
        have hxPL : (x : G) ∈ P ⊓ c.L := hxz.1
        refine ⟨Subgroup.mem_subgroupOf.mpr hxPL, ?_⟩
        have hcen : QuotientGroup.mk (s := O) ⟨x.1, hxPL.2⟩ ∈
            Subgroup.center c.Lbar :=
          (mem_center_lbar_iff_wPL2 c hON hP hxPL).mpr hxz
        rw [MonoidHom.mem_ker, hφ_eq x hxPL.2, hconj_one_iff]
        exact hcen
    have hinfKerCard : Nat.card ↥(PLm ⊓ (phiOf_wPL2 c).ker) = 3 := by
      rw [hkerEq]
      have hzle : zSub P c.L ≤ D.M :=
        (inf_le_left.trans inf_le_left).trans hP.le
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv]
      exact c.card_inf_centralizer_of_onan hON hP
    have hmul := CFSG.Walter.W67.card_eq_card_map_mul_card_inf_ker (phiOf_wPL2 c) PLm
    change Nat.card ↥PLm = Nat.card ↥B * Nat.card ↥(PLm ⊓ (phiOf_wPL2 c).ker) at hmul
    rw [hPLmCard, hinfKerCard] at hmul
    have : Nat.card ↥B * 3 = 3 ^ 5 := hmul.symm
    omega
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar :=
    isHatON_lbar_wPL2 c hON
  have hA3 : IsPGroup 3 A := hP.isPGroup.comap_subtype.map (phiOf_wPL2 c)
  have hAcard : Nat.card ↥A ≤ 3 ^ 4 :=
    CFSG.HardMathSupport.Solomon.Coordinator.inputONAut_holds (X := c.Lbar) hHat A hA3
  have hBleA : B ≤ A := by
    refine Subgroup.map_mono ?_
    intro x hx
    exact (Subgroup.mem_subgroupOf.mp hx).1
  have hBA : B = A :=
    Subgroup.eq_of_le_of_card_ge hBleA (by rw [hBcard]; exact hAcard)
  exact hBA.symm

theorem P_eq_PL_sup_modCen_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    P = (P ⊓ c.L) ⊔ (P ⊓ modCenOf_wPL2 c) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro p hp
  have hpM : p ∈ D.M := hP.le hp
  let pm : ↥D.M := ⟨p, hpM⟩
  have hφp : phiOf_wPL2 c pm ∈ (P.subgroupOf D.M).map (phiOf_wPL2 c) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  rw [map_P_eq_map_PL_wPL2 c hON hP] at hφp
  obtain ⟨xm, hxmP, hxmφ⟩ := Subgroup.mem_map.mp hφp
  have hxPL : (xm : G) ∈ P ⊓ c.L := Subgroup.mem_subgroupOf.mp hxmP
  have hcP : p * (xm : G)⁻¹ ∈ P := P.mul_mem hp (P.inv_mem hxPL.1)
  have hcM : p * (xm : G)⁻¹ ∈ D.M :=
    D.M.mul_mem hpM (D.M.inv_mem (c.hyp81.1 hxPL.2))
  have hcmKer : (⟨p * (xm : G)⁻¹, hcM⟩ : ↥D.M) ∈ (phiOf_wPL2 c).ker := by
    rw [MonoidHom.mem_ker]
    have hprod : (⟨p * (xm : G)⁻¹, hcM⟩ : ↥D.M) = pm * xm⁻¹ := by
      ext
      rfl
    rw [hprod, map_mul, map_inv, hxmφ]
    group
  have hcmod : p * (xm : G)⁻¹ ∈ modCenOf_wPL2 c :=
    Subgroup.mem_map.mpr ⟨⟨p * (xm : G)⁻¹, hcM⟩, hcmKer, rfl⟩
  have hpt : p = (p * (xm : G)⁻¹) * xm := by group
  rw [hpt]
  have hcmem : p * (xm : G)⁻¹ ∈ (P ⊓ c.L) ⊔ (P ⊓ modCenOf_wPL2 c) :=
    Subgroup.mem_sup_right
      (show p * (xm : G)⁻¹ ∈ P ⊓ modCenOf_wPL2 c from Subgroup.mem_inf.mpr ⟨hcP, hcmod⟩)
  have htmem : (xm : G) ∈ (P ⊓ c.L) ⊔ (P ⊓ modCenOf_wPL2 c) :=
    Subgroup.mem_sup_left
      (show (xm : G) ∈ P ⊓ c.L from Subgroup.mem_inf.mpr ⟨hxPL.1, hxPL.2⟩)
  exact ((P ⊓ c.L) ⊔ (P ⊓ modCenOf_wPL2 c)).mul_mem hcmem htmem

theorem modCen_centralizes_PL_wPL2 (c : Ctx82E3 D)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∀ x ∈ P ⊓ modCenOf_wPL2 c, ∀ y ∈ P ⊓ c.L, x * y = y * x := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  intro x hx y hy
  obtain ⟨xm, hxmker, hxmval⟩ := Subgroup.mem_map.mp hx.2
  have hxM : x ∈ D.M := hP.le hx.1
  have hyL : y ∈ c.L := hy.2
  have hxyL : x * y * x⁻¹ ∈ c.L :=
    (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hxM) y).mp hyL
  have hφx : phiOf_wPL2 c xm = 1 := hxmker
  have hmap : π ⟨x * y * x⁻¹, hxyL⟩ = π ⟨y, hyL⟩ := by
    have h := congrArg (fun f : MulAut c.Lbar =>
      f (QuotientGroup.mk (s := O) ⟨y, hyL⟩)) hφx
    simp only [MulAut.one_apply] at h
    change (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L xm)
      (QuotientGroup.mk (s := O) ⟨y, hyL⟩) =
        QuotientGroup.mk (s := O) ⟨y, hyL⟩ at h
    rw [CFSG.GroupTheory.conjModPCore_mk] at h
    change QuotientGroup.mk (s := O) ⟨x * y * x⁻¹, hxyL⟩ =
      QuotientGroup.mk (s := O) ⟨y, hyL⟩
    rw [← h]
    apply congrArg π
    apply Subtype.ext
    dsimp
    have hxmval' : (xm : G) = x := hxmval
    rw [hxmval']
  have hcommL : x * y * x⁻¹ * y⁻¹ ∈ c.L :=
    c.L.mul_mem hxyL (c.L.inv_mem hyL)
  have hmemO : (⟨x * y * x⁻¹, hxyL⟩ * (⟨y, hyL⟩ : ↥c.L)⁻¹) ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    change π (⟨x * y * x⁻¹, hxyL⟩ * (⟨y, hyL⟩ : ↥c.L)⁻¹) = 1
    rw [map_mul, map_inv, hmap, mul_inv_cancel]
  have hmemOG : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
    Subgroup.mem_map.mpr ⟨⟨x * y * x⁻¹ * y⁻¹, hcommL⟩, hmemO, rfl⟩
  have hmemP : x * y * x⁻¹ * y⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hx.1 (hy.1)) (P.inv_mem hx.1)) (P.inv_mem hy.1)
  have hPdisjO : P ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ := by
    have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P _ hP.isPGroup hO2).eq_bot
  have hbot : x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hPdisjO]
    exact ⟨hmemP, hmemOG⟩
  have hcomm : x * y * x⁻¹ * y⁻¹ = 1 := by simpa using hbot
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hcomm, one_mul]

theorem PL_le_normalizer_modCen_wPL2 (c : Ctx82E3 D)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    (P ⊓ c.L) ≤ Subgroup.normalizer ((P ⊓ modCenOf_wPL2 c : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro t ht x hx
  have hcomm := modCen_centralizes_PL_wPL2 c hP x hx t ht
  rw [show t * x * t⁻¹ = x by rw [← hcomm]; group]
  exact hx

theorem inf_centralizer_eq_sup_modCen_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {a : G}
    (ha : a ∈ P ⊓ c.L) :
    P ⊓ cenOf_wPL2 a = ((P ⊓ c.L) ⊓ cenOf_wPL2 a) ⊔ (P ⊓ modCenOf_wPL2 c) := by
  have hC0cent : P ⊓ modCenOf_wPL2 c ≤ cenOf_wPL2 a := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact modCen_centralizes_PL_wPL2 c hP x hx a ha
  have hPLnormC0 := PL_le_normalizer_modCen_wPL2 c hP
  refine le_antisymm ?_ ?_
  · intro p hp
    have hpP : p ∈ (P ⊓ c.L) ⊔ (P ⊓ modCenOf_wPL2 c) := by
      rw [← P_eq_PL_sup_modCen_wPL2 c hON hP]
      exact hp.1
    have hpPprod : p ∈ ((P ⊓ c.L : Subgroup G) : Set G) *
        ((P ⊓ modCenOf_wPL2 c : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (P ⊓ c.L)
        (P ⊓ modCenOf_wPL2 c) hPLnormC0]
      exact hpP
    rcases hpPprod with ⟨u, hu, v, hv, huv⟩
    have hvcent : v ∈ cenOf_wPL2 a := hC0cent hv
    have hucent : u ∈ cenOf_wPL2 a := by
      have hu_eq : u = p * v⁻¹ := by rw [← huv]; group
      rw [hu_eq]
      exact (cenOf_wPL2 a).mul_mem hp.2 ((cenOf_wPL2 a).inv_mem hvcent)
    have hHnorm : ((P ⊓ c.L) ⊓ cenOf_wPL2 a) ≤
        Subgroup.normalizer ((P ⊓ modCenOf_wPL2 c : Subgroup G) : Set G) :=
      inf_le_left.trans hPLnormC0
    have hmemprod : p ∈ (((P ⊓ c.L) ⊓ cenOf_wPL2 a : Subgroup G) : Set G) *
        ((P ⊓ modCenOf_wPL2 c : Subgroup G) : Set G) :=
      ⟨u, Subgroup.mem_inf.mpr ⟨hu, hucent⟩, v, hv, huv⟩
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right ((P ⊓ c.L) ⊓ cenOf_wPL2 a)
      (P ⊓ modCenOf_wPL2 c) hHnorm] at hmemprod
    exact hmemprod
  · refine sup_le ?_ ?_
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · exact le_inf inf_le_left hC0cent

theorem card_inf_centralizer_P_eq_wPL2
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {a b : G} (ha : a ∈ P ⊓ c.L) (haZ : a ∉ zSub P c.L)
    (hb : b ∈ P ⊓ c.L) (hbZ : b ∉ zSub P c.L) :
    Nat.card ↥(P ⊓ cenOf_wPL2 a) = Nat.card ↥(P ⊓ cenOf_wPL2 b) := by
  classical
  let A : Subgroup G := (P ⊓ c.L) ⊓ cenOf_wPL2 a
  let B : Subgroup G := (P ⊓ c.L) ⊓ cenOf_wPL2 b
  let C0 : Subgroup G := P ⊓ modCenOf_wPL2 c
  have hcardA : Nat.card ↥A = 81 := by
    simpa [A] using card_inf_centralizer_PL_wPL2 c hON hP ha haZ
  have hcardB : Nat.card ↥B = 81 := by
    simpa [B] using card_inf_centralizer_PL_wPL2 c hON hP hb hbZ
  have hPLnormC0 := PL_le_normalizer_modCen_wPL2 c hP
  have hnormA : A ≤ Subgroup.normalizer (C0 : Set G) := by
    simpa [A, C0] using inf_le_left.trans hPLnormC0
  have hnormB : B ≤ Subgroup.normalizer (C0 : Set G) := by
    simpa [B, C0] using inf_le_left.trans hPLnormC0
  have hsupA : P ⊓ cenOf_wPL2 a = A ⊔ C0 := by
    simpa [A, C0] using inf_centralizer_eq_sup_modCen_wPL2 c hON hP ha
  have hsupB : P ⊓ cenOf_wPL2 b = B ⊔ C0 := by
    simpa [B, C0] using inf_centralizer_eq_sup_modCen_wPL2 c hON hP hb
  have hinfA : A ⊓ C0 = (P ⊓ c.L) ⊓ C0 := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      exact (Subgroup.mem_centralizer_singleton_iff (G := G) (g := a) (k := x)).mpr
        (modCen_centralizes_PL_wPL2 c hP x hx.2 a ha)
  have hinfB : B ⊓ C0 = (P ⊓ c.L) ⊓ C0 := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      exact (Subgroup.mem_centralizer_singleton_iff (G := G) (g := b) (k := x)).mpr
        (modCen_centralizes_PL_wPL2 c hP x hx.2 b hb)
  have hmulA : Nat.card ↥(P ⊓ cenOf_wPL2 a) * Nat.card ↥(A ⊓ C0) =
      Nat.card ↥A * Nat.card ↥C0 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := A) (K := C0) hnormA
    rw [← hsupA] at h
    exact h
  have hmulB : Nat.card ↥(P ⊓ cenOf_wPL2 b) * Nat.card ↥(B ⊓ C0) =
      Nat.card ↥B * Nat.card ↥C0 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := B) (K := C0) hnormB
    rw [← hsupB] at h
    exact h
  have hk : Nat.card ↥(A ⊓ C0) = Nat.card ↥(B ⊓ C0) := by rw [hinfA, hinfB]
  rw [← hk] at hmulB
  have hkpos : 0 < Nat.card ↥(A ⊓ C0) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hkpos ?_
  calc Nat.card ↥(P ⊓ cenOf_wPL2 a) * Nat.card ↥(A ⊓ C0)
      = Nat.card ↥A * Nat.card ↥C0 := hmulA
    _ = Nat.card ↥B * Nat.card ↥C0 := by rw [hcardA, hcardB]
    _ = Nat.card ↥(P ⊓ cenOf_wPL2 b) * Nat.card ↥(A ⊓ C0) := hmulB.symm

theorem exists_conj_zpowers_of_mem_wPL2
    (hK6 : K6ONanClasses) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {e y : G} (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    (hy : y ∈ P ⊓ c.L) (hy3 : orderOf y = 3) (hyZ : y ∉ zSub P c.L) :
    ∃ l ∈ c.L, l * e * l⁻¹ = y ∨ l * e * l⁻¹ = y⁻¹ := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hPdisjO : P ⊓ O = ⊥ := by
    have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P O hP.isPGroup hO2).eq_bot
  have he1 : e ≠ 1 := by
    intro h
    rw [h] at he3
    simp at he3
  have hy1 : y ≠ 1 := by
    intro h
    rw [h] at hy3
    simp at hy3
  have hπe_order : orderOf (π ⟨e, he.2⟩) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, show (⟨e, he.2⟩ : ↥c.L) ^ 3 = 1 by
        ext
        rw [← he3]
        exact pow_orderOf_eq_one e]
      simp
    · intro h1
      have hO : (⟨e, he.2⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L :=
        (QuotientGroup.eq_one_iff (⟨e, he.2⟩ : ↥c.L)).mp h1
      have heO : e ∈ O := Subgroup.mem_map.mpr ⟨⟨e, he.2⟩, hO, rfl⟩
      have hbot : e ∈ (⊥ : Subgroup G) := by
        rw [← hPdisjO]
        exact ⟨he.1, heO⟩
      exact he1 (by simpa using hbot)
  have hπy_order : orderOf (π ⟨y, hy.2⟩) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, show (⟨y, hy.2⟩ : ↥c.L) ^ 3 = 1 by
        ext
        rw [← hy3]
        exact pow_orderOf_eq_one y]
      simp
    · intro h1
      have hO : (⟨y, hy.2⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L :=
        (QuotientGroup.eq_one_iff (⟨y, hy.2⟩ : ↥c.L)).mp h1
      have hyO : y ∈ O := Subgroup.mem_map.mpr ⟨⟨y, hy.2⟩, hO, rfl⟩
      have hbot : y ∈ (⊥ : Subgroup G) := by
        rw [← hPdisjO]
        exact ⟨hy.1, hyO⟩
      exact hy1 (by simpa using hbot)
  have hπe_center : π ⟨e, he.2⟩ ∉ Subgroup.center c.Lbar := by
    intro hc
    exact heZ ((mem_center_lbar_iff_wPL2 c hON hP he).mp hc)
  have hπy_center : π ⟨y, hy.2⟩ ∉ Subgroup.center c.Lbar := by
    intro hc
    exact hyZ ((mem_center_lbar_iff_wPL2 c hON hP hy).mp hc)
  obtain ⟨g, hg⟩ := hK6 c.Lbar hON (π ⟨e, he.2⟩) (π ⟨y, hy.2⟩)
    hπe_order hπe_center hπy_order hπy_center
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥c.L) g
  let x : G := l * e * l⁻¹
  have hxL : x ∈ c.L := c.L.mul_mem (c.L.mul_mem l.2 he.2) (c.L.inv_mem l.2)
  have hπx : π ⟨x, hxL⟩ = π ⟨y, hy.2⟩ := by
    have hg' : π l * π ⟨e, he.2⟩ * (π l)⁻¹ = π ⟨y, hy.2⟩ := by
      have h := hg
      rw [← hl] at h
      exact h
    have hsub : (⟨x, hxL⟩ : ↥c.L) = l * ⟨e, he.2⟩ * l⁻¹ := by
      apply Subtype.ext
      rfl
    calc π ⟨x, hxL⟩ = π l * π ⟨e, he.2⟩ * (π l)⁻¹ := by
          rw [hsub, map_mul, map_mul, map_inv]
      _ = π ⟨y, hy.2⟩ := hg'
  have hxyO : (⟨y, hy.2⟩ : ↥c.L) * (⟨x, hxL⟩ : ↥c.L)⁻¹ ∈
      CFSG.Open.pCore 2 ↥c.L := by
    rw [← QuotientGroup.eq_one_iff]
    change π ((⟨y, hy.2⟩ : ↥c.L) * (⟨x, hxL⟩ : ↥c.L)⁻¹) = 1
    rw [map_mul, map_inv, hπx, mul_inv_cancel]
  let H : Subgroup G := Subgroup.zpowers x ⊔ O
  have hx3 : orderOf x = 3 := by
    simpa [x, MulAut.conj_apply, he3] using (MulAut.conj (l : G)).orderOf_eq e
  have hy3' : orderOf y = 3 := hy3
  have hxH : x ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyOG : y * x⁻¹ ∈ O := by
    refine Subgroup.mem_map.mpr ⟨(⟨y, hy.2⟩ : ↥c.L) * (⟨x, hxL⟩ : ↥c.L)⁻¹, hxyO, ?_⟩
    rfl
  have hyH : y ∈ H := by
    have hy_eq : y = (y * x⁻¹) * x := by group
    rw [hy_eq]
    exact H.mul_mem (Subgroup.mem_sup_right hyOG) hxH
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num)
  have hyP : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy3']; norm_num)
  have hxnormO : Subgroup.zpowers x ≤ Subgroup.normalizer (O : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    exact (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)) hxL
  have hdisjxO : Subgroup.zpowers x ⊓ O = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ O hxP hO2).eq_bot
  have hHcard : Nat.card H = 3 * Nat.card O := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Subgroup.zpowers x) (K := O) hxnormO
    rw [hdisjxO, Subgroup.card_bot, mul_one, Nat.card_zpowers, hx3] at h
    exact h
  have hnotdvdO : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2 Nat.prime_three (by norm_num)
  have hxSyl : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers x) H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hxP, ?_⟩
    have hmul := Subgroup.relIndex_mul_card (H := Subgroup.zpowers x) (K := H)
    rw [inf_eq_left.mpr le_sup_left, Nat.card_zpowers, hx3, hHcard] at hmul
    have hidx : (Subgroup.zpowers x).relIndex H = Nat.card O := by
      have : (Subgroup.zpowers x).relIndex H * 3 = Nat.card O * 3 := by
        rw [hmul]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
    rw [hidx]
    exact hnotdvdO
  have hySyl : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers y) H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨Subgroup.zpowers_le.mpr hyH, hyP, ?_⟩
    have hmul := Subgroup.relIndex_mul_card (H := Subgroup.zpowers y) (K := H)
    rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hyH), Nat.card_zpowers, hy3', hHcard] at hmul
    have hidx : (Subgroup.zpowers y).relIndex H = Nat.card O := by
      have : (Subgroup.zpowers y).relIndex H * 3 = Nat.card O * 3 := by
        rw [hmul]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
    rw [hidx]
    exact hnotdvdO
  obtain ⟨k, hkH, hkconj⟩ := hxSyl.exists_mem_conj hySyl
  have hky : k⁻¹ * y * k ∈ Subgroup.zpowers x :=
    (hkconj y).mp (Subgroup.mem_zpowers y)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hky
  have hzk3 : orderOf (k * x * k⁻¹) = 3 := by
    simpa [MulAut.conj_apply, hx3] using (MulAut.conj (k : G)).orderOf_eq x
  have hzpow : (k * x * k⁻¹) ^ m = k * x ^ m * k⁻¹ := by
    simpa [MulAut.conj_apply] using (map_zpow (MulAut.conj (k : G)).toMonoidHom x m)
  have hzy : y = (k * x * k⁻¹) ^ m := by
    rw [hzpow]
    rw [hm]
    group
  have hy_mem_z : y ∈ Subgroup.zpowers (k * x * k⁻¹) := by
    rw [hzy]
    exact Subgroup.zpow_mem (Subgroup.zpowers (k * x * k⁻¹)) (Subgroup.mem_zpowers _) m
  have hcases := CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
    hzk3 hy_mem_z hy1
  have hHleL : H ≤ c.L := by
    refine sup_le ?_ (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L)
    exact Subgroup.zpowers_le.mpr hxL
  have hkL : k ∈ c.L := hHleL hkH
  have hklL : k * l ∈ c.L := c.L.mul_mem hkL l.2
  have hconj_eq : (k * l) * e * (k * l)⁻¹ = k * x * k⁻¹ := by
    dsimp only [x]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rcases hcases with hzy_eq | hzy_inv
  · exact ⟨k * l, hklL, Or.inl (by rw [hconj_eq]; exact hzy_eq.symm)⟩
  · refine ⟨k * l, hklL, Or.inr ?_⟩
    have hz_eq_inv : k * x * k⁻¹ = y⁻¹ := by
      rw [hzy_inv]
      group
    rw [hconj_eq, hz_eq_inv]

theorem pcore_centralizer_le_theta_P1'
    (hK2 : K2ONanCentralizer) (hK6 : K6ONanClasses) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ cenOf_wPL2 e) (cenOf_wPL2 e) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy, hy3, hyZ, hTy, -⟩ :=
    exists_sylow_centralizer_of_gamma' hK6 c hON h7 hP hNZ e he he3 heZ
  have hcardP : Nat.card ↥(P ⊓ cenOf_wPL2 e) = Nat.card ↥(P ⊓ cenOf_wPL2 y) :=
    card_inf_centralizer_P_eq_wPL2 c hON hP he heZ hy hyZ
  obtain ⟨l, -, hcases⟩ :=
    exists_conj_zpowers_of_mem_wPL2 hK6 c hON hP he he3 heZ hy hy3 hyZ
  have hcardcen : Nat.card ↥(cenOf_wPL2 e) = Nat.card ↥(cenOf_wPL2 y) := by
    rcases hcases with h | h
    · exact CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj
        (isConj_iff.mpr ⟨l, h⟩)
    · have h1 := CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj
        (isConj_iff.mpr ⟨l, h⟩)
      have h2 : Nat.card ↥(cenOf_wPL2 y⁻¹) = Nat.card ↥(cenOf_wPL2 y) := by
        have hcen : cenOf_wPL2 y⁻¹ = cenOf_wPL2 y := by
          ext x
          rw [Subgroup.mem_centralizer_singleton_iff,
            Subgroup.mem_centralizer_singleton_iff]
          exact ⟨fun h => Commute.inv_right_iff.mp h, Commute.inv_right⟩
        rw [hcen]
      rw [h1, h2]
  have hcardExp : Nat.card ↥(P ⊓ cenOf_wPL2 e) =
      3 ^ (Nat.card ↥(cenOf_wPL2 e)).factorization 3 := by
    rw [hcardP, hTy.card_eq, hcardcen]
  exact CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right hcardExp

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
