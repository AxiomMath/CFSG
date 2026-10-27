module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveBExist
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwoP
public import CFSG.Quasithin.Vol2.Ch10SecEE3Prod
public import CFSG.LocalAnalysis.WeakClosure81.W15SixC
public import CFSG.Quasithin.Background.RonanG72Classical
public import CFSG.LieType.SuzukiSubgroups.Facts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagProducts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinInv
import CFSG.Quasithin.H13.NQRigidB2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_fix_iff rhoL_inner)
open CFSG.GroupTheory (conjModPCore)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barImage_inf_eq_bot_of_center_eq_bot {I L K : Subgroup G} (hL : L ∈ calC I)
    (hK : K ∈ calC I) (hne : L ≠ K) (hZ : Subgroup.center ↥(barImage I L) = ⊥) :
    barImage I L ⊓ barImage I K = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxcenter : (⟨x, hx.1⟩ : ↥(barImage I L)) ∈
      Subgroup.center ↥(barImage I L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (uc22p22l_barImage_commute hL hK hne y y.2 x hx.2)
  rw [hZ, Subgroup.mem_bot] at hxcenter
  exact Subtype.ext_iff.mp hxcenter

noncomputable def bar2SquareHom {I L K : Subgroup G}
    (hsup : barImage I L ⊔ barImage I K = ⊤)
    (hcomm : ∀ a ∈ barImage I L, ∀ b ∈ barImage I K, a * b = b * a)
    (hdisj : barImage I L ⊓ barImage I K = ⊥) :
    ↥(barImage I L) × ↥(barImage I K) ≃* Bar2 I :=
  (CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcomm hdisj).trans
    ((MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv)

noncomputable def bar2SquareEquiv {I L K : Subgroup G}
    (hsup : barImage I L ⊔ barImage I K = ⊤)
    (hcomm : ∀ a ∈ barImage I L, ∀ b ∈ barImage I K, a * b = b * a)
    (hdisj : barImage I L ⊓ barImage I K = ⊥) :
    Bar2 I ≃* ↥(barImage I L) × ↥(barImage I K) :=
  (bar2SquareHom hsup hcomm hdisj).symm

theorem bar2SquareHom_apply {I L K : Subgroup G}
    (hsup : barImage I L ⊔ barImage I K = ⊤)
    (hcomm : ∀ a ∈ barImage I L, ∀ b ∈ barImage I K, a * b = b * a)
    (hdisj : barImage I L ⊓ barImage I K = ⊥)
    (p : ↥(barImage I L) × ↥(barImage I K)) :
    bar2SquareHom hsup hcomm hdisj p = ((p.1 : Bar2 I) * (p.2 : Bar2 I)) := by
  simp [bar2SquareHom, CFSG.Quasithin.Vol2.Ch10.SecE.coe_prodEquivSup]

theorem bar2SquareEquiv_apply_fst {I L K : Subgroup G}
    (hsup : barImage I L ⊔ barImage I K = ⊤)
    (hcomm : ∀ a ∈ barImage I L, ∀ b ∈ barImage I K, a * b = b * a)
    (hdisj : barImage I L ⊓ barImage I K = ⊥) (x : ↥(barImage I L)) :
    bar2SquareEquiv hsup hcomm hdisj (x : Bar2 I) = (x, 1) := by
  rw [bar2SquareEquiv, MulEquiv.symm_apply_eq]
  rw [bar2SquareHom_apply]
  simp

theorem bar2SquareEquiv_apply_snd {I L K : Subgroup G}
    (hsup : barImage I L ⊔ barImage I K = ⊤)
    (hcomm : ∀ a ∈ barImage I L, ∀ b ∈ barImage I K, a * b = b * a)
    (hdisj : barImage I L ⊓ barImage I K = ⊥) (x : ↥(barImage I K)) :
    bar2SquareEquiv hsup hcomm hdisj (x : Bar2 I) = (1, x) := by
  rw [bar2SquareEquiv, MulEquiv.symm_apply_eq]
  rw [bar2SquareHom_apply]
  simp

theorem finite_of_isL2 {A : Type} [Group A] {n : ℕ} (h : IsL2 A n) : Finite A :=
  CFSG.LieType.Simplicity.finite_of_statedClassicalModel
    ((CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).1 h)

theorem pRank_top_isL2_three (A : Type) [Group A] [Finite A] (hA : IsL2 A 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup A) = 1 := by
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup A) ≤ 1 := by
    have hS : CFSG.Open.StatedClassicalModel A .PSL 2 2 3 :=
      (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).1 hA
    exact CFSG.Quasithin.A318P.pRank_le_one_psl_two_even (by norm_num) hS
      Nat.prime_three (by norm_num)
  have hpos : 0 < CFSG.Open.pRank 3 (⊤ : Subgroup A) := by
    by_contra h
    have h0 : CFSG.Open.pRank 3 (⊤ : Subgroup A) = 0 := Nat.eq_zero_of_not_pos h
    exact (CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three h0)
      (by rw [Subgroup.card_top, card_of_isL2 hA]; norm_num)
  omega

theorem pRank_top_isSz_five (B : Type) [Group B] [Finite B] (hB : IsSz B 5) :
    CFSG.Open.pRank 5 (⊤ : Subgroup B) = 1 := by
  have hle : CFSG.Open.pRank 5 (⊤ : Subgroup B) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki
      (CFSG.Blueprint.LieModel.suzukiModel hB).2 Nat.prime_five (by norm_num)
  have hpos : 0 < CFSG.Open.pRank 5 (⊤ : Subgroup B) := by
    by_contra h
    have h0 : CFSG.Open.pRank 5 (⊤ : Subgroup B) = 0 := Nat.eq_zero_of_not_pos h
    exact (CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_five h0)
      (by rw [Subgroup.card_top, CFSG.Quasithin.card_of_isSz
        (CFSG.Blueprint.LieModel.suzukiModel hB).2]; norm_num)
  omega

theorem pRank_two_of_isL2Square_three {A : Type} [Group A] [Finite A]
    (h : IsL2Square A 3) : CFSG.Open.pRank 3 (⊤ : Subgroup A) = 2 := by
  obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := h
  have : Finite P := finite_of_isL2 hP
  have : Finite Q := finite_of_isL2 hQ
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.Quasithin.H13.NQBlock.pRank_prod_eq Nat.prime_three,
    CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_isL2_three P hP,
    pRank_top_isL2_three Q hQ]

theorem pRank_two_of_isSzSquare_five {A : Type} [Group A] [Finite A]
    (h : IsSzSquare A 5) : CFSG.Open.pRank 5 (⊤ : Subgroup A) = 2 := by
  obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := h
  have : Finite P := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hP
  have : Finite Q := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hQ
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e]
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.Quasithin.H13.NQBlock.pRank_prod_eq Nat.prime_five,
    CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_isSz_five P hP,
    pRank_top_isSz_five Q hQ]

theorem pCoreOf_le_centOverO2 (D : Data G) {X : Subgroup G} (hXM : X ≤ D.M) :
    CFSG.Open.pCoreOf 2 X ≤ F08.CentOverO2 D.M X := by
  intro q hq
  have hqX : q ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hq
  rw [mem_centOverO2_iff]
  refine ⟨hXM hqX, fun l hl => ?_⟩
  have hq' : q⁻¹ ∈ CFSG.Open.pCoreOf 2 X := (CFSG.Open.pCoreOf 2 X).inv_mem hq
  have hlql : l * q⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hl) q⁻¹).1 hq'
  have heq : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
  rw [heq]
  exact (CFSG.Open.pCoreOf 2 X).mul_mem hq hlql

theorem ker_conjModPCore_eq_centOverO2 (D : Data G) {X N : Subgroup G}
    (hXM : X ≤ D.M) (hN : N = X ⊔ F08.CentOverO2 D.M X)
    (hNX : N ≤ Subgroup.normalizer (X : Set G)) :
    (conjModPCore 2 X N hNX).ker.map N.subtype = F08.CentOverO2 D.M X := by
  have hCM : F08.CentOverO2 D.M X ≤ D.M := fun x hx => (mem_centOverO2_iff.mp hx).1
  have hND : N ≤ D.M := hN ▸ sup_le hXM hCM
  ext n
  rw [CFSG.GroupTheory.mem_map_ker_conjModPCore_iff, mem_centOverO2_iff]
  constructor
  · rintro ⟨hnN, hcomm⟩
    exact ⟨hND hnN, hcomm⟩
  · rintro ⟨hnM, hcomm⟩
    refine ⟨?_, hcomm⟩
    rw [hN]
    exact Subgroup.mem_sup_right (mem_centOverO2_iff.mpr ⟨hnM, hcomm⟩)

theorem range_conjModPCore_eq_inner (D : Data G) {X N : Subgroup G}
    (hXM : X ≤ D.M) (hN : N = X ⊔ F08.CentOverO2 D.M X)
    (hNX : N ≤ Subgroup.normalizer (X : Set G)) :
    (conjModPCore 2 X N hNX).range =
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
  have hXN : X ≤ N := hN ▸ le_sup_left
  have hCN : F08.CentOverO2 D.M X ≤ N := hN ▸ le_sup_right
  have hsup : X.subgroupOf N ⊔ (F08.CentOverO2 D.M X).subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXN hCN, show X ⊔ F08.CentOverO2 D.M X = N from hN.symm,
      Subgroup.subgroupOf_self]
  have hXmap : (X.subgroupOf N).map (conjModPCore 2 X N hNX) =
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
    apply le_antisymm
    · intro f hf
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      rw [show conjModPCore 2 X N hNX x = MulAut.conj (QuotientGroup.mk ⟨(x : G), hxX⟩) from
        CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 X N hNX (m := (x : G)) x.2 hxX]
      exact ⟨QuotientGroup.mk ⟨(x : G), hxX⟩, rfl⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      refine Subgroup.mem_map.mpr ⟨⟨x, hXN x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, ?_⟩
      exact CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 X N hNX (m := (x : G))
        (hXN x.2) x.2
  have hCmap : ((F08.CentOverO2 D.M X).subgroupOf N).map (conjModPCore 2 X N hNX) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro f hf
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hf
    have hcC : (c : G) ∈ F08.CentOverO2 D.M X := Subgroup.mem_subgroupOf.mp hc
    have hker : (c : G) ∈ (conjModPCore 2 X N hNX).ker.map N.subtype := by
      rw [CFSG.GroupTheory.mem_map_ker_conjModPCore_iff]
      exact ⟨c.2, (mem_centOverO2_iff.mp hcC).2⟩
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hker
    have hd1 : conjModPCore 2 X N hNX d = 1 := MonoidHom.mem_ker.mp hd
    have hdeq : d = c := Subtype.ext hdc
    rw [Subgroup.mem_bot, ← hdeq]
    exact hd1
  have hrange : (conjModPCore 2 X N hNX).range = (X.subgroupOf N).map (conjModPCore 2 X N hNX) ⊔
      ((F08.CentOverO2 D.M X).subgroupOf N).map (conjModPCore 2 X N hNX) := by
    rw [MonoidHom.range_eq_map, ← hsup, Subgroup.map_sup]
  rw [hrange, hXmap, hCmap, sup_bot_eq]

theorem pRank_sup_centOverO2_le_add (D : Data G) {X : Subgroup G} {p : ℕ}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hp : p.Prime) (hZ : Subgroup.center (Bar2 X) = ⊥)
    (hrankX : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) = 2) :
    CFSG.Open.pRank p (X ⊔ F08.CentOverO2 D.M X) ≤
      2 + CFSG.Open.pRank p (F08.CentOverO2 D.M X) := by
  let N : Subgroup G := X ⊔ F08.CentOverO2 D.M X
  let hNX : N ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer (fun x hx => hMX (mem_centOverO2_iff.mp hx).1)
  have h1 := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range 2 p hp X N hNX
  have hker : (conjModPCore 2 X N hNX).ker.map N.subtype = F08.CentOverO2 D.M X :=
    ker_conjModPCore_eq_centOverO2 D hXM rfl hNX
  have hrange : (conjModPCore 2 X N hNX).range =
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) :=
    range_conjModPCore_eq_inner D hXM rfl hNX
  have hinner :
      CFSG.Open.pRank p (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X)) =
        CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) := by
    have h := CFSG.Quasithin.H13.NQRigid.pRank_inner_eq (J := Bar2 X) hp
      (by rw [hZ, Subgroup.card_bot]; exact hp.not_dvd_one)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top] at h
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X))]
    exact h
  rw [hker, hrange, hinner, hrankX] at h1
  rw [add_comm] at h1
  change CFSG.Open.pRank p N ≤ 2 + CFSG.Open.pRank p (F08.CentOverO2 D.M X)
  exact h1

theorem center_eq_bot_of_isSz_five {P : Type} [Group P] [Finite P] (h : IsSz P 5) :
    Subgroup.center P = ⊥ := by
  have : IsSimpleGroup P :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_lieModel_isSimple_twistedB2 h
  refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
  intro hc
  have : IsMulCommutative P := hc
  have hp := CFSG.OrderReductions.Helpers.prime_card_of_simple_commutative P
  rw [CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel h).2] at hp
  norm_num at hp

theorem center_eq_bot_of_isL2Square_three {A : Type} [Group A] [Finite A]
    (h : IsL2Square A 3) : Subgroup.center A = ⊥ := by
  obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := h
  have : Finite P := finite_of_isL2 hP
  have : Finite Q := finite_of_isL2 hQ
  have hPQ : Subgroup.center (P × Q) = ⊥ := by
    rw [Subgroup.center_prod, center_eq_bot_of_lieModel_psl2 hP,
      center_eq_bot_of_lieModel_psl2 hQ, Subgroup.bot_prod_bot]
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : e z ∈ Subgroup.center (P × Q) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, hz w']
  rw [hPQ, Subgroup.mem_bot] at hz'
  exact e.injective (by simpa using hz')

theorem center_eq_bot_of_isSzSquare_five {A : Type} [Group A] [Finite A]
    (h : IsSzSquare A 5) : Subgroup.center A = ⊥ := by
  obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := h
  have : Finite P := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hP
  have : Finite Q := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hQ
  have hPQ : Subgroup.center (P × Q) = ⊥ := by
    rw [Subgroup.center_prod, center_eq_bot_of_isSz_five hP, center_eq_bot_of_isSz_five hQ,
      Subgroup.bot_prod_bot]
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : e z ∈ Subgroup.center (P × Q) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, hz w']
  rw [hPQ, Subgroup.mem_bot] at hz'
  exact e.injective (by simpa using hz')

theorem exists_elemAbelian_lift_of_bar {X : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup (Bar2 X)) = 2) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨H, -, hHel, hHcard⟩ :=
    CFSG.SectionRank.exists_pRank hr.one_lt (⊤ : Subgroup (Bar2 X))
  have hHcard' : Nat.card ↥H = r ^ 2 := by
    rw [hHcard, hrank]
  have hHodd : Odd (Nat.card ↥H) := by
    rw [hHcard']
    exact (hr.odd_of_ne_two hr2).pow
  let Y : Type := ↥X
  let N : Subgroup Y := CFSG.pCore 2 Y
  have hN : IsPGroup 2 N := CFSG.pCore_isPGroup
  obtain ⟨K, hKcard, hKH, hKinj⟩ := CFSG.CGT.Timmesfeld75.osg_exists_lift N hN H hHodd
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  let φ : ↥K →* ↥H :=
    { toFun := fun k => ⟨π (k : Y), hKH k k.2⟩
      map_one' := by ext; simp [π]
      map_mul' := by intro a b; ext; simp [π, map_mul] }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hπ : π ((a : ↥K) : Y) = π ((b : ↥K) : Y) := congrArg Subtype.val hab
    have h1 : π (((a : ↥K) : Y)⁻¹ * (b : ↥K)) = 1 := by
      rw [map_mul, map_inv, hπ, inv_mul_cancel]
    have hmem : ((a : ↥K) : Y)⁻¹ * (b : ↥K) ∈ K := K.mul_mem (K.inv_mem a.2) b.2
    have heq := hKinj _ hmem h1
    apply Subtype.ext
    have := congrArg (fun y : Y => ((a : ↥K) : Y) * y) heq
    simpa using this.symm
  have hcardK : Nat.card ↥K = Nat.card ↥H := hKcard
  letI : Fintype ↥K := Fintype.ofFinite ↥K
  letI : Fintype ↥H := Fintype.ofFinite ↥H
  have hcard' : Fintype.card ↥K = Fintype.card ↥H := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard]
  let e₀ : ↥K ≃ ↥H := Fintype.equivOfCardEq hcard'
  have hφsurj : Function.Surjective φ :=
    (Finite.injective_iff_surjective_of_equiv e₀).mp hφinj
  have hφbij : Function.Bijective φ := ⟨hφinj, hφsurj⟩
  let e : ↥K ≃* ↥H := MulEquiv.ofBijective φ hφbij
  have hHtop : IsElemAbelian r (⊤ : Subgroup ↥H) := by
    simpa using hHel.subgroupOf H
  have hKtop : IsElemAbelian r (⊤ : Subgroup ↥K) := by
    have h := hHtop.map e.symm.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  refine ⟨K.map X.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
  · have hmap : (⊤ : Subgroup ↥K).map (X.subtype.comp K.subtype) = K.map X.subtype := by
      ext g
      constructor
      · rintro ⟨k, -, rfl⟩
        exact ⟨k, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, trivial, rfl⟩
    have h := hKtop.map (X.subtype.comp K.subtype)
    rwa [hmap] at h
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hKcard, hHcard']

theorem pRank_top_isL2_seven (A : Type) [Group A] [Finite A] (hA : IsL2 A 3) :
    CFSG.Open.pRank 7 (⊤ : Subgroup A) = 1 := by
  have hle : CFSG.Open.pRank 7 (⊤ : Subgroup A) ≤ 1 := by
    have hS : CFSG.Open.StatedClassicalModel A .PSL 2 2 3 :=
      (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).1 hA
    exact CFSG.Quasithin.A318P.pRank_le_one_psl_two_even (by norm_num) hS
      (by norm_num) (by norm_num)
  have hpos : 0 < CFSG.Open.pRank 7 (⊤ : Subgroup A) := by
    by_contra h
    have h0 : CFSG.Open.pRank 7 (⊤ : Subgroup A) = 0 := Nat.eq_zero_of_not_pos h
    exact (CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero (by norm_num : Nat.Prime 7) h0)
      (by rw [Subgroup.card_top, card_of_isL2 hA]; norm_num)
  omega

theorem pRank_top_isSz_thirtyone (B : Type) [Group B] [Finite B] (hB : IsSz B 5) :
    CFSG.Open.pRank 31 (⊤ : Subgroup B) = 1 := by
  have hle : CFSG.Open.pRank 31 (⊤ : Subgroup B) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki
      (CFSG.Blueprint.LieModel.suzukiModel hB).2 (by norm_num) (by norm_num)
  have hpos : 0 < CFSG.Open.pRank 31 (⊤ : Subgroup B) := by
    by_contra h
    have h0 : CFSG.Open.pRank 31 (⊤ : Subgroup B) = 0 := Nat.eq_zero_of_not_pos h
    exact (CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero (by norm_num : Nat.Prime 31) h0)
      (by rw [Subgroup.card_top, CFSG.Quasithin.card_of_isSz
        (CFSG.Blueprint.LieModel.suzukiModel hB).2]; norm_num)
  omega

theorem pRank_two_of_isL2Square_seven {A : Type} [Group A] [Finite A]
    (h : IsL2Square A 3) : CFSG.Open.pRank 7 (⊤ : Subgroup A) = 2 := by
  obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := h
  have : Finite P := finite_of_isL2 hP
  have : Finite Q := finite_of_isL2 hQ
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) e]
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.Quasithin.H13.NQBlock.pRank_prod_eq (by norm_num : Nat.Prime 7),
    CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_isL2_seven P hP,
    pRank_top_isL2_seven Q hQ]

theorem pRank_two_of_isSzSquare_thirtyone {A : Type} [Group A] [Finite A]
    (h : IsSzSquare A 5) : CFSG.Open.pRank 31 (⊤ : Subgroup A) = 2 := by
  obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := h
  have : Finite P := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hP
  have : Finite Q := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hQ
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 31) (by norm_num) e]
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.Quasithin.H13.NQBlock.pRank_prod_eq (by norm_num : Nat.Prime 31),
    CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_isSz_thirtyone P hP,
    pRank_top_isSz_thirtyone Q hQ]

theorem gap17_45_pRanCtxAt_of (D : Data G)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V₀ V : Subgroup G}
    (h1 : ∀ hV : Hyp125 D V₀ V, R17_1At D V₀ V hV)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34)
    (hK4 : Inputs1719.K_CartanRankLeThree) :
    Gap17_45_PRanCtxAt D V₀ V := by
  intro L X p n l r Ccart Dc Gamma x A₀ ctx h8100 hc
  classical
  obtain ⟨hLcal, hLne, hshapeN, hr, hrdvd, hpSig, -, -, hXprod, hMNX⟩ := h8100
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshapeN 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hrdvd
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hKdef
  have hXprod' : (X : Set G) = (L : Set G) * (K : Set G) := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hXprod
  have hLcal0 : L ∈ calC D.M := by simpa using hLcal 0
  have hLM : L ≤ D.M := s13_le_of_mem_calC hLcal0
  have hXeq : X = L ⊔ K := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz' : z ∈ (L : Set G) * (K : Set G) := by rwa [← hXprod']
      obtain ⟨a, ha, b, hb, rfl⟩ := hz'
      exact Subgroup.mul_mem_sup ha hb
    · refine sup_le ?_ ?_
      · intro a ha
        have h : a ∈ (L : Set G) * (K : Set G) := ⟨a, ha, 1, K.one_mem, by simp⟩
        change a ∈ (X : Set G)
        rw [hXprod']
        exact h
      · intro b hb
        have h : b ∈ (L : Set G) * (K : Set G) := ⟨1, L.one_mem, b, hb, by simp⟩
        change b ∈ (X : Set G)
        rw [hXprod']
        exact h
  have hLKne : L ≠ K := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hLne
  have hKconj : K ∈ conjSetOf D.M L := by
    rcases hc with h3 | h4
    · have h1' : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L := by
        simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h3.1
      have hmem : K ∈ ({L, K} : Set (Subgroup G)) := by simp
      rwa [h1'] at hmem
    · have h1' : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L := by
        simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h4.1
      have hmem : K ∈ ({L, K} : Set (Subgroup G)) := by simp
      rwa [h1'] at hmem
  have hKcalM : K ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hLcal0 hKconj
  obtain ⟨m, hmM, hmK⟩ := hKconj
  have hmK' : K = CFSG.Quasithin.conjSubgroup L m⁻¹ := by
    rw [hmK, CFSG.Quasithin.conjSubgroup]
    simp
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hXM : X ≤ D.M := by rw [hXeq]; exact sup_le hLM hKM
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := hMNX
  have hXne : X ≠ L := by
    intro hXL
    have hKleL : K ≤ L := by
      have : K ≤ X := by rw [hXeq]; exact le_sup_right
      rwa [hXL] at this
    have hKcard : Nat.card ↥K = Nat.card ↥L := by
      rw [hmK', CFSG.Quasithin.conjSubgroup]
      exact Subgroup.card_map_of_injective (MulAut.conj (m⁻¹)⁻¹).injective
    have hKL : K = L := Subgroup.eq_of_le_of_card_ge hKleL (by rw [hKcard])
    exact hLKne hKL.symm
  have hXsup : conjClosure D.M L = L ⊔ K := by rw [← ctx.X_eq, hXeq]
  have hneCl : conjClosure D.M L ≠ L := by rw [← ctx.X_eq]; exact hXne
  have hpair : ∃ y ∈ D.M, X = L ⊔ CFSG.Quasithin.conjSubgroup L y ∧ X ≠ L :=
    ⟨m⁻¹, (D.M.inv_mem hmM), by rw [hXeq, ← hmK'], hXne⟩
  have hpP : p.Prime := (D.sig_prime p hpSig).1
  rcases hc with h3 | h4
  · obtain ⟨-, hL2raw, hp3, -, φ, hφ, hker⟩ := h3
    have hL2 : IsL2 (Bar2 L) 3 := hL2raw
    subst p
    have hn3 : n = 3 := by
      rcases hshape0 with hN | hN
      · exact isL2_field_unique hN hL2
      · exact (P2214S.false_of_isSz_of_isL2 hN hL2).elim
    have hr7 : r = 7 := by
      have hdvd7 : r ∣ 7 := by simpa [hn3] using hrdvd
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h | h
      · exact absurd h hr.ne_one
      · exact h
    have hr2 : r ≠ 2 := by rw [hr7]; norm_num
    have hrp : r ≠ 3 := by rw [hr7]; norm_num
    have hSq : IsL2Square (Bar2 X) 3 := by
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isL2Square_bar2_conjClosure
        hLcal0 (D.M.inv_mem hmM) (by rw [hXsup, ← hmK']) hneCl hL2
      rwa [← ctx.X_eq] at h
    have hZ : Subgroup.center (Bar2 X) = ⊥ := center_eq_bot_of_isL2Square_three hSq
    have hrankX : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 X)) = 2 :=
      pRank_two_of_isL2Square_three hSq
    have hrankR : CFSG.Open.pRank 7 (⊤ : Subgroup (Bar2 X)) = 2 :=
      pRank_two_of_isL2Square_seven hSq
    obtain ⟨r', hr', hrdvd', hnotStrong'⟩ :=
      s17_45_exists_not_strongly ctx hshape0 hpair (h1 ctx.hyp125) hK3 hK4
    have hr'7 : r' = 7 := by
      have hdvd7 : r' ∣ 7 := by simpa [hn3] using hrdvd'
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h | h
      · exact absurd h hr'.ne_one
      · exact h
    have hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
      rw [hr7]
      rw [hr'7] at hnotStrong'
      exact hnotStrong'
    have hbarCard : Nat.card (Bar2 X) = 504 ^ 2 := by
      obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := hSq
      have : Finite P := finite_of_isL2 hP
      have : Finite Q := finite_of_isL2 hQ
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_of_isL2 hP, card_of_isL2 hQ]
      norm_num
    have hab : ∀ P : Sylow r (Bar2 X), IsMulCommutative (P : Subgroup (Bar2 X)) := by
      intro P
      have : Fact r.Prime := ⟨hr⟩
      have hfact : (Nat.card (Bar2 X)).factorization 7 = 2 := by
        have hpos : Nat.card (Bar2 X) ≠ 0 := Nat.card_pos.ne'
        have hdvd : 7 ^ 2 ∣ Nat.card (Bar2 X) := by rw [hbarCard]; norm_num
        have hnot : ¬ 7 ^ 3 ∣ Nat.card (Bar2 X) := by rw [hbarCard]; norm_num
        have hle : 2 ≤ (Nat.card (Bar2 X)).factorization 7 :=
          (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 7) hpos).mp hdvd
        have hlt : (Nat.card (Bar2 X)).factorization 7 < 3 := by
          by_contra h
          exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization
            (by norm_num : Nat.Prime 7) hpos).mpr (by omega))
        omega
      have hPcard : Nat.card ↥(P : Subgroup (Bar2 X)) = r ^ 2 := by
        rw [Sylow.card_eq_multiplicity, hr7, hfact]
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard
    have hrel : (X ⊔ F08.CentOverO2 D.M X).relIndex D.M = Nat.card (DihedralGroup 3) := by
      have h1' := Subgroup.relIndex_subgroupOf (H := X ⊔ F08.CentOverO2 D.M X)
        (K := D.M) (L := D.M) (le_refl D.M)
      rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h1'
      rw [← h1', ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    have hout : ¬ r ∣ (X ⊔ F08.CentOverO2 D.M X).relIndex D.M := by
      rw [hrel, DihedralGroup.nat_card]
      intro h
      rcases (Nat.Prime.dvd_mul hr).mp h with h2 | hpdiv
      · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1' | h1'
        · omega
        · exact hr2 h1'
      · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hpdiv with h1' | h1'
        · omega
        · exact hrp h1'
    have hrankR' : CFSG.Open.pRank r (⊤ : Subgroup (Bar2 X)) = 2 := by
      rw [hr7]; exact hrankR
    obtain ⟨E, hEX, hEel, hEcard⟩ := exists_elemAbelian_lift_of_bar (X := X) hr hr2 hrankR'
    have hC : CFSG.Open.pRank 3 (F08.CentOverO2 D.M X) ≤ 1 :=
      pRank_centOverO2_le_one_of_not_strongly (E := E) hSg h1219 h76 h614 hpSig
        hXM hMX hr hr2 hrp hab hout hnotStrong hEX hEel hEcard
    refine ⟨?_, ?_⟩
    · simpa using hC
    · have h := pRank_sup_centOverO2_le_add D hXM hMX (by norm_num : Nat.Prime 3) hZ hrankX
      omega
  · obtain ⟨-, hSzraw, hp5, -, φ, hφ, hker⟩ := h4
    have hSz : IsSz (Bar2 L) 5 := hSzraw
    subst p
    have hn5 : n = 5 := by
      rcases hshape0 with hN | hN
      · exact (P2214S.false_of_isSz_of_isL2 hSz hN).elim
      · exact eq_five_of_isSz_five hN hSz
    have hr31 : r = 31 := by
      have hdvd31 : r ∣ 31 := by simpa [hn5] using hrdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd31 with h | h
      · exact absurd h hr.ne_one
      · exact h
    have hr2 : r ≠ 2 := by rw [hr31]; norm_num
    have hrp : r ≠ 5 := by rw [hr31]; norm_num
    have hSq : IsSzSquare (Bar2 X) 5 := by
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSzSquare_bar2_conjClosure
        hLcal0 (D.M.inv_mem hmM) (by rw [hXsup, ← hmK']) hneCl hSz
      rwa [← ctx.X_eq] at h
    have hZ : Subgroup.center (Bar2 X) = ⊥ := center_eq_bot_of_isSzSquare_five hSq
    have hrankX : CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 X)) = 2 :=
      pRank_two_of_isSzSquare_five hSq
    have hrankR : CFSG.Open.pRank 31 (⊤ : Subgroup (Bar2 X)) = 2 :=
      pRank_two_of_isSzSquare_thirtyone hSq
    obtain ⟨r', hr', hrdvd', hnotStrong'⟩ :=
      s17_45_exists_not_strongly ctx hshape0 hpair (h1 ctx.hyp125) hK3 hK4
    have hr'31 : r' = 31 := by
      have hdvd31 : r' ∣ 31 := by simpa [hn5] using hrdvd'
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd31 with h | h
      · exact absurd h hr'.ne_one
      · exact h
    have hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
      rw [hr31]
      rw [hr'31] at hnotStrong'
      exact hnotStrong'
    have hbarCard : Nat.card (Bar2 X) = 32537600 ^ 2 := by
      obtain ⟨P, Q, _, _, ⟨e⟩, hP, hQ⟩ := hSq
      have : Finite P := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hP
      have : Finite Q := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hQ
      rw [Nat.card_congr e.toEquiv, Nat.card_prod,
        CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel hP).2,
        CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel hQ).2]
      norm_num
    have hab : ∀ P : Sylow r (Bar2 X), IsMulCommutative (P : Subgroup (Bar2 X)) := by
      intro P
      have : Fact r.Prime := ⟨hr⟩
      have hfact : (Nat.card (Bar2 X)).factorization 31 = 2 := by
        have hpos : Nat.card (Bar2 X) ≠ 0 := Nat.card_pos.ne'
        have hdvd : 31 ^ 2 ∣ Nat.card (Bar2 X) := by rw [hbarCard]; norm_num
        have hnot : ¬ 31 ^ 3 ∣ Nat.card (Bar2 X) := by rw [hbarCard]; norm_num
        have hle : 2 ≤ (Nat.card (Bar2 X)).factorization 31 :=
          (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 31) hpos).mp hdvd
        have hlt : (Nat.card (Bar2 X)).factorization 31 < 3 := by
          by_contra h
          exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization
            (by norm_num : Nat.Prime 31) hpos).mpr (by omega))
        omega
      have hPcard : Nat.card ↥(P : Subgroup (Bar2 X)) = r ^ 2 := by
        rw [Sylow.card_eq_multiplicity, hr31, hfact]
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard
    have hrel : (X ⊔ F08.CentOverO2 D.M X).relIndex D.M = Nat.card (DihedralGroup 5) := by
      have h1' := Subgroup.relIndex_subgroupOf (H := X ⊔ F08.CentOverO2 D.M X)
        (K := D.M) (L := D.M) (le_refl D.M)
      rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h1'
      rw [← h1', ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    have hout : ¬ r ∣ (X ⊔ F08.CentOverO2 D.M X).relIndex D.M := by
      rw [hrel, DihedralGroup.nat_card]
      intro h
      rcases (Nat.Prime.dvd_mul hr).mp h with h2 | hpdiv
      · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1' | h1'
        · omega
        · exact hr2 h1'
      · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hpdiv with h1' | h1'
        · omega
        · exact hrp h1'
    have hrankR' : CFSG.Open.pRank r (⊤ : Subgroup (Bar2 X)) = 2 := by
      rw [hr31]; exact hrankR
    obtain ⟨E, hEX, hEel, hEcard⟩ := exists_elemAbelian_lift_of_bar (X := X) hr hr2 hrankR'
    have hC : CFSG.Open.pRank 5 (F08.CentOverO2 D.M X) ≤ 1 :=
      pRank_centOverO2_le_one_of_not_strongly (E := E) hSg h1219 h76 h614 hpSig
        hXM hMX hr hr2 hrp hab hout hnotStrong hEX hEel hEcard
    refine ⟨?_, ?_⟩
    · simpa using hC
    · have h := pRank_sup_centOverO2_le_add D hXM hMX (by norm_num : Nat.Prime 5) hZ hrankX
      omega

theorem card_normalizer_sylow_isL2_three (A : Type) [Group A] [Finite A] (hA : IsL2 A 3)
    (S : Subgroup A) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    Nat.card ↥(Subgroup.normalizer (S : Set A)) = 56 ∧ Nat.card ↥S = 8 := by
  have hPSL : CFSG.Quasithin.IsPSL 2 2 3 A :=
    (CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL).mp hA
  have hPSLtop : CFSG.Quasithin.IsPSL 2 2 3 ↥(⊤ : Subgroup A) :=
    CFSG.Quasithin.RonanG72.statedClassicalModel_of_mulEquiv
      (Subgroup.topEquiv (G := A)) hPSL
  obtain ⟨-, hU, hB, -⟩ :=
    CFSG.Quasithin.H13.P31X.l2BorelFacts_holds 3 (by norm_num) A ⊤ S hPSLtop hS
  refine ⟨?_, hU⟩
  rw [show (⊤ : Subgroup A) ⊓ Subgroup.normalizer (S : Set A) =
    Subgroup.normalizer (S : Set A) from inf_eq_right.mpr le_top] at hB
  rw [hB]
  norm_num

theorem card_normalizer_sylow_isSz_five
    (B : Type) [Group B] [Finite B] (hB : IsSz B 5)
    (S : Subgroup B) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    Nat.card ↥(Subgroup.normalizer (S : Set B)) = 31744 ∧ Nat.card ↥S = 1024 := by
  have hB' : CFSG.Quasithin.IsSz 5 B :=
    (CFSG.LocalAnalysis.WeakClosure81.isSz_iff_isSz).mp hB
  have hcardB : Nat.card B = 32537600 := by
    rw [CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel hB).2]
    norm_num
  let Qtop : Sylow 2 ↥(⊤ : Subgroup B) := CFSG.Quasithin.A4.toSylow hS
  let e : ↥(⊤ : Subgroup B) ≃* B := Subgroup.topEquiv
  let Q : Sylow 2 B := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Qtop
  have hQcoe : ((Q : Sylow 2 B) : Subgroup B) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : B) ∈ S := by
        have h1 := hy
        rw [show ((Qtop : Sylow 2 ↥(⊤ : Subgroup B)) :
          Subgroup ↥(⊤ : Subgroup B)) = S.subgroupOf ⊤ from rfl] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      simpa [e] using hy'
    · intro hx
      refine ⟨⟨x, trivial⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr hx
  have hN : Nat.card ↥(Subgroup.normalizer (S : Set B)) = 31744 := by
    rw [← hQcoe]
    have := CFSG.LieType.SuzukiSubgroups.card_normalizer_sylow_of_isSz (H := B) hB' Q
    rw [this]
    norm_num
  refine ⟨hN, ?_⟩
  have hfact : (32537600 : ℕ).factorization 2 = 10 := by
    have hpos : (32537600 : ℕ) ≠ 0 := by norm_num
    have hdvd : 2 ^ 10 ∣ 32537600 := by norm_num
    have hnot : ¬ 2 ^ 11 ∣ 32537600 := by norm_num
    have hle : 10 ≤ (32537600 : ℕ).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp hdvd
    have hlt : (32537600 : ℕ).factorization 2 < 11 := by
      by_contra h
      exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mpr (by omega))
    omega
  have h := CFSG.QuasithinUnique.IsSylowTwoOf.card_eq hS
  rw [h, CFSG.QuasithinUnique.twoPart, Subgroup.card_top, hcardB, hfact]
  norm_num

theorem sylow_inf_T (D : Data G) {X : Subgroup G}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G)) :
    CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ X) X ∧
      CFSG.Open.pCoreOf 2 X ≤ D.T ⊓ X := by
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM
  have hXn : (X.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr hMX
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ X) X :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hT hXM hMX
  exact ⟨hSyl, CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hSyl⟩

theorem factor_borel_data_isL2_three (A : Type) [Group A] [Finite A] (hA : IsL2 A 3)
    (S : Subgroup A) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    Nat.card ↥(Subgroup.normalizer (S : Set A)) = 56 ∧ Nat.card ↥S = 8 ∧
      S.relIndex (Subgroup.normalizer (S : Set A)) = 7 ∧
      (Nat.card ↥(Subgroup.normalizer (S : Set A))).factorization 7 = 1 ∧
      (Nat.card A).factorization 7 = 1 ∧
      ¬ 3 ∣ Nat.card ↥(Subgroup.normalizer (S : Set A)) := by
  obtain ⟨hN, hS8⟩ := card_normalizer_sylow_isL2_three A hA S hS
  have hcardA : Nat.card A = 504 := by
    rw [card_of_isL2 hA]; norm_num
  refine ⟨hN, hS8, ?_, ?_, ?_, ?_⟩
  · have hrel := Subgroup.relIndex_mul_card S (Subgroup.normalizer (S : Set A))
    rw [inf_eq_left.mpr (Subgroup.le_normalizer), hN, hS8] at hrel
    omega
  · exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num : Nat.Prime 7)
      (by rw [hN]; norm_num) (by rw [hN]; norm_num) (by rw [hN]; norm_num)
  · exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num : Nat.Prime 7)
      (by rw [hcardA]; norm_num) (by rw [hcardA]; norm_num) (by rw [hcardA]; norm_num)
  · rw [hN]; norm_num

theorem factor_borel_data_isSz_five
    (B : Type) [Group B] [Finite B] (hB : IsSz B 5)
    (S : Subgroup B) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    Nat.card ↥(Subgroup.normalizer (S : Set B)) = 31744 ∧ Nat.card ↥S = 1024 ∧
      S.relIndex (Subgroup.normalizer (S : Set B)) = 31 ∧
      (Nat.card ↥(Subgroup.normalizer (S : Set B))).factorization 31 = 1 ∧
      (Nat.card B).factorization 31 = 1 ∧
      ¬ 5 ∣ Nat.card ↥(Subgroup.normalizer (S : Set B)) := by
  obtain ⟨hN, hS1024⟩ := card_normalizer_sylow_isSz_five B hB S hS
  have hcardB : Nat.card B = 32537600 := by
    rw [CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel hB).2]
    norm_num
  refine ⟨hN, hS1024, ?_, ?_, ?_, ?_⟩
  · have hrel := Subgroup.relIndex_mul_card S (Subgroup.normalizer (S : Set B))
    rw [inf_eq_left.mpr (Subgroup.le_normalizer), hN, hS1024] at hrel
    omega
  · exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num : Nat.Prime 31)
      (by rw [hN]; norm_num) (by rw [hN]; norm_num) (by rw [hN]; norm_num)
  · exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num : Nat.Prime 31)
      (by rw [hcardB]; norm_num) (by rw [hcardB]; norm_num) (by rw [hcardB]; norm_num)
  · rw [hN]; norm_num

theorem product_borel_data_isL2_square {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (hA : IsL2 A 3) (hB : IsL2 B 3) {S : Subgroup (A × B)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.normalizer (S : Set (A × B))) ∧
      S.relIndex (Subgroup.normalizer (S : Set (A × B))) = 7 ^ 2 ∧
      (Nat.card ↥(Subgroup.normalizer (S : Set (A × B)))).factorization 7 = 2 ∧
      (Nat.card (A × B)).factorization 7 = 2 := by
  have hSA := CFSG.Quasithin.E9P2.FinInv.isSylowTwoOf_map_fst hS
  have hSB := CFSG.Quasithin.E9P2.FinInv.isSylowTwoOf_map_snd hS
  obtain ⟨hNA, hSA8, hrelA, hfacNA, hfacA, hpA⟩ := factor_borel_data_isL2_three A hA _ hSA
  obtain ⟨hNB, hSB8, hrelB, hfacNB, hfacB, hpB⟩ := factor_borel_data_isL2_three B hB _ hSB
  have hSprod : S = (S.map (MonoidHom.fst A B)).prod (S.map (MonoidHom.snd A B)) :=
    CFSG.Quasithin.E9P2.FinInv.eq_prod_map hS
  have hNprod : Subgroup.normalizer (S : Set (A × B)) =
      (Subgroup.normalizer (S.map (MonoidHom.fst A B))).prod
        (Subgroup.normalizer (S.map (MonoidHom.snd A B))) := by
    conv_lhs => rw [hSprod]
    exact UC22.normalizer_prod_eq'
  have hNcard : Nat.card ↥(Subgroup.normalizer (S : Set (A × B))) = 56 * 56 := by
    rw [hNprod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hNA, hNB]
  have hScard : Nat.card ↥S = 8 * 8 := by
    rw [hSprod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hSA8, hSB8]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hNcard]
    norm_num
  · have hrel := Subgroup.relIndex_mul_card S (Subgroup.normalizer (S : Set (A × B)))
    rw [inf_eq_left.mpr (Subgroup.le_normalizer), hNcard, hScard] at hrel
    have : S.relIndex (Subgroup.normalizer (S : Set (A × B))) = 49 := by omega
    exact this
  · rw [hNcard]
    change (56 * 56 : ℕ).factorization 7 = 2
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num : Nat.Prime 7) (by norm_num)
      (by norm_num : 7 ^ 2 ∣ 56 * 56) (by norm_num : ¬ 7 ^ 3 ∣ 56 * 56)
  · rw [Nat.card_prod, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    change (Nat.card A).factorization 7 + (Nat.card B).factorization 7 = 2
    rw [hfacA, hfacB]

theorem product_borel_data_isSz_square
    {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (hA : IsSz A 5) (hB : IsSz B 5) {S : Subgroup (A × B)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ¬ 5 ∣ Nat.card ↥(Subgroup.normalizer (S : Set (A × B))) ∧
      S.relIndex (Subgroup.normalizer (S : Set (A × B))) = 31 ^ 2 ∧
      (Nat.card ↥(Subgroup.normalizer (S : Set (A × B)))).factorization 31 = 2 ∧
      (Nat.card (A × B)).factorization 31 = 2 := by
  have hSA := CFSG.Quasithin.E9P2.FinInv.isSylowTwoOf_map_fst hS
  have hSB := CFSG.Quasithin.E9P2.FinInv.isSylowTwoOf_map_snd hS
  obtain ⟨hNA, hSA1024, hrelA, hfacNA, hfacA, hpA⟩ := factor_borel_data_isSz_five A hA _ hSA
  obtain ⟨hNB, hSB1024, hrelB, hfacNB, hfacB, hpB⟩ := factor_borel_data_isSz_five B hB _ hSB
  have hSprod : S = (S.map (MonoidHom.fst A B)).prod (S.map (MonoidHom.snd A B)) :=
    CFSG.Quasithin.E9P2.FinInv.eq_prod_map hS
  have hNprod : Subgroup.normalizer (S : Set (A × B)) =
      (Subgroup.normalizer (S.map (MonoidHom.fst A B))).prod
        (Subgroup.normalizer (S.map (MonoidHom.snd A B))) := by
    conv_lhs => rw [hSprod]
    exact UC22.normalizer_prod_eq'
  have hNcard : Nat.card ↥(Subgroup.normalizer (S : Set (A × B))) = 31744 * 31744 := by
    rw [hNprod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hNA, hNB]
  have hScard : Nat.card ↥S = 1024 * 1024 := by
    rw [hSprod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hSA1024, hSB1024]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hNcard]
    norm_num
  · have hrel := Subgroup.relIndex_mul_card S (Subgroup.normalizer (S : Set (A × B)))
    rw [inf_eq_left.mpr (Subgroup.le_normalizer), hNcard, hScard] at hrel
    have : S.relIndex (Subgroup.normalizer (S : Set (A × B))) = 961 := by omega
    exact this
  · rw [hNcard]
    change (31744 * 31744 : ℕ).factorization 31 = 2
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num : Nat.Prime 31) (by norm_num)
      (by norm_num : 31 ^ 2 ∣ 31744 * 31744) (by norm_num : ¬ 31 ^ 3 ∣ 31744 * 31744)
  · rw [Nat.card_prod, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    change (Nat.card A).factorization 31 + (Nat.card B).factorization 31 = 2
    rw [hfacA, hfacB]

theorem borel_order_data_of_bar (D : Data G) {X : Subgroup G} {p r : ℕ}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ X) X)
    (hQ : CFSG.Open.pCoreOf 2 X ≤ D.T ⊓ X)
    (hNbar : ¬ p ∣ Nat.card ↥(Subgroup.normalizer
      (barImage X (D.T ⊓ X) : Set (Bar2 X))))
    (hrelbar : (barImage X (D.T ⊓ X)).relIndex
      (Subgroup.normalizer (barImage X (D.T ⊓ X) : Set (Bar2 X))) = r ^ 2)
    (hfacN : (Nat.card ↥(Subgroup.normalizer
      (barImage X (D.T ⊓ X) : Set (Bar2 X)))).factorization r = 2)
    (hfacX : (Nat.card (Bar2 X)).factorization r = 2) :
    ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ∧
      (D.T ⊓ X).relIndex
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2 ∧
      (Nat.card ↥(X ⊓ Subgroup.normalizer
        ((D.T ⊓ X : Subgroup G) : Set G))).factorization r = 2 ∧
      (Nat.card ↥X).factorization r = 2 := by
  classical
  let Y : Type := ↥X
  let U : Subgroup Y := (D.T ⊓ X).subgroupOf X
  let π : Y →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 Y)
  have hker_eq : π.ker = CFSG.pCore 2 Y := QuotientGroup.ker_mk' (CFSG.pCore 2 Y)
  let Sbar : Subgroup (Bar2 X) := barImage X (D.T ⊓ X)
  let Nbar : Subgroup (Bar2 X) := Subgroup.normalizer (Sbar : Set (Bar2 X))
  let P : Subgroup G := D.T ⊓ X
  let NG : Subgroup G := X ⊓ Subgroup.normalizer (P : Set G)
  have hker : π.ker ≤ U := by
    intro z hz
    rw [hker_eq] at hz
    have hz' : z ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf X := by
      rw [CFSG.openPCoreOf_subgroupOf]
      exact hz
    exact Subgroup.mem_subgroupOf.mpr (hQ (Subgroup.mem_subgroupOf.mp hz'))
  have hSbar : U.map π = Sbar := rfl
  have hUeq : Sbar.comap π = U := by
    rw [← hSbar]
    exact Subgroup.comap_map_eq_self hker
  have hNU : Subgroup.normalizer (U : Set Y) = Nbar.comap π := by
    change Subgroup.normalizer (U : Set Y) = (Subgroup.normalizer (U.map π)).comap π
    rw [Subgroup.comap_normalizer_eq_of_surjective _
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 Y) : Function.Surjective π),
      Subgroup.comap_map_eq_self hker]
  have hrel : U.relIndex (Subgroup.normalizer (U : Set Y)) = r ^ 2 := by
    have h := Subgroup.relIndex_comap (H := Sbar) (f := π) (K := Nbar.comap π)
    rw [hUeq] at h
    rw [hNU, h, Subgroup.map_comap_eq]
    have htop : π.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rw [htop, top_inf_eq]
    exact hrelbar
  have hker2 : IsPGroup 2 ↥(CFSG.pCore 2 Y) := CFSG.pCore_isPGroup
  have hnotdvd : ¬ r ∣ Nat.card ↥(CFSG.pCore 2 Y) := by
    intro hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker2
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hdvd))
  have hnotdvd_p : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 Y) := by
    intro hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker2
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hdvd))
  have hpCore_le_Nbar : CFSG.pCore 2 Y ≤ Nbar.comap π := by
    intro z hz
    have hz' : z ∈ π.ker := by rwa [hker_eq]
    have hzU : z ∈ U := hker hz'
    have hzS : z ∈ Sbar.comap π := by rwa [hUeq]
    exact Subgroup.comap_mono (Subgroup.le_normalizer) hzS
  have hNcardU : Nat.card ↥(Subgroup.normalizer (U : Set Y)) =
      Nat.card ↥Nbar * Nat.card ↥(CFSG.pCore 2 Y) := by
    let f : ↥(Nbar.comap π) →* ↥Nbar :=
      { toFun := fun x => ⟨π (x : Y), Subgroup.mem_comap.mp x.2⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp }
    have hfker : f.ker = (CFSG.pCore 2 Y).subgroupOf (Nbar.comap π) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have h1 : π (x : Y) = 1 := by
          have := congrArg Subtype.val hx
          simpa [f] using this
        exact (QuotientGroup.eq_one_iff (x : Y)).mp h1
      · intro hx
        have h1 : π (x : Y) = 1 := (QuotientGroup.eq_one_iff (x : Y)).mpr hx
        ext
        simpa [f] using h1
    have hfsurj : Function.Surjective f := by
      intro n
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Y) (n : Bar2 X)
      refine ⟨⟨y, ?_⟩, ?_⟩
      · rw [Subgroup.mem_comap, hy]
        exact n.2
      · ext
        exact hy
    have h := Subgroup.card_ker_mul_card_of_surjective hfsurj
    rw [hfker] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hpCore_le_Nbar).toEquiv] at h
    rw [hNU, ← h, mul_comm]
  have hXcard : Nat.card Y = Nat.card (Bar2 X) * Nat.card ↥(CFSG.pCore 2 Y) := by
    have h := Subgroup.card_ker_mul_card_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 Y) : Function.Surjective π)
    rw [hker_eq] at h
    rw [← h, mul_comm]
  have hNGsub : NG.subgroupOf X = Subgroup.normalizer (U : Set Y) := by
    rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer X P inf_le_right]
  have hNGcard : Nat.card ↥NG = Nat.card ↥(Subgroup.normalizer (U : Set Y)) := by
    rw [← hNGsub]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show NG ≤ X from inf_le_left)).toEquiv).symm
  have hrelG : P.relIndex NG = r ^ 2 := by
    have h := Subgroup.relIndex_subgroupOf (H := P) (K := NG) (L := X)
      (show NG ≤ X from inf_le_left)
    rw [hNGsub] at h
    rw [← h]
    exact hrel
  have hfacNG : (Nat.card ↥NG).factorization r = 2 := by
    rw [hNGcard, hNcardU, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    change (Nat.card ↥Nbar).factorization r +
      (Nat.card ↥(CFSG.pCore 2 Y)).factorization r = 2
    rw [hfacN, Nat.factorization_eq_zero_of_not_dvd hnotdvd]
  have hfacXG : (Nat.card ↥X).factorization r = 2 := by
    rw [show Nat.card ↥X = Nat.card Y from rfl, hXcard,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    change (Nat.card (Bar2 X)).factorization r +
      (Nat.card ↥(CFSG.pCore 2 Y)).factorization r = 2
    rw [hfacX, Nat.factorization_eq_zero_of_not_dvd hnotdvd]
  have hpNG : ¬ p ∣ Nat.card ↥NG := by
    rw [hNGcard, hNcardU]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hNbar h
    · exact hnotdvd_p h
  exact ⟨hpNG, hrelG, hfacNG, hfacXG⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
