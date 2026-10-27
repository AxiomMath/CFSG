module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenStepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4G2TwoAutInnerHolds
public import CFSG.Quasithin.Background.Sp4InfGeo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin (IsSylowIn)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatLeafProof
  (lieModel_eq_of_isChar2LieShape fieldExponent_eq_of_isChar2LieShape)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem barSub_M_le_normalizer_barSub (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) :
    barSub V₀ V h.hyp125.isElemAbelian D.M ≤
      Subgroup.normalizer
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) : Set _) := by
  obtain ⟨hV, -, -, -, -, -, -⟩ := h.hyp125.pairFacts
  have hYX : ∀ y ∈ D.M, ∀ x ∈ conjClosure D.M L, y * x * y⁻¹ ∈ conjClosure D.M L :=
    fun y hy x hx =>
      (Subgroup.mem_normalizer_iff.1
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L hy) x).1 hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    have h1 := c8_conj_mem_barSub V₀ V hV hYX (g⁻¹) (Subgroup.inv_mem _ hg) y hy
    simpa using h1
  · intro hy
    have h1 := c8_conj_mem_barSub V₀ V hV hYX g hg (g⁻¹ * y * g) hy
    have hEq : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [hEq] at h1

theorem conj_eq_of_actTil_tilOf_eq_of_bot {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ = ⊥) {g : G} (hgs : g ∈ stabTil V₀ V) {v : G} (hv : v ∈ V)
    (hfix : actTil V₀ V hV ⟨g, hgs⟩ (tilOf V₀ V hV v hv) = tilOf V₀ V hV v hv) :
    g * v * g⁻¹ = v := by
  have h2 : mkTil V₀ V hV
      (actStab V₀ V hV ⟨g, hgs⟩ (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)) =
      mkTil V₀ V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩) := by
    rw [← actTil_mk]
    exact hfix
  have h3 := (mkTil_eq_iff V₀ V hV _ _).1 h2
  rw [actStab_apply_val] at h3
  have h4 : g * v * g⁻¹ * v⁻¹ ∈ V₀ := h3
  rw [hV₀] at h4
  exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 h4)

theorem preBarSub_S_eq (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hsimple : IsSimpleGroup (Bar2 (conjClosure D.M L)))
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥) :
    preBarSub (conjClosure D.M L) V₀ V h.hyp125.isElemAbelian
      (barSub V₀ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L)) =
      D.T ⊓ conjClosure D.M L := by
  classical
  obtain ⟨hV, -, -, -, hMnorm, hMnorm₀, -⟩ := h.hyp125.pairFacts
  set M := D.M with hMdef
  set T := D.T with hTdef
  set X := conjClosure D.M L with hXdef
  have hXM : X ≤ M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hMstab : M ≤ stabTil V₀ V := le_stabTil hMnorm hMnorm₀
  have hXstab : X ≤ stabTil V₀ V := hXM.trans hMstab
  have hXn : (X.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr
      (TwelveTwentyThree.le_normalizer_conjClosure M L)
  have hTsyl : IsSylowIn 2 T M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hO2_le : pCoreOf 2 X ≤ T ⊓ X := by
    have hO2normal : ((pCoreOf 2 X).subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 X)]
      intro a b ha hb
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hb ha
    have hSylIn : IsSylowIn 2 (T ⊓ X) X :=
      (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T ⊓ X) (K := X)).mp
        (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hXM
          (TwelveTwentyThree.le_normalizer_conjClosure M L))
    exact hSylIn.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hO2normal
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X)
  have hXsub : CFSG.Open.IsSubnormal X M :=
    CFSG.Open.IsSubnormal.step hXM hXn (CFSG.Open.IsSubnormal.refl M)
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgX, hgs, hact⟩ := (mem_preBarSub X V₀ V hV _).1 hg
    obtain ⟨s, hs, hgs'⟩ := (mem_barSub V₀ V hV (T ⊓ X)
      (actTil V₀ V hV ⟨g, hgs⟩)).1 hact
    have hval : actTil V₀ V hV ⟨(s : G), s.2⟩ = actTil V₀ V hV ⟨g, hgs⟩ := hgs'
    have hmem : (s : G) ∈ T ⊓ X := hs
    have hgsx : (s : G)⁻¹ * g ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem (hXstab hmem.2)) hgs
    have hprod : actTil V₀ V hV ⟨(s : G), hXstab hmem.2⟩ *
        actTil V₀ V hV ⟨(s : G)⁻¹ * g, hgsx⟩ = actTil V₀ V hV ⟨g, hgs⟩ := by
      rw [← map_mul]
      congr 1
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hact1 : actTil V₀ V hV ⟨(s : G)⁻¹ * g, hgsx⟩ = 1 := by
      have h6 : actTil V₀ V hV ⟨g, hgs⟩ * actTil V₀ V hV ⟨(s : G)⁻¹ * g, hgsx⟩ =
          actTil V₀ V hV ⟨g, hgs⟩ * 1 := by
        rw [mul_one]
        calc actTil V₀ V hV ⟨g, hgs⟩ * actTil V₀ V hV ⟨(s : G)⁻¹ * g, hgsx⟩
            = actTil V₀ V hV ⟨(s : G), hXstab hmem.2⟩ *
                actTil V₀ V hV ⟨(s : G)⁻¹ * g, hgsx⟩ := by rw [hval]
          _ = actTil V₀ V hV ⟨g, hgs⟩ := hprod
      exact mul_left_cancel h6
    have hker : ((s : G)⁻¹ * g) ∈ pCoreOf 2 X :=
      mem_pCoreOf_of_actTil_eq_one h.hyp125 hXsub hsimple hX1
        (X.mul_mem (X.inv_mem hmem.2) hgX) hgsx hact1
    have hg_eq : g = (s : G) * ((s : G)⁻¹ * g) := by group
    refine ⟨?_, ?_⟩
    · rw [hg_eq]
      exact T.mul_mem hmem.1 (hO2_le hker).1
    · rw [hg_eq]
      exact X.mul_mem hmem.2 (hO2_le hker).2
  · intro g hg
    obtain ⟨hgT, hgX⟩ := hg
    refine (mem_preBarSub X V₀ V hV _).2 ⟨hgX, hXstab hgX, ?_⟩
    exact actTil_mem_barSub V₀ V hV (show g ∈ T ⊓ X from ⟨hgT, hgX⟩) (hXstab hgX)

theorem inCalV1_of_hyp125_bot (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    InCalV1 D.M D.T V := by
  rcases h.1 with ⟨hW, -⟩ | ⟨hV0, -⟩
  · exact hW.1.1
  · exact absurd rfl hV0.1.1

theorem hpow_and_inner_of_isSp4 (D : Data G) {X : Subgroup G} {n : ℕ}
    (hX : X ∈ calC D.M) (hTL : D.T ≤ normalizer (X : Set G))
    (hns : ¬ S17.SwapsParabolics D.T X) (hodd : Odd n)
    (hSp : IsSp4 (Bar2 X) n) (hZ : Subgroup.center (Bar2 X) = ⊥) :
    (∀ m : ↥(normalizer (X : Set G)), (m : G) ∈ D.T →
        UC6S846.rhoL X m ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X)) ∧
      (∀ t ∈ D.T, ∃ j : ℕ, ∀ b ∈ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G),
        t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ D.T ⊓ X) := by
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ X) X :=
    S17.isSylowTwoOf_inf_of_mem_calC hX
  have hin : ∀ m : ↥(normalizer (X : Set G)), (m : G) ∈ D.T →
      UC6S846.rhoL X m ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
    intro m hmT
    exact sp4_twoAut_inner hodd hSp (S17.isSylowTwoOf_sylowBar2_of hSyl)
      (S17.exists_rhoL_pow_two_pow_eq_one hT2 m hmT)
      (S17.rhoL_map_eq_of_not_swaps hns m hmT)
  exact ⟨hin, S17.powerMap_of_rhoL_mem_inner hTL hT2 hSyl hZ hin⟩

theorem two_mul_le_mBar_of_involution (D : Data G) {V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D ⊥ V p L) {n : ℕ}
    (hSp : IsSp4 ↥(barSub ⊥ V h.hyp125.isElemAbelian (conjClosure D.M L)) n)
    (hinv : ∀ t ∈ normalizer (barSub ⊥ V h.hyp125.isElemAbelian
        (conjClosure D.M L) : Set (MulAut (Vtil ⊥ V h.hyp125.isElemAbelian))),
      orderOf t = 2 →
      2 * n ≤ CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t))) :
    2 * n ≤ mBar D.M ⊥ V h.hyp125.isElemAbelian := by
  classical
  obtain ⟨hV, -, -, -, -, -, -⟩ := h.hyp125.pairFacts
  set Xbar : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV (conjClosure D.M L) with hXdef
  set Mbar : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV D.M with hMdef
  have hXle : Xbar ≤ Mbar :=
    barSub_mono ⊥ V hV (TwelveTwentyThree.conjClosure_le h.hL.1.1.le)
  have hXeven : Even (Nat.card ↥Xbar) := by
    obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := LieModel.statedClassicalModel hSp (by decide)
    have hn1 : 1 ≤ n := (LieModel.admissible hSp).2.1
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hn1 hKcard
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Quasithin.B69.even_natCard_statedProj_sp
  have heven : Even (Nat.card ↥Mbar) :=
    even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hXeven)
      (Subgroup.card_dvd_of_le hXle))
  have hMnorm : Mbar ≤ Subgroup.normalizer (Xbar : Set _) :=
    barSub_M_le_normalizer_barSub D h
  unfold mBar
  rw [CFSG.Quasithin.E3.mParam, if_pos heven]
  refine le_csInf ?_ ?_
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥Mbar) 2
      (even_iff_two_dvd.mp heven)
    exact ⟨CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV
        (Subgroup.zpowers (t : MulAut (Vtil ⊥ V hV)))),
      t, t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩
  · rintro k ⟨t, htM, ht2, rfl⟩
    exact hinv t (hMnorm htM) ht2

theorem sp4_rootLine_setup (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) {n : ℕ}
    (hSp : IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n) :
    (∃ r : ℕ, r.Prime ∧ 7 ≤ r ∧ r ∣ 2 ^ n - 1 ∧
        conjClosure D.M L = Opp r D.M ∧ 2 ≤ CFSG.Open.pRank r D.M) ∧
      CFSG.Open.pRank p (conjClosure D.M L) = 2 ∧ 3 ≤ n ∧
      (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ p ∣ 2 ^ n + 1 ∧
      Subgroup.center (Bar2 (conjClosure D.M L)) = ⊥ ∧
      IsCyclic (Outer (Bar2 (conjClosure D.M L))) := by
  classical
  set X := conjClosure D.M L with hXdef
  have hSpBar2 : IsSp4 (Bar2 X) n := isSp4_bar2_of_isSp4_barSub h hSp
  obtain ⟨hXL, -, hn1, hodd, hcong, -, hmore⟩ :=
    isSp4_or_isG2_bar2_cong_more h h1742 (Or.inl hSpBar2)
  have hSpBar2L : IsSp4 (Bar2 L) n := hXL ▸ hSpBar2
  have hp : p.Prime := (D.sig_prime p h.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.hp).2
  have hLc : L ∈ calC D.M := h.hL.1
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hq : 2 < 2 ^ n := by
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    norm_num at h8
    omega
  have hpn : p ∣ 2 ^ n + 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  have hZ : Subgroup.center (Bar2 X) = ⊥ :=
    Inputs1719.center_eq_bot_of_rootLineShape (Y := Bar2 X) (n := n) hq
      (Or.inr (Or.inl hSpBar2))
  have hOut : IsCyclic (Outer (Bar2 X)) :=
    Inputs1719.isCyclic_outer_of_rootLineShape (Y := Bar2 X) (n := n)
      (Or.inr (Or.inl hSpBar2))
  have hrdata : ∃ r : ℕ, r.Prime ∧ 7 ≤ r ∧ r ∣ 2 ^ n - 1 ∧ X = Opp r D.M ∧
      2 ≤ CFSG.Open.pRank r D.M := by
    obtain ⟨r, hr, hrdvd⟩ := s13_exists_prime_dvd hn1
    have hr7 : 7 ≤ r := s13_seven_le_of_dvd hodd hr hrdvd
    have hr2 : r ≠ 2 := by omega
    have hXr : X = Opp r D.M := (hmore.2 r hr (by omega) hrdvd).1
    obtain ⟨E, hE, hEel, hEcard⟩ :=
      S17.exists_elemAbelian_sq_le_borel hLc (Or.inr (Or.inl hSpBar2L)) hq hr hr2 hrdvd
    have hrankE : 2 ≤ CFSG.Open.pRank r D.M :=
      CFSG.SectionRank.le_pRank hr.one_lt
        (hE.trans (inf_le_left.trans hLc.1.le)) hEel hEcard
    exact ⟨r, hr, hr7, hrdvd, hXr, hrankE⟩
  have hpX : CFSG.Open.pRank p X = 2 := by
    have hdvd : p ∣ (2 ^ n) ^ 2 - 1 := by
      have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        simpa using Nat.sq_sub_sq (2 ^ n) 1
      rw [hfac]
      exact dvd_mul_of_dvd_left hpn _
    have hle : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) ≤ 2 :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p218d_pRank_le_two_sp4 hSpBar2 hp hp2
    have hge : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.two_le_pRank_sp4 hSpBar2 hp hdvd
    rw [← CFSG.Quasithin.pRank_modO2_eq X hp hp2]
    exact le_antisymm hle hge
  exact ⟨hrdata, hpX, hn3, hcong, hpn, hZ, hOut⟩

theorem sp4Data_of_df (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hm3 : MBarGT D.M V₀ V 3) (h6b : R18_6bAt D V₀ V p L h)
    (h7b : R18_7bAt D V₀ V p L h) (h8 : R18_8At D V₀ V p L h)
    (h9 : R18_9At D V₀ V p L h) (h10 : R18_10At D V₀ V p L h)
    (hSp : IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n) :
    IsSp4 (Bar2 (conjClosure D.M L)) n ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (π : ↥(StatedSp 2 K) →* ↥(barSub V₀ V h.hyp125.isElemAbelian
          (conjClosure D.M L))),
        Nat.card K = 2 ^ n ∧
          SumOfNatVia (CFSG.Quasithin.FFModel.nat (StatedSp 2 K))
            (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2 π := by
  classical
  have hSpBar2 : IsSp4 (Bar2 (conjClosure D.M L)) n := isSp4_bar2_of_isSp4_barSub h hSp
  have hsX : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
  rcases h6b hm3 h7b with h2 | h3 | h4 | h5 | h6
  · obtain ⟨m, hsu | hom6 | hop4⟩ := h10 h2
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp
        (isU4_of_isSUn_four hsu)).1 (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp
        (isU4_of_isOmegaMinus hom6)).1 (by decide)
    · exact (not_isSimpleGroup_of_isOmegaPlus_four hop4 hsX).elim
  · obtain ⟨f, hsp | hom6 | hom4⟩ := h3
    · obtain ⟨hSpBar2f, K, hKf, hKfin, π, hKcard, hsum⟩ := hsp
      have hfn : f = n :=
        fieldExponent_eq_of_isChar2LieShape hSpBar2 S17.isChar2LieShape_PSp hSpBar2f
      exact ⟨hSpBar2, K, hKf, hKfin, π, by rw [hKcard, hfn], hsum⟩
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp
        (isU4_of_isOmegaMinus hom6.1)).1 (by decide)
    · obtain ⟨-, hOm4, K, hKfield, hKfin, b, c, π, hKcard, hbc, hsum⟩ := hom4
      have hk : 1 ≤ f / 2 := by
        rcases Nat.eq_zero_or_pos (f / 2) with h0 | h0
        · rw [h0, pow_zero] at hKcard
          exact absurd hKcard (Finite.one_lt_card).ne'
        · exact h0
      exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp
        (isL2_of_isOmegaMinus_four hk hOm4)).1 (by decide)
  · exact (h9 h4).elim
  · exact (h8 h5).elim
  · exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp
      (isU4_of_isSUn_four h6.1)).1 (by decide)

theorem not_swapsParabolics_of_isSp4_df (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hm3 : MBarGT D.M V₀ V 3) (h6b : R18_6bAt D V₀ V p L h)
    (h7b : R18_7bAt D V₀ V p L h) (h8 : R18_8At D V₀ V p L h)
    (h9 : R18_9At D V₀ V p L h) (h10 : R18_10At D V₀ V p L h)
    (hSp : IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n)
    (hKns : K_Sp4TwoNat_noSwap) :
    ¬ S17.SwapsParabolics D.T (conjClosure D.M L) := by
  classical
  intro hswap
  obtain ⟨hSpBar2, K, hKf, hKfin, π, hKcard, hsum⟩ :=
    sp4Data_of_df D h hm3 h6b h7b h8 h9 h10 hSp
  obtain ⟨hV, -, -, -, hMnorm, hMnorm₀, -⟩ := h.hyp125.pairFacts
  set X : Subgroup G := conjClosure D.M L with hXdef
  set T : Subgroup G := D.T with hTdef
  have hMstab : D.M ≤ stabTil V₀ V := le_stabTil hMnorm hMnorm₀
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hXn : (X.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hTsyl : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hYnorm := EighteenElevenTransport.barSub_le_normalizer_barSub D h
  have hSyl : IsSylowIn 2
      (barSub V₀ V hV D.T ⊓ barSub V₀ V hV X) (barSub V₀ V hV X) :=
    EighteenElevenTransport.barSub_inf_isSylow hV hMstab hTsyl hXM hXn
  have hBar2 : IsSimpleGroup (Bar2 X) :=
    (uc22p22a_sp4_simple _ n hSpBar2).1
  have hSumIso : SumOfNatIsoMod (fun H U Z => NatSpn H U Z 4 n)
      (barSub V₀ V hV X) ⊤ ⊥ 2 :=
    sumOfNatIsoMod_natSpn_of_sumOfNatVia hKcard hsum
  have hSpX : IsSp4 ↥(barSub V₀ V hV X) n := by
    rw [hXdef]
    exact hSp
  exact (hKns (Vtil V₀ V hV) (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (barSub V₀ V hV X) (barSub V₀ V hV D.T) n hYnorm hSyl hSpX hSumIso)
    (swapsParabolics_barSub_of_hyp18 D h hSp hBar2 hswap)

theorem gap_18_11_V0_of_df (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h67 : S17.R17_67At D V₀ V)
    (hm3 : MBarGT D.M V₀ V 3) (h6b : R18_6bAt D V₀ V p L h)
    (h7b : R18_7bAt D V₀ V p L h) (h8 : R18_8At D V₀ V p L h)
    (h9 : R18_9At D V₀ V p L h) (h10 : R18_10At D V₀ V p L h)
    (hKns : K_Sp4TwoNat_noSwap) :
    Gap_18_11_V0 D V₀ V p L h := by
  rintro ⟨n, hSp⟩
  have hSpBar2 : IsSp4 (Bar2 (conjClosure D.M L)) n := isSp4_bar2_of_isSp4_barSub h hSp
  have hXL : conjClosure D.M L = L :=
    conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSpBar2)
  have hnot := not_swapsParabolics_of_isSp4_df D h hm3 h6b h7b h8 h9 h10 hSp hKns
  by_contra hV0
  have h67' := h67 hV0 p h.hp L h.hL (conjClosure D.M L) rfl h.hX
  rcases h67' with hU5 | ⟨m, -, hU4⟩ | ⟨m, hsp4, hswap⟩ | ⟨hne, m, hshape4⟩ |
    ⟨m, -, hshape5⟩
  · exact absurd (lieModel_eq_of_isChar2LieShape hSpBar2 S17.isChar2LieShape_PSp hU5).1
      (by decide)
  · exact absurd (lieModel_eq_of_isChar2LieShape hSpBar2 S17.isChar2LieShape_PSp hU4).1
      (by decide)
  · exact hnot hswap
  · exact hne hXL
  · rcases hshape5 with hl2 | hu3
    · exact absurd (lieModel_eq_of_isChar2LieShape hSpBar2 S17.isChar2LieShape_PSp hl2).1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hSpBar2 S17.isChar2LieShape_PSp hu3).1
        (by decide)

theorem exists_mem_inf_mul_centOverO2 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hX : conjClosure D.M L ∈ calC D.M)
    (hTL : D.T ≤ normalizer (conjClosure D.M L : Set G))
    (hns : ¬ S17.SwapsParabolics D.T (conjClosure D.M L)) (hodd : Odd n)
    (hSp : IsSp4 (Bar2 (conjClosure D.M L)) n)
    (hZ : Subgroup.center (Bar2 (conjClosure D.M L)) = ⊥) :
    ∀ t ∈ D.T, ∃ s ∈ D.T ⊓ conjClosure D.M L,
      s⁻¹ * t ∈ F08.CentOverO2 D.M (conjClosure D.M L) := by
  classical
  obtain ⟨hV, -, -, -, hMnorm, hMnorm₀, -⟩ := h.hyp125.pairFacts
  set X := conjClosure D.M L with hXdef
  set T := D.T with hTdef
  have hMstab : D.M ≤ stabTil V₀ V := le_stabTil hMnorm hMnorm₀
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hXstab : X ≤ stabTil V₀ V := hXM.trans hMstab
  have hT2 : IsPGroup 2 T := D.sylowM.isPGroup
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ X) X :=
    S17.isSylowTwoOf_inf_of_mem_calC hX
  have hin := (hpow_and_inner_of_isSp4 D hX hTL hns hodd hSp hZ).1
  intro t ht
  have htnorm : t ∈ normalizer (X : Set G) := hTL ht
  obtain ⟨q, hq⟩ := hin ⟨t, htnorm⟩ ht
  obtain ⟨k, hk⟩ := S17.exists_rhoL_pow_two_pow_eq_one hT2 ⟨t, htnorm⟩ ht
  have hqpow : q ^ 2 ^ k = 1 := by
    have h2 : MulAut.conj (q ^ 2 ^ k) = 1 := by
      rw [map_pow, hq, hk]
    have hcent : q ^ 2 ^ k ∈ Subgroup.center (Bar2 X) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := congrArg (fun φ : MulAut (Bar2 X) => φ y) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at hy
      calc y * q ^ 2 ^ k = ((q ^ 2 ^ k) * y * (q ^ 2 ^ k)⁻¹) * q ^ 2 ^ k := by rw [hy]
        _ = q ^ 2 ^ k * y := by group
    rw [hZ] at hcent
    exact Subgroup.mem_bot.mp hcent
  have hTU : T ≤ normalizer ((T ⊓ X : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer (H := T)) hTL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hqmap : (S17.sylowBar2 X (T ⊓ X)).map (MulAut.conj q).toMonoidHom =
      S17.sylowBar2 X (T ⊓ X) := by
    rw [hq]
    exact S17.rhoL_map_sylowBar2 (L := X) (U := T ⊓ X) ⟨t, htnorm⟩ (hTU ht)
  have hqN : q ∈ normalizer (S17.sylowBar2 X (T ⊓ X) : Set (Bar2 X)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hqmap
  have hqS : q ∈ S17.sylowBar2 X (T ⊓ X) :=
    CFSG.Quasithin.H13.KGHe.mem_of_mem_normalizer_of_pow
      (S17.isSylowTwoOf_sylowBar2_of hSyl) (Subgroup.mem_top q) hqN hqpow
  obtain ⟨s', hs', hsq⟩ := Subgroup.mem_map.1 hqS
  have hsX : (s' : G) ∈ X := (Subgroup.mem_subgroupOf.1 hs').2
  have hsT : (s' : G) ∈ T := (Subgroup.mem_subgroupOf.1 hs').1
  have hsq' : (QuotientGroup.mk s' : Bar2 X) = q := hsq
  have hnorm : (s' : G)⁻¹ * t ∈ normalizer (X : Set G) :=
    Subgroup.mul_mem (Subgroup.normalizer (X : Set G))
      (Subgroup.inv_mem (Subgroup.normalizer (X : Set G)) (Subgroup.le_normalizer hsX)) (hTL ht)
  have hs_eq : UC6S846.rhoL X ⟨(s' : G), Subgroup.le_normalizer hsX⟩ =
      UC6S846.rhoL X ⟨t, htnorm⟩ := by
    rw [UC6S846.rhoL_inner X (s' : G) hsX, hsq', hq]
  have hmul : (⟨(s' : G), Subgroup.le_normalizer hsX⟩ : ↥(normalizer (X : Set G)))⁻¹ *
      ⟨t, htnorm⟩ = ⟨(s' : G)⁻¹ * t, hnorm⟩ := by
    ext
    simp
  have hrho1 : UC6S846.rhoL X ⟨(s' : G)⁻¹ * t, hnorm⟩ = 1 := by
    rw [← hmul, map_mul, map_inv, hs_eq]
    exact inv_mul_cancel _
  have hcomm : ∀ l ∈ X, (s' : G)⁻¹ * t * l * ((s' : G)⁻¹ * t)⁻¹ * l⁻¹ ∈ pCoreOf 2 X := by
    intro l hl
    have hfix : UC6S846.rhoL X ⟨(s' : G)⁻¹ * t, hnorm⟩ (QuotientGroup.mk ⟨l, hl⟩) =
        QuotientGroup.mk ⟨l, hl⟩ := by
      rw [hrho1]
      rfl
    exact (UC6S846.rhoL_fix_iff X ⟨(s' : G)⁻¹ * t, hnorm⟩ ⟨l, hl⟩).1 hfix
  refine ⟨(s' : G), ⟨hsT, hsX⟩, ?_⟩
  refine (mem_centOverO2_iff (X := D.M) (L := X)).2 ⟨?_, ?_⟩
  · exact D.M.mul_mem (D.M.inv_mem (hXM hsX)) (D.sylowM.le ht)
  · intro l hl
    exact hcomm l hl

theorem actTil_eq_mul_of_centOverO2 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hX : conjClosure D.M L ∈ calC D.M)
    (hTL : D.T ≤ normalizer (conjClosure D.M L : Set G))
    (hns : ¬ S17.SwapsParabolics D.T (conjClosure D.M L)) (hodd : Odd n)
    (hSp : IsSp4 (Bar2 (conjClosure D.M L)) n)
    (hZ : Subgroup.center (Bar2 (conjClosure D.M L)) = ⊥) {t : G} (ht : t ∈ D.T)
    (hts : t ∈ stabTil V₀ V) :
    ∃ s ∈ D.T ⊓ conjClosure D.M L, ∃ c ∈ F08.CentOverO2 D.M (conjClosure D.M L),
      t = s * c ∧
      ∀ (hss : s ∈ stabTil V₀ V) (hcs : c ∈ stabTil V₀ V),
        actTil V₀ V h.hyp125.isElemAbelian ⟨t, hts⟩ =
            actTil V₀ V h.hyp125.isElemAbelian ⟨s, hss⟩ *
              actTil V₀ V h.hyp125.isElemAbelian ⟨c, hcs⟩ ∧
          actTil V₀ V h.hyp125.isElemAbelian ⟨c, hcs⟩ ∈
            Subgroup.centralizer (barSub V₀ V h.hyp125.isElemAbelian
              (conjClosure D.M L) : Set _) := by
  classical
  obtain ⟨hV, -, -, -, hMnorm, hMnorm₀, -⟩ := h.hyp125.pairFacts
  set X := conjClosure D.M L with hXdef
  have hMstab : D.M ≤ stabTil V₀ V := le_stabTil hMnorm hMnorm₀
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hXstab : X ≤ stabTil V₀ V := hXM.trans hMstab
  have hXsub : CFSG.Open.IsSubnormal X D.M :=
    CFSG.Open.IsSubnormal.step hXM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L))
      (CFSG.Open.IsSubnormal.refl D.M)
  obtain ⟨s, hs, hc⟩ := exists_mem_inf_mul_centOverO2 D h hX hTL hns hodd hSp hZ t ht
  have hsT : s ∈ D.T := hs.1
  have hsX : s ∈ X := hs.2
  have hcM : s⁻¹ * t ∈ D.M := (mem_centOverO2_iff (X := D.M) (L := X)).1 hc |>.1
  refine ⟨s, hs, s⁻¹ * t, hc, by group, ?_⟩
  intro hss hcs
  constructor
  · have hst : (⟨t, hts⟩ : ↥(stabTil V₀ V)) = ⟨s, hss⟩ * ⟨s⁻¹ * t, hcs⟩ := by
      ext
      simp [mul_assoc]
    rw [hst, map_mul]
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨g, hgX, hgy⟩ := (mem_barSub V₀ V hV X y).1 hy
    have hgl : (g : G) ∈ X := hgX
    have hgls : (g : G) ∈ stabTil V₀ V := hXstab hgl
    have hcomm : (s⁻¹ * t) * (g : G) * (s⁻¹ * t)⁻¹ * (g : G)⁻¹ ∈ pCoreOf 2 X :=
      (mem_centOverO2_iff (X := D.M) (L := X)).1 hc |>.2 (g : G) hgl
    have hcommS : (s⁻¹ * t) * (g : G) * (s⁻¹ * t)⁻¹ * (g : G)⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem
        ((stabTil V₀ V).mul_mem
          ((stabTil V₀ V).mul_mem hcs (hXstab hgl))
          ((stabTil V₀ V).inv_mem hcs))
        ((stabTil V₀ V).inv_mem (hXstab hgl))
    have hzero : actTil V₀ V hV
        ⟨(s⁻¹ * t) * (g : G) * (s⁻¹ * t)⁻¹ * (g : G)⁻¹, hcommS⟩ = 1 := by
      have h2 : barSub V₀ V hV (pCoreOf 2 X) = ⊥ :=
        TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hXsub
          (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125)
      have hmem := actTil_mem_barSub V₀ V hV hcomm hcommS
      rw [h2, Subgroup.mem_bot] at hmem
      exact hmem
    have h4 : actTil V₀ V hV ⟨s⁻¹ * t, hcs⟩ * actTil V₀ V hV ⟨(g : G), hgls⟩ *
        (actTil V₀ V hV ⟨s⁻¹ * t, hcs⟩)⁻¹ *
          (actTil V₀ V hV ⟨(g : G), hgls⟩)⁻¹ = 1 := by
      have hz := hzero
      rw [show actTil V₀ V hV
          ⟨(s⁻¹ * t) * (g : G) * (s⁻¹ * t)⁻¹ * (g : G)⁻¹, hcommS⟩ =
          actTil V₀ V hV (⟨s⁻¹ * t, hcs⟩ * ⟨(g : G), hgls⟩ * ⟨s⁻¹ * t, hcs⟩⁻¹ *
            ⟨(g : G), hgls⟩⁻¹) by
        rfl] at hz
      simpa only [map_mul, map_inv] using hz
    have h5 : actTil V₀ V hV ⟨s⁻¹ * t, hcs⟩ * actTil V₀ V hV ⟨(g : G), hgls⟩ =
        actTil V₀ V hV ⟨(g : G), hgls⟩ * actTil V₀ V hV ⟨s⁻¹ * t, hcs⟩ := by
      refine mul_inv_eq_one.1 ?_
      simpa only [mul_inv_rev, mul_assoc] using h4
    have hgy' : actTil V₀ V hV ⟨(g : G), hgls⟩ = y := hgy
    rw [← hgy']
    exact h5.symm

theorem le_normalizer_preBarSub_of_centOverO2 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) {n : ℕ}
    (hX : conjClosure D.M L ∈ calC D.M)
    (hTL : D.T ≤ normalizer (conjClosure D.M L : Set G))
    (hns : ¬ S17.SwapsParabolics D.T (conjClosure D.M L)) (hodd : Odd n)
    (hSp : IsSp4 (Bar2 (conjClosure D.M L)) n)
    (hZ : Subgroup.center (Bar2 (conjClosure D.M L)) = ⊥)
    {Qbar : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hQX : Qbar ≤ barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))
    (hQ : barSub V₀ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L) ≤
      Subgroup.normalizer (Qbar : Set _)) :
    D.T ≤ Subgroup.normalizer
      (preBarSub (conjClosure D.M L) V₀ V h.hyp125.isElemAbelian Qbar : Set G) := by
  classical
  obtain ⟨hV, -, -, -, hMnorm, hMnorm₀, -⟩ := h.hyp125.pairFacts
  set X := conjClosure D.M L with hXdef
  have hMstab : D.M ≤ stabTil V₀ V := le_stabTil hMnorm hMnorm₀
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hXstab : X ≤ stabTil V₀ V := hXM.trans hMstab
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) :=
    TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hstep : ∀ (x : G) (hxN : x ∈ Subgroup.normalizer (X : Set G))
      (hxS : x ∈ stabTil V₀ V),
      actTil V₀ V hV ⟨x, hxS⟩ ∈ Subgroup.normalizer (Qbar : Set _) →
      ∀ y, y ∈ preBarSub X V₀ V hV Qbar → x * y * x⁻¹ ∈ preBarSub X V₀ V hV Qbar := by
    intro x hxN hxS hxQ y hy
    obtain ⟨hyX, hyS, hyQ⟩ := (mem_preBarSub X V₀ V hV Qbar).1 hy
    have hxyX : x * y * x⁻¹ ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff''.1
        (Subgroup.inv_mem (Subgroup.normalizer (X : Set G)) hxN) y).1 hyX
    have hxyS : x * y * x⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem hxS hyS) ((stabTil V₀ V).inv_mem hxS)
    refine (mem_preBarSub X V₀ V hV Qbar).2 ⟨hxyX, hxyS, ?_⟩
    have hxy : (⟨x * y * x⁻¹, hxyS⟩ : ↥(stabTil V₀ V)) =
        ⟨x, hxS⟩ * ⟨y, hyS⟩ * ⟨x, hxS⟩⁻¹ := rfl
    simp only [hxy, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hxQ (actTil V₀ V hV ⟨y, hyS⟩)).1 hyQ
  have key : ∀ (x : G) (hxN : x ∈ Subgroup.normalizer (X : Set G))
      (hxS : x ∈ stabTil V₀ V),
      actTil V₀ V hV ⟨x, hxS⟩ ∈ Subgroup.normalizer (Qbar : Set _) →
      x ∈ Subgroup.normalizer (preBarSub X V₀ V hV Qbar : Set G) := by
    intro x hxN hxS hxQ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      exact hstep x hxN hxS hxQ y hy
    · exact le_of_eq (Subgroup.card_map_of_injective
        (K := preBarSub X V₀ V hV Qbar) (f := (MulAut.conj x).toMonoidHom)
        (MulAut.conj x).injective).symm
  intro t ht
  have hts : t ∈ stabTil V₀ V := hMstab (D.sylowM.le ht)
  obtain ⟨s, hs, c, hc, ht_eq, hprops⟩ :=
    actTil_eq_mul_of_centOverO2 D h hX hTL hns hodd hSp hZ ht hts
  have hsX : s ∈ X := hs.2
  have hcM : c ∈ D.M := (mem_centOverO2_iff (X := D.M) (L := X)).1 hc |>.1
  have hcs : c ∈ stabTil V₀ V := hMstab hcM
  obtain ⟨-, hcen⟩ := hprops (hXstab hsX) hcs
  have hsN : s ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hsX
  have hsQ : actTil V₀ V hV ⟨s, hXstab hsX⟩ ∈ Subgroup.normalizer (Qbar : Set _) :=
    hQ (actTil_mem_barSub V₀ V hV hs (hXstab hsX))
  have hcCenQ : actTil V₀ V hV ⟨c, hcs⟩ ∈ Subgroup.centralizer (Qbar : Set _) :=
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 hcen) y (hQX hy)
  have hcQ : actTil V₀ V hV ⟨c, hcs⟩ ∈ Subgroup.normalizer (Qbar : Set _) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      have h1 : actTil V₀ V hV ⟨c, hcs⟩ * y * (actTil V₀ V hV ⟨c, hcs⟩)⁻¹ = y := by
        have h2 := (Subgroup.mem_centralizer_iff.1 hcCenQ) y hy
        calc actTil V₀ V hV ⟨c, hcs⟩ * y * (actTil V₀ V hV ⟨c, hcs⟩)⁻¹
            = (y * actTil V₀ V hV ⟨c, hcs⟩) * (actTil V₀ V hV ⟨c, hcs⟩)⁻¹ := by rw [← h2]
          _ = y := by group
      change actTil V₀ V hV ⟨c, hcs⟩ * y * (actTil V₀ V hV ⟨c, hcs⟩)⁻¹ ∈ Qbar
      rw [h1]
      exact hy
    · intro z hz
      refine ⟨z, hz, ?_⟩
      have h2 := (Subgroup.mem_centralizer_iff.1 hcCenQ) z hz
      change actTil V₀ V hV ⟨c, hcs⟩ * z * (actTil V₀ V hV ⟨c, hcs⟩)⁻¹ = z
      calc actTil V₀ V hV ⟨c, hcs⟩ * z * (actTil V₀ V hV ⟨c, hcs⟩)⁻¹
          = (z * actTil V₀ V hV ⟨c, hcs⟩) * (actTil V₀ V hV ⟨c, hcs⟩)⁻¹ := by rw [← h2]
        _ = z := by group
  have hsKey := key s hsN (hXstab hsX) hsQ
  have hcKey := key c (hMX hcM) hcs hcQ
  rw [ht_eq]
  exact Subgroup.mul_mem (Subgroup.normalizer (preBarSub X V₀ V hV Qbar : Set G))
    hsKey hcKey


theorem centralizes_omegaCenter_of_actTil_fixV (D : Data G) {V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D ⊥ V p L)
    {x : G} (hxs : x ∈ stabTil ⊥ V)
    (hfix : ∀ w ∈ CFSG.Quasithin.fixV (barSub ⊥ V h.hyp125.isElemAbelian
        (D.T ⊓ conjClosure D.M L)), actTil ⊥ V h.hyp125.isElemAbelian ⟨x, hxs⟩ w = w) :
    ∀ u ∈ V ⊓ CFSG.Quasithin.centerOf D.T, x * u * x⁻¹ = u := by
  classical
  obtain ⟨-, -, -, -, hMnorm, -, -⟩ := h.hyp125.pairFacts
  have hTnormV : D.T ≤ Subgroup.normalizer (V : Set G) := D.sylowM.le.trans hMnorm
  intro u hu
  obtain ⟨huV, huC⟩ := hu
  obtain ⟨huT, huZ⟩ := huC
  have huZ' : ∀ t ∈ D.T, t * u = u * t := by
    intro t ht
    exact Subgroup.mem_centralizer_iff.1 huZ t ht
  have hmem : tilOf ⊥ V h.hyp125.isElemAbelian u huV ∈ CFSG.Quasithin.fixV
      (barSub ⊥ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L)) := by
    rw [CFSG.Quasithin.mem_fixV]
    intro y hy
    obtain ⟨t, ht, hty⟩ :=
      (mem_barSub ⊥ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L) y).1 hy
    have htV : (t : G) * u * (t : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hTnormV ht.1) u).1 huV
    have htu : (t : G) * u * (t : G)⁻¹ = u := by
      rw [huZ' (t : G) ht.1]
      group
    have hact : actTil ⊥ V h.hyp125.isElemAbelian t
        (tilOf ⊥ V h.hyp125.isElemAbelian u huV) =
        tilOf ⊥ V h.hyp125.isElemAbelian ((t : G) * u * (t : G)⁻¹) htV := by
      unfold tilOf
      rw [actTil_mk]
      congr 1
    have htu' : tilOf ⊥ V h.hyp125.isElemAbelian ((t : G) * u * (t : G)⁻¹) htV =
        tilOf ⊥ V h.hyp125.isElemAbelian u huV := by
      unfold tilOf
      congr 1
      exact Subtype.ext htu
    have hmem' : actTil ⊥ V h.hyp125.isElemAbelian t
        (tilOf ⊥ V h.hyp125.isElemAbelian u huV) =
        tilOf ⊥ V h.hyp125.isElemAbelian u huV :=
      hact.trans htu'
    rwa [hty] at hmem'
  exact conj_eq_of_actTil_tilOf_eq_of_bot h.hyp125.isElemAbelian rfl hxs huV
    (hfix (tilOf ⊥ V h.hyp125.isElemAbelian u huV) hmem)

theorem normalizer_inf_of_actTil_mem_normalizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hsimple : IsSimpleGroup (Bar2 (conjClosure D.M L)))
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥)
    {b : G} (hb : b ∈ conjClosure D.M L) (hbs : b ∈ stabTil V₀ V)
    (hbn : actTil V₀ V h.hyp125.isElemAbelian ⟨b, hbs⟩ ∈
      Subgroup.normalizer (barSub V₀ V h.hyp125.isElemAbelian
        (D.T ⊓ conjClosure D.M L) : Set _)) :
    b ∈ Subgroup.normalizer (D.T ⊓ conjClosure D.M L : Set G) := by
  classical
  have hpre : b ∈ Subgroup.normalizer
      (preBarSub (conjClosure D.M L) V₀ V h.hyp125.isElemAbelian
        (barSub V₀ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L)) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      obtain ⟨hyX, hys, hyS⟩ :=
        (mem_preBarSub (conjClosure D.M L) V₀ V h.hyp125.isElemAbelian _).1 hy
      have hbyX : b * y * b⁻¹ ∈ conjClosure D.M L :=
        (conjClosure D.M L).mul_mem ((conjClosure D.M L).mul_mem hb hyX)
          ((conjClosure D.M L).inv_mem hb)
      have hbyS : b * y * b⁻¹ ∈ stabTil V₀ V :=
        (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem hbs hys) ((stabTil V₀ V).inv_mem hbs)
      refine (mem_preBarSub (conjClosure D.M L) V₀ V h.hyp125.isElemAbelian _).2
        ⟨hbyX, hbyS, ?_⟩
      have hmem3 : actTil V₀ V h.hyp125.isElemAbelian ⟨b * y * b⁻¹, hbyS⟩ ∈
          barSub V₀ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L) := by
        have hby : actTil V₀ V h.hyp125.isElemAbelian ⟨b * y * b⁻¹, hbyS⟩ =
            actTil V₀ V h.hyp125.isElemAbelian ⟨b, hbs⟩ *
              actTil V₀ V h.hyp125.isElemAbelian ⟨y, hys⟩ *
                (actTil V₀ V h.hyp125.isElemAbelian ⟨b, hbs⟩)⁻¹ := by
          have hsub : (⟨b * y * b⁻¹, hbyS⟩ : ↥(stabTil V₀ V)) =
              ⟨b, hbs⟩ * ⟨y, hys⟩ * ⟨b, hbs⟩⁻¹ := rfl
          rw [hsub, map_mul, map_mul, map_inv]
        rw [hby]
        exact (Subgroup.mem_normalizer_iff.mp hbn
          (actTil V₀ V h.hyp125.isElemAbelian ⟨y, hys⟩)).1 hyS
      exact hmem3
    · exact le_of_eq (Subgroup.card_map_of_injective
        (K := preBarSub (conjClosure D.M L) V₀ V h.hyp125.isElemAbelian
          (barSub V₀ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L)))
        (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective).symm
  have hS : preBarSub (conjClosure D.M L) V₀ V h.hyp125.isElemAbelian
      (barSub V₀ V h.hyp125.isElemAbelian (D.T ⊓ conjClosure D.M L)) =
        D.T ⊓ conjClosure D.M L :=
    preBarSub_S_eq D h hsimple hX1
  rwa [hS] at hpre

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
