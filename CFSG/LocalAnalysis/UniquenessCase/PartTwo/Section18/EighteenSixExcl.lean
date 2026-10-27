module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.CGT.Foote82.T66.MC2Quot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev s18XBar (D : Data G) (V₀ V : Subgroup G) (L : Subgroup G)
    (hV : IsElemAbelian 2 V) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  barSub V₀ V hV (UC22.conjClosure D.M L)

@[expose] def alt5_18_6 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  (IsL3 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 1 ∧
    (∃ π : ↥(StatedSL 3 (ZMod 2)) →*
        ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)),
      SumOfNatVia (CFSG.Quasithin.FFModel.nat (StatedSL 3 (ZMod 2)))
        (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 4 π) ∧
    IsSubgroupOfAlt
      ↥(centGroupIn (Mbar D.M V₀ V h.hyp125.isElemAbelian)
        (barSub V₀ V h.hyp125.isElemAbelian L)) 8 ∧
    (7 ∣ Nat.card (centGroupIn (Mbar D.M V₀ V h.hyp125.isElemAbelian)
        (barSub V₀ V h.hyp125.isElemAbelian L)) →
      IsAlt ↥(centGroupIn (Mbar D.M V₀ V h.hyp125.isElemAbelian)
          (barSub V₀ V h.hyp125.isElemAbelian L)) 8 ∨
        IsAlt ↥(centGroupIn (Mbar D.M V₀ V h.hyp125.isElemAbelian)
            (barSub V₀ V h.hyp125.isElemAbelian L)) 7 ∨
        IsL3 ↥(centGroupIn (Mbar D.M V₀ V h.hyp125.isElemAbelian)
            (barSub V₀ V h.hyp125.isElemAbelian L)) 1))

@[expose] def alt6_18_6 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  (Fstar (Mbar D.M V₀ V h.hyp125.isElemAbelian) =
      barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ∧
    CFSG.Blueprint.LieModel
      ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) .PSL 3 2 2 ∧
    (IsIrrOn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ ∧
      E3.mQuot (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ⊥ = 9))

@[expose] def alt7_18_6 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ((Fstar (Mbar D.M V₀ V h.hyp125.isElemAbelian) =
        barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ∧
      ((IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 3 ∧
          (IsIrrOn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ ∧
            E3.mQuot (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ⊥ = 8)) ∨
        (IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 4 ∧
          (IsIrrOn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ ∧
            E3.mQuot (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ⊥ = 16)) ∨
        (IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 ∧
          (IsIrrOn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ ∧
            E3.mQuot (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ⊥ = 16)))) ∨
    (IsZ3xL2_64 ↥(Fstar (Mbar D.M V₀ V h.hyp125.isElemAbelian)) ∧
      (IsIrrOn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ ∧
        E3.mQuot (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ⊥ = 16)))

theorem isChar2LieShape_PSU_five : IsChar2LieShape .PSU 5 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))

theorem fstar_eq_generalizedFittingSubgroupOf {D : Data G} {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) :
    Fstar (Mbar D.M V₀ V hV) =
      CFSG.GorensteinWalter.generalizedFittingSubgroupOf (Mbar D.M V₀ V hV) := by
  rw [UC22.Fstar, CFSG.Adapters.genFittingFStar_eq_foundations,
    ← CFSG.Adapters.generalizedFittingSubgroupOf_top_eq_foundations
      (↥(Mbar D.M V₀ V hV))]
  have hmap : (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)).map (Mbar D.M V₀ V hV).subtype =
      Mbar D.M V₀ V hV := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have h := CFSG.Walter.generalizedFittingSubgroupOf_map_subtype'
    (Mbar D.M V₀ V hV) ⊤
  rwa [hmap] at h

private theorem not_sq_dvd_16320 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 16320 := by
  intro hdvd
  have hpdvd : p ∣ 16320 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hdvd
  have hfac : 16320 = 2 ^ 6 * 3 * 5 * 17 := by norm_num
  rw [hfac] at hpdvd
  rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h | h17
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h3
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (Nat.Prime.dvd_of_dvd_pow hp h))
      · rcases (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).1 h3 with rfl
        norm_num at hdvd
    · rcases (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h5 with rfl
      norm_num at hdvd
  · rcases (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 h17 with rfl
    norm_num at hdvd

theorem not_isL2_four_of_fstar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hF : Fstar (Mbar D.M V₀ V h.hyp125.isElemAbelian) =
      s18XBar D V₀ V L h.hyp125.isElemAbelian)
    (hL2 : IsL2 ↥(s18XBar D V₀ V L h.hyp125.isElemAbelian) 4) : False := by
  set hV := h.hyp125.isElemAbelian with hVdef
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hYdef
  set X : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L) with hXdef
  have hFYX : Fstar Y = X := by
    simpa [hVdef, hYdef, hXdef, s18XBar] using hF
  have hXY : X ≤ Y := by
    rw [hXdef, hYdef]
    exact barSub_mono V₀ V hV (TwelveTwentyThree.conjClosure_le h.hL.1.1.le)
  have hX2 : IsL2 ↥X 4 := by
    simpa [hVdef, hXdef, s18XBar] using hL2
  have hcardX : Nat.card ↥X = 4080 := by
    rw [S17.card_of_isL2 hX2]
    norm_num
  have hFstar_eq : Fstar Y = CFSG.GorensteinWalter.generalizedFittingSubgroupOf Y :=
    fstar_eq_generalizedFittingSubgroupOf (D := D) (V₀ := V₀) (V := V) hV
  have hgen : CFSG.generalizedFitting ↥Y = X.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hXY]
    rw [← CFSG.Adapters.genFittingFStar_eq_foundations]
    exact hFYX
  have hC : Subgroup.centralizer (X.subgroupOf Y : Set ↥Y) ≤ X.subgroupOf Y := by
    have hb := CFSG.centralizer_generalizedFitting_le (↥Y)
    rwa [hgen] at hb
  have hXn : (X.subgroupOf Y).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr ?_
    have hFnormal : CFSG.GorensteinWalter.IsNormalIn
        (CFSG.GorensteinWalter.generalizedFittingSubgroupOf Y) Y :=
      CFSG.GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn Y
    have hXeq : CFSG.GorensteinWalter.generalizedFittingSubgroupOf Y = X :=
      hFstar_eq ▸ hFYX
    rw [hXeq] at hFnormal
    exact CFSG.GorensteinWalter.le_normalizer_of_isNormalIn hFnormal
  have hSC : StatedClassicalModel ↥X .PSL 2 2 4 :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0) hX2
  obtain ⟨eX⟩ := CFSG.Quasithin.F134.nonempty_mulEquiv_psl2 (p := 2) (f := 4) hSC
  let eK : ↥(X.subgroupOf Y) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4) :=
    (Subgroup.subgroupOfEquivOfLe hXY).trans eX
  have hOutDvd : Nat.card (Outer
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))) ∣ 4 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
      (p := 2) (f := 4) Nat.prime_two (GaloisField 2 4)
        (GaloisField.card 2 4 (by norm_num))).1
    simpa using h
  have hIdx : (X.subgroupOf Y).index ∣ 4 :=
    (CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv
      (X.subgroupOf Y) hC eK).trans hOutDvd
  have hcardK : Nat.card ↥(X.subgroupOf Y) = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv
  have hcardYdvd : Nat.card ↥Y ∣ 16320 := by
    have h1 : Nat.card ↥Y =
        Nat.card ↥(X.subgroupOf Y) * (X.subgroupOf Y).index :=
      (Subgroup.card_mul_index (X.subgroupOf Y)).symm
    rw [h1, hcardK, hcardX]
    simpa using mul_dvd_mul (dvd_refl 4080) hIdx
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hcardV₀ : Nat.card V₀ ≤ 4 :=
    ((mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small).trans (by norm_num)
  have hCtildeNormal : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal (D := D) hV hMs
  have h115 := uc22p22q_r115_of D hx h61 V₀ V
    (Hyp125.hyp11 h127 h.hyp125) hcardV₀ p h.hp
  have hprankM : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) :=
    h115.2.2.trans h115.2.1
  have hprankY : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥Y) := by
    rw [hYdef, ← s15_Three_pRank_MBar11 (D := D) hV hMs p]
    exact hprankM
  have hprankY' : 2 ≤ CFSG.Open.pRank p Y := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y]
    exact hprankY
  have hpsq : p ^ 2 ∣ Nat.card Y :=
    CFSG.CGT.Foote82.MC2.sq_dvd_card_of_two_le_pRank
      (p := p) ((D.sig_prime p h.hp).1.one_lt) hprankY'
  exact not_sq_dvd_16320 (D.sig_prime p h.hp).1 (D.sig_prime p h.hp).2
    (hpsq.trans hcardYdvd)

theorem component_le_fstar {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Subgroup (MulAut (Vtil V₀ V hV))}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV)) : K ≤ Fstar (Mbar D.M V₀ V hV) := by
  obtain ⟨hKY, hKtop⟩ := (isComponentOf_iff_subgroupOf (K := K)
    (Y := Mbar D.M V₀ V hV)).mp hK
  have hKcomp : CFSG.IsComponent (K.subgroupOf (Mbar D.M V₀ V hV)) :=
    CFSG.Quasithin.A3.isComponentOf_top_iff.mp hKtop
  have hKle : K.subgroupOf (Mbar D.M V₀ V hV) ≤
      CFSG.generalizedFitting ↥(Mbar D.M V₀ V hV) :=
    (CFSG.LocalCores.component_le_layer hKcomp).trans le_sup_right
  calc K = (K.subgroupOf (Mbar D.M V₀ V hV)).map (Mbar D.M V₀ V hV).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hKY).symm
    _ ≤ (CFSG.generalizedFitting ↥(Mbar D.M V₀ V hV)).map
          (Mbar D.M V₀ V hV).subtype := Subgroup.map_mono hKle
    _ = Fstar (Mbar D.M V₀ V hV) := by
        rw [UC22.Fstar, CFSG.Adapters.genFittingFStar_eq_foundations]

section Certified


theorem not_isL3_of_shape {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hshape : Shape18_6 D L)
    {f : ℕ} (hL3 : IsL3 ↥(s18XBar D V₀ V L h.hyp125.isElemAbelian) f) : False := by
  have hs : IsSimpleGroup ↥(s18XBar D V₀ V L h.hyp125.isElemAbelian) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  have hXeq : s18XBar D V₀ V L h.hyp125.isElemAbelian = barSub V₀ V h.hyp125.isElemAbelian L := by
    unfold s18XBar
    rw [hXL]
  have hL3' : IsL3 (Bar2 L) f :=
    LieModel.of_mulEquiv e.symm (hXeq ▸ hL3)
  rcases hshape with ⟨hne, -⟩ | ⟨-, hB⟩
  · exact absurd hXL hne
  rcases hB with hB | hB | hB | hB
  · exact absurd (lieModel_eq_of_isChar2LieShape hB.1 S17.isChar2LieShape_PSL hL3').2.1
      (by norm_num)
  · exact absurd (lieModel_eq_of_isChar2LieShape hB.1 isChar2LieShape_PSU_five hL3').1
      (by decide)
  · rcases hB.2.2 with hSp | hG2
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp hL3').1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hG2 S17.isChar2LieShape_G2 hL3').1
        (by decide)
  · exact absurd (lieModel_eq_of_isChar2LieShape hB.2 S17.isChar2LieShape_PSU_four hL3').1
      (by decide)

theorem not_isL2_of_shape {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hshape : Shape18_6 D L)
    {m : ℕ} (hm : m = 3 ∨ m = 6)
    (hL2 : IsL2 ↥(s18XBar D V₀ V L h.hyp125.isElemAbelian) m) : False := by
  have hs : IsSimpleGroup ↥(s18XBar D V₀ V L h.hyp125.isElemAbelian) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  have hXeq : s18XBar D V₀ V L h.hyp125.isElemAbelian = barSub V₀ V h.hyp125.isElemAbelian L := by
    unfold s18XBar
    rw [hXL]
  have hL2' : IsL2 (Bar2 L) m :=
    LieModel.of_mulEquiv e.symm (hXeq ▸ hL2)
  rcases hshape with ⟨hne, -⟩ | ⟨-, hB⟩
  · exact absurd hXL hne
  rcases hB with hB | hB | hB | hB
  · obtain ⟨k, hk⟩ := hB.2.2
    have hmk : m = 2 ^ k :=
      (lieModel_eq_of_isChar2LieShape hB.1 S17.isChar2LieShape_PSL hL2').2.2.trans hk
    rcases hm with rfl | rfl
    · have hklt : k < 3 :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by
          rw [← hmk]; norm_num)
      interval_cases k <;> norm_num at hmk
    · have hklt : k < 3 :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by
          rw [← hmk]; norm_num)
      interval_cases k <;> norm_num at hmk
  · exact absurd (lieModel_eq_of_isChar2LieShape hB.1 isChar2LieShape_PSU_five hL2').1
      (by decide)
  · rcases hB.2.2 with hSp | hG2
    · exact absurd (lieModel_eq_of_isChar2LieShape hSp S17.isChar2LieShape_PSp hL2').1
        (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hG2 S17.isChar2LieShape_G2 hL2').1
        (by decide)
  · exact absurd (lieModel_eq_of_isChar2LieShape hB.2 S17.isChar2LieShape_PSU_four hL2').1
      (by decide)

theorem not_isZ3xL2_64_of_shape {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hshape : Shape18_6 D L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥)
    (hZ : IsZ3xL2_64 ↥(Fstar (Mbar D.M V₀ V h.hyp125.isElemAbelian))) : False := by
  set hV := h.hyp125.isElemAbelian with hVdef
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hYdef
  set X : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L) with hXdef
  set F : Subgroup (MulAut (Vtil V₀ V hV)) := Fstar Y with hFdef
  have hZ' : IsZ3xL2_64 ↥F := by
    simpa [hFdef, hYdef, hVdef] using hZ
  have hFstar_eq : F = CFSG.GorensteinWalter.generalizedFittingSubgroupOf Y := by
    rw [hFdef, hYdef]
    exact fstar_eq_generalizedFittingSubgroupOf (D := D) (V₀ := V₀) (V := V) hV
  have hFleY : F ≤ Y := by
    rw [hFstar_eq]
    exact CFSG.GorensteinWalter.generalizedFittingSubgroupOf_le Y
  have hLbar_comp : IsComponentOf (barSub V₀ V hV L) Y := by
    have hmem := barSub_mem_compBar_of_ne_bot (D := D) h.hyp125 h.hL.1
      (by simpa [hVdef] using hLb)
    simpa [compBar, hYdef] using hmem
  let K : Y → Subgroup (MulAut (Vtil V₀ V hV)) := fun φ =>
    (barSub V₀ V hV L).map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom
  have hKcomp : ∀ φ : Y, IsComponentOf (K φ) Y := by
    intro φ
    exact CFSG.Quasithin.B113.isComponentOf_conj hLbar_comp φ.2
  have hKperf : ∀ φ : Y, ⁅K φ, K φ⁆ = K φ := fun φ =>
    Subgroup.isPerfect_iff.mp ((Group.isPerfect_def).2 (hKcomp φ).2.2.1)
  have hKleF : ∀ φ : Y, K φ ≤ F := by
    intro φ
    simpa [hYdef] using component_le_fstar (D := D) (V₀ := V₀) (V := V) hV (hKcomp φ)
  have hXeq : X = ⨆ φ : Y, K φ := by
    simpa [K, hXdef, hVdef, hYdef] using barSub_conjClosure_eq_iSup h
  have hconjEq : UC22.conjClosure Y (barSub V₀ V hV L) = ⨆ φ : Y, K φ := by
    refine le_antisymm ?_ ?_
    · rw [UC22.conjClosure]
      refine iSup_le fun K' => iSup_le fun hK' => ?_
      obtain ⟨φ, hφ, rfl⟩ := hK'
      exact le_iSup (fun φ : Y => K φ) ⟨φ, hφ⟩
    · refine iSup_le fun φ => ?_
      rw [UC22.conjClosure]
      exact le_iSup₂_of_le (K φ) ⟨φ, φ.2, rfl⟩ le_rfl
  have hXconj : X = UC22.conjClosure Y (barSub V₀ V hV L) := hXeq.trans hconjEq.symm
  have hLbar_le_X : barSub V₀ V hV L ≤ X := by
    rw [hXconj]
    exact TwelveTwentyThree.le_conjClosure Y (barSub V₀ V hV L)
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hAcyc, hBL2⟩ := hZ'
  let _ : Group A := hAg
  let _ : Group B := hBg
  let _ : IsCyclic A := hAcyc.1
  have hcommA : IsMulCommutative A := IsCyclic.isMulCommutative
  let π : ↥F →* A := (MonoidHom.fst A B).comp e.toMonoidHom
  have hKpi : ∀ φ : Y, (K φ).subgroupOf F ≤ π.ker := by
    intro φ x hx
    have hperfF : Group.IsPerfect ↥((K φ).subgroupOf F) := by
      let e' : ↥(K φ) ≃* ↥((K φ).subgroupOf F) :=
        (Subgroup.subgroupOfEquivOfLe (hKleF φ)).symm
      have hperfK : Group.IsPerfect ↥(K φ) := Subgroup.isPerfect_iff.mpr (hKperf φ)
      exact Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
    have h := CFSG.Certificates.perfect_hom_comm_trivial
      (π.comp ((K φ).subgroupOf F).subtype) ⟨x, hx⟩
    simpa using h
  have hXle : X ≤ (π.ker).map F.subtype := by
    rw [hXeq]
    refine iSup_le fun φ => ?_
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hKleF φ hx⟩,
      hKpi φ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hXleF : X ≤ F := hXle.trans (Subgroup.map_subtype_le _)
  have hXF_le_ker : X.subgroupOf F ≤ π.ker := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (hXle (Subgroup.mem_subgroupOf.mp hx))
    have hk_eq : k = x := Subtype.ext hkx
    rwa [← hk_eq]
  have hYnorm : Y ≤ Subgroup.normalizer (X : Set (MulAut (Vtil V₀ V hV))) := by
    have h := TwelveTwentyThree.le_normalizer_conjClosure Y (barSub V₀ V hV L)
    rwa [← hXconj] at h
  have hXnF : (X.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXleF).mpr (hFleY.trans hYnorm)
  have hmap_le : (X.subgroupOf F).map e.toMonoidHom ≤
      (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxker := hXF_le_ker hx
    have hxker' : π x = 1 := MonoidHom.mem_ker.mp hxker
    have hfst : (e x).1 = 1 := by
      simpa [π, MonoidHom.comp_apply] using hxker'
    exact Subgroup.mem_prod.mpr ⟨by simpa using hfst, Subgroup.mem_top _⟩
  have hmap_normal : ((X.subgroupOf F).map e.toMonoidHom).Normal :=
    hXnF.map e.toMonoidHom e.surjective
  have hprod_simple : IsSimpleGroup ↥((⊥ : Subgroup A).prod (⊤ : Subgroup B)) := by
    let eProd : ↥((⊥ : Subgroup A).prod (⊤ : Subgroup B)) ≃* B :=
      (Subgroup.prodEquiv (⊥ : Subgroup A) (⊤ : Subgroup B)).trans
        (MulEquiv.uniqueProd.trans Subgroup.topEquiv)
    have hsimpleB : IsSimpleGroup B :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hBL2
    exact MulEquiv.isSimpleGroup eProd
  have hmap_eq : (X.subgroupOf F).map e.toMonoidHom =
      (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
    have hsub_normal : (((X.subgroupOf F).map e.toMonoidHom).subgroupOf
        ((⊥ : Subgroup A).prod (⊤ : Subgroup B))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hmap_normal.conj_mem (n : A × B) hn (g : A × B)
    rcases hprod_simple.eq_bot_or_eq_top_of_normal
      (((X.subgroupOf F).map e.toMonoidHom).subgroupOf
        ((⊥ : Subgroup A).prod (⊤ : Subgroup B))) with hbot | htop
    · exfalso
      have hmapbot : (X.subgroupOf F).map e.toMonoidHom = ⊥ := by
        have h := congrArg
          (Subgroup.map ((⊥ : Subgroup A).prod (⊤ : Subgroup B)).subtype) hbot
        rw [Subgroup.map_subgroupOf_eq_of_le hmap_le, Subgroup.map_bot] at h
        exact h
      have hLbarF_ne : (barSub V₀ V hV L).subgroupOf F ≠ ⊥ := by
        intro hbotL
        have hmapL := congrArg (Subgroup.map F.subtype) hbotL
        rw [Subgroup.map_subgroupOf_eq_of_le
          (hLbar_le_X.trans hXleF), Subgroup.map_bot] at hmapL
        exact hLb (by simpa [hVdef] using hmapL)
      have hLbarF_le : (barSub V₀ V hV L).subgroupOf F ≤ X.subgroupOf F := by
        intro x hx
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hLbar_le_X hx
      have himage_le : ((barSub V₀ V hV L).subgroupOf F).map e.toMonoidHom ≤
          (X.subgroupOf F).map e.toMonoidHom := Subgroup.map_mono hLbarF_le
      rw [hmapbot] at himage_le
      have himage_bot : ((barSub V₀ V hV L).subgroupOf F).map e.toMonoidHom = ⊥ :=
        le_bot_iff.mp himage_le
      exact hLbarF_ne ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp himage_bot)
    · have hmap_top : (X.subgroupOf F).map e.toMonoidHom =
          (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
        have h1 : (((X.subgroupOf F).map e.toMonoidHom).subgroupOf
            ((⊥ : Subgroup A).prod (⊤ : Subgroup B))).map
            ((⊥ : Subgroup A).prod (⊤ : Subgroup B)).subtype =
            (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
          rw [htop, Subgroup.map_top, Subgroup.range_subtype]
        rwa [Subgroup.map_subgroupOf_eq_of_le hmap_le] at h1
      exact hmap_top
  let eXFB : ↥(X.subgroupOf F) ≃* B :=
    (Subgroup.equivMapOfInjective (X.subgroupOf F) e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hmap_eq).trans
        ((Subgroup.prodEquiv (⊥ : Subgroup A) (⊤ : Subgroup B)).trans
          (MulEquiv.uniqueProd.trans Subgroup.topEquiv)))
  have hXF6 : IsL2 ↥(X.subgroupOf F) 6 :=
    LieModel.of_mulEquiv eXFB.symm hBL2
  have hX6 : IsL2 ↥X 6 :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXleF) hXF6
  exact not_isL2_of_shape h hshape (Or.inr rfl) (by simpa [hVdef, hXdef, s18XBar] using hX6)

theorem not_w4_alt5to7 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h : Hyp18 D V₀ V p L)
    (hshape : Shape18_6 D L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥) :
    ¬ (alt5_18_6 D V₀ V p L h ∨ alt6_18_6 D V₀ V p L h ∨ alt7_18_6 D V₀ V p L h) := by
  rintro (h5 | h6 | h7)
  · exact not_isL3_of_shape h hshape h5.1
  · exact not_isL3_of_shape h hshape h6.2.1
  · rcases h7 with ⟨hF, hcase⟩ | ⟨hZ, -⟩
    · rcases hcase with h3 | h4 | h6
      · exact not_isL2_of_shape h hshape (Or.inl rfl) h3.1
      · exact not_isL2_four_of_fstar D hx h61 h127 h hF h4.1
      · exact not_isL2_of_shape h hshape (Or.inr rfl) h6.1
    · exact not_isZ3xL2_64_of_shape h hshape hLb hZ

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
