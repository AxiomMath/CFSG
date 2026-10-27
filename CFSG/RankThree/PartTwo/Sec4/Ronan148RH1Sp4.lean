module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Sp44
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph
public import CFSG.HardMathSupport.Dickson.Bal207.SpShape
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1LieOrd
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut fieldAut)
open scoped MatrixGroups commutatorElement
open CFSG.GorensteinWalter (PSL2)

section QS

variable {X Y : Type} [Group X] [Group Y]

@[expose] def QSList (C T : Subgroup X) : Prop :=
  ∀ K : Subgroup X, K ≤ C → IsQuasisimple K → (K.subgroupOf C).IsSubnormal → K = T

theorem isSubnormal_subgroupOf_map (e : X ≃* Y) {K C : Subgroup X} (hKC : K ≤ C)
    (h : (K.subgroupOf C).IsSubnormal) :
    ((K.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom)).IsSubnormal := by
  let eC : C ≃* C.map e.toMonoidHom := C.equivMapOfInjective e.toMonoidHom e.injective
  have heC : ∀ x : C, ((eC x : C.map e.toMonoidHom) : Y) = e x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply C e.toMonoidHom e.injective x
  have hmap := Subgroup.IsSubnormal.map (f := (eC : C →* C.map e.toMonoidHom)) eC.surjective h
  have heq : (K.subgroupOf C).map (eC : C →* C.map e.toMonoidHom) =
      (K.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, ← heC x, hxy]
    · rintro ⟨x, hxK, rfl⟩
      refine ⟨⟨x, hKC hxK⟩, hxK, Subtype.ext ?_⟩
      rw [heC]
      rfl
  rwa [heq] at hmap

theorem QSList.map (e : X ≃* Y) {C T : Subgroup X} (h : QSList C T) :
    QSList (C.map e.toMonoidHom) (T.map e.toMonoidHom) := by
  intro K hKC hKq hKs
  have hback : (C.map e.toMonoidHom).map e.symm.toMonoidHom = C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id C
    ext x
    simp
  have hK'C : K.map e.symm.toMonoidHom ≤ C := hback ▸ Subgroup.map_mono hKC
  have hK'q : IsQuasisimple (K.map e.symm.toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective _ e.symm.injective) hKq
  have hK's : ((K.map e.symm.toMonoidHom).subgroupOf C).IsSubnormal := by
    have := isSubnormal_subgroupOf_map e.symm hKC hKs
    rwa [hback] at this
  have h1 := h _ hK'C hK'q hK's
  rw [← h1, Subgroup.map_map]
  convert (Subgroup.map_id K).symm
  ext x
  simp

theorem centralizer_map_mulEquiv (e : X ≃* Y) (x : X) :
    (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y) := by
  ext z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    rwa [map_mul, map_mul, e.apply_symm_apply] at this
  · intro h
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h

variable [Finite X]

theorem eq_of_quasisimple_subnormal {C T : Subgroup X} (hTC : T ≤ C)
    (hTn : ∀ g ∈ C, ∀ s ∈ T, g * s * g⁻¹ ∈ T) (hTq : IsQuasisimple T)
    (hcomm : ∀ u ∈ C, ∀ v ∈ C, (∀ s ∈ T, u * s = s * u) → (∀ s ∈ T, v * s = s * v) →
      u * v = v * u) : QSList C T := by
  intro K hKC hKq hKs
  set T' : Subgroup C := T.subgroupOf C with hT'
  have hT'n : T'.Normal := ⟨fun a ha g => hTn g g.2 a ha⟩
  have hT'c : IsComponent T' :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTC).symm hTq,
      hT'n.isSubnormal⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hT'c hKs with h1 | h1
  ·
    have hTK : T ≤ K := fun s hs => by
      have : (⟨s, hTC hs⟩ : C) ∈ K.subgroupOf C := h1 hs
      exact this
    have hN : (T.subgroupOf K).Normal :=
      ⟨fun a ha g => hTn g (hKC g.2) a ha⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hN with h2 | h2
    · refine le_antisymm (fun k hk => ?_) hTK
      have : (⟨k, hk⟩ : K) ∈ T.subgroupOf K := h2 ▸ Subgroup.mem_top _
      exact this
    ·
      exfalso
      haveI : Group.IsPerfect T := hTq.1
      haveI : Nontrivial T := CFSG.LocalCores.isQuasisimple_nontrivial hTq
      have hcT : ∀ a b : T, a * b = b * a := by
        intro a b
        have ha : (⟨a, hTK a.2⟩ : K) ∈ Subgroup.center K := h2 a.2
        have hab : (a : X) * b = b * a :=
          (congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨b, hTK b.2⟩)).symm
        exact Subtype.ext hab
      haveI : IsMulCommutative T := ⟨⟨hcT⟩⟩
      exact Group.IsPerfect.not_isMulCommutative T inferInstance
  ·
    exfalso
    have hKT : ∀ k ∈ K, ∀ s ∈ T, k * s = s * k := by
      intro k hk s hs
      have hmem : ⁅(⟨s, hTC hs⟩ : C), (⟨k, hKC hk⟩ : C)⁆ ∈ ⁅T', K.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator hs hk
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact (congrArg Subtype.val hmem).symm
    haveI : Group.IsPerfect K := hKq.1
    haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    haveI : IsMulCommutative K := ⟨⟨fun a b => Subtype.ext
      (hcomm a (hKC a.2) b (hKC b.2) (hKT a a.2) (hKT b b.2))⟩⟩
    exact Group.IsPerfect.not_isMulCommutative K inferInstance

theorem good427_of_qsList {C T : Subgroup X} (h : QSList C T) [IsSimpleGroup T]
    (hna : ∃ a b : T, a * b ≠ b * a) (h60 : Nat.card T ≠ 60) : Good427 C := by
  intro K hKC hKq hKs hA5
  have hKT := h K hKC hKq hKs
  subst hKT
  exact not_isA5Type_of_simple hna h60 hA5

end QS

section Transfer




theorem row427_of_noCfg_qs
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (h : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → NoCfgS427 S')
    (hc : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → ∀ y : S', y ≠ 1 →
      y ^ 3 = 1 → ∀ K : Subgroup S', K ≤ Subgroup.centralizer ({y} : Set S') → IsQuasisimple K →
        (K.subgroupOf (Subgroup.centralizer ({y} : Set S'))).IsSubnormal → y ∉ K) :
    Row427 S := by
  intro G _ _ hG A hA _ hθ L hL ⟨e⟩ d hdA hd1 _ hLd K hK htype
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL) hdA
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hσ3 : descAut L ⟨d, hdN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hσ1 : descAut L ⟨d, hdN⟩ ≠ 1 := by
    intro h1
    apply hLd
    have hdC := (descAut_eq_one_iff hL.1.1 ⟨d, hdN⟩).mp h1
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdC l hl
  have hle := map_le_autFix hdN (hK'M.trans inf_le_right)
  have hsn := isSubnormal_bar hdN hK'M hK'sn
  rcases htype with ⟨⟨φ⟩⟩ | ⟨hdK, -⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have eKL : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
    have hK₁q : IsQuasisimple (K'.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eKL.symm hK'q
    have hZK : Subgroup.center (K'.subgroupOf L ⧸ CFSG.pCore 2 (K'.subgroupOf L)) = ⊥ := by
      haveI := (isA5Type_quot_congr eKL hT).isSimpleGroup
      haveI : Group.IsPerfect (K'.subgroupOf L) := hK₁q.1
      exact center_eq_bot_of_isSimpleGroup_of_isPerfect
    have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ :=
      inf_eq_bot_of_center_eq_bot hK₁q hZK le_rfl hZ3
    have eB := equivBar hK'L hinf
    exact (h (L ⧸ Subgroup.center L) ⟨e⟩) _ hσ3 hσ1 _ hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn (isA5Type_quot_congr eB.symm hT)
  ·
    have hZ : Subgroup.center L = ⊥ := hZS L (sectionFourHyp_subgroup hG L) hL.1 hZ3 ⟨e⟩
    have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ := by rw [hZ, inf_bot_eq]
    have eB := equivBar hK'L hinf
    have hdK' : d ∈ K' := hK' ▸ hdK
    have hdL : d ∈ L := hK'L hdK'
    set y : L ⧸ Subgroup.center L := ((⟨d, hdL⟩ : L) : L ⧸ Subgroup.center L) with hy
    have hσ : descAut L ⟨d, hdN⟩ = MulAut.conj y := Ronan148S.descAut_eq_conj hdL
    have hy1 : y ≠ 1 := by
      intro h1
      apply hσ1
      rw [hσ, h1, map_one]
    have hy3 : y ^ 3 = 1 := by
      rw [hy, ← QuotientGroup.mk_pow]
      have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, QuotientGroup.mk_one]
    rw [hσ, autFix_conj] at hle hsn
    refine hc (L ⧸ Subgroup.center L) ⟨e⟩ y hy1 hy3 _ hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn ?_
    exact ⟨⟨d, hdL⟩, hdK', rfl⟩

end Transfer

namespace Sp4

open CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.SpFour (isQuasisimple_sl2 projEquiv
  center_statedProj_eq_bot three_ne_zero_of_charTwo)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem T_le_C : (KFacts.planeSp (F := F) 1).range ≤ Subgroup.centralizer {KFacts.sp4T F} := by
  rintro _ ⟨B, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (KFacts.planeSp_commute _ _).symm

theorem block0Hom_T (h3 : (3 : F) ≠ 0) {s : StatedSp 2 F}
    (hs : s ∈ (KFacts.planeSp (F := F) 1).range) :
    KFacts.block0Hom F h3 ⟨s, T_le_C hs⟩ = 1 := by
  obtain ⟨B, rfl⟩ := hs
  rw [KFacts.block0Hom_apply, KFacts.coe_planeSp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KFacts.block0, KFacts.planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat]

theorem T_normal (r : StatedSp 2 F) (hr : r ∈ Subgroup.centralizer {KFacts.sp4T F})
    (s : StatedSp 2 F) (hs : s ∈ (KFacts.planeSp (F := F) 1).range) :
    r * s * r⁻¹ ∈ (KFacts.planeSp (F := F) 1).range := by
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charTwo
  have hsC := T_le_C hs
  have hm : r * s * r⁻¹ ∈ Subgroup.centralizer {KFacts.sp4T F} :=
    mul_mem (mul_mem hr hsC) (inv_mem hr)
  refine KFacts.mem_range_planeSp_one h3 hm ?_
  have key : KFacts.block0Hom F h3 (⟨r, hr⟩ * ⟨s, hsC⟩ * ⟨r, hr⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, block0Hom_T h3 hs, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [KFacts.block0Hom_apply] at key
  exact key

noncomputable def TEquiv : SL(2, F) ≃* (KFacts.planeSp (F := F) 1).range :=
  MonoidHom.ofInjective (KFacts.planeSp_injective (F := F) 1)

theorem eq_one_of_central_T {s : StatedSp 2 F} (hs : s ∈ (KFacts.planeSp (F := F) 1).range)
    (hc : ∀ s' ∈ (KFacts.planeSp (F := F) 1).range, s * s' = s' * s) : s = 1 := by
  obtain ⟨B, rfl⟩ := hs
  have hB : B ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B'
    apply KFacts.planeSp_injective (F := F) 1
    rw [map_mul, map_mul]
    exact (hc _ ⟨B', rfl⟩).symm
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at hB
  rw [hB, map_one]

theorem comm_of_centralize_T (u : StatedSp 2 F) (hu : u ∈ Subgroup.centralizer {KFacts.sp4T F})
    (v : StatedSp 2 F) (hv : v ∈ Subgroup.centralizer {KFacts.sp4T F})
    (huT : ∀ s ∈ (KFacts.planeSp (F := F) 1).range, u * s = s * u)
    (hvT : ∀ s ∈ (KFacts.planeSp (F := F) 1).range, v * s = s * v) : u * v = v * u := by
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charTwo
  set ψ := KFacts.block0Hom F h3
  have hbc : ψ ⟨u, hu⟩ * ψ ⟨v, hv⟩ = ψ ⟨v, hv⟩ * ψ ⟨u, hu⟩ :=
    KFacts.commute_of_commute_ordThreeMat
      (KFacts.block0_mul_ordThreeMat h3 (KFacts.mul_planeBlock_eq_of_mem_centralizer hu))
      (KFacts.block0_mul_ordThreeMat h3 (KFacts.mul_planeBlock_eq_of_mem_centralizer hv))
  set w : Subgroup.centralizer {KFacts.sp4T F} := (⟨v, hv⟩ * ⟨u, hu⟩)⁻¹ * (⟨u, hu⟩ * ⟨v, hv⟩)
  have hw1 : ψ w = 1 := by
    have h1 : ψ (⟨u, hu⟩ * ⟨v, hv⟩) = ψ (⟨v, hv⟩ * ⟨u, hu⟩) := by rw [map_mul, map_mul, hbc]
    rw [map_mul, h1, ← map_mul, inv_mul_cancel, map_one]
  have hwT : (w : StatedSp 2 F) ∈ (KFacts.planeSp (F := F) 1).range :=
    KFacts.mem_range_planeSp_one h3 w.2 (by rw [← KFacts.block0Hom_apply]; exact hw1)
  have hwe : (w : StatedSp 2 F) = u⁻¹ * v⁻¹ * (u * v) := by
    simp [w, mul_inv_rev]
  have hwc : ∀ s ∈ (KFacts.planeSp (F := F) 1).range, (w : StatedSp 2 F) * s = s * w := by
    intro s hs
    have cu : Commute u s := huT s hs
    have cv : Commute v s := hvT s hs
    have c : Commute (u⁻¹ * v⁻¹ * (u * v)) s :=
      (cu.inv_left.mul_left cv.inv_left).mul_left (cu.mul_left cv)
    rw [hwe]
    exact c
  have hw : (w : StatedSp 2 F) = 1 := eq_one_of_central_T hwT hwc
  rw [hwe] at hw
  have h2 : u * v = v * u := by
    have h3' : (v * u)⁻¹ * (u * v) = 1 := by rw [mul_inv_rev]; exact hw
    exact (inv_mul_eq_one.mp h3').symm
  exact h2

theorem T_quasisimple (hF : 4 ≤ Nat.card F) : IsQuasisimple (KFacts.planeSp (F := F) 1).range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv TEquiv (isQuasisimple_sl2 hF)

theorem qsList_C (hF : 4 ≤ Nat.card F) :
    QSList (Subgroup.centralizer {KFacts.sp4T F}) (KFacts.planeSp (F := F) 1).range :=
  eq_of_quasisimple_subnormal T_le_C (fun g hg s hs => T_normal g hg s hs) (T_quasisimple hF)
    fun u hu v hv huT hvT => comm_of_centralize_T u hu v hv huT hvT

theorem sp4T_not_mem_T : KFacts.sp4T F ∉ (KFacts.planeSp (F := F) 1).range := by
  intro h
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charTwo
  have h1 := block0Hom_T h3 h
  rw [KFacts.block0Hom_apply, KFacts.coe_sp4T] at h1
  have h00 := congrFun (congrFun h1 0) 0
  simp [KFacts.block0, KFacts.planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat,
    KFacts.ordThreeMat] at h00

theorem T_simple (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup (KFacts.planeSp (F := F) 1).range ∧
      (∃ a b : (KFacts.planeSp (F := F) 1).range, a * b ≠ b * a) ∧
      Nat.card (KFacts.planeSp (F := F) 1).range = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let e : (KFacts.planeSp (F := F) 1).range ≃* PSL2 F :=
    TEquiv.symm.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm
  obtain ⟨hsimp, hsolv⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable hF
  haveI : IsSimpleGroup (PSL2 F) := hsimp
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hsolv
    haveI : IsMulCommutative (KFacts.planeSp (F := F) 1).range := ⟨⟨hcon⟩⟩
    have : Group.IsSolvable (KFacts.planeSp (F := F) 1).range := inferInstance
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · rw [← Nat.card_congr TEquiv.toEquiv, CFSG.GorensteinWalter.sl2_card_formula]

theorem good427_C (hF : 8 ≤ Nat.card F) : Good427 (Subgroup.centralizer {KFacts.sp4T F}) := by
  have hF4 : 4 ≤ Nat.card F := by omega
  obtain ⟨hs, hna, hcard⟩ := T_simple hF4
  haveI := hs
  refine good427_of_qsList (qsList_C hF4) hna ?_
  rw [hcard]
  intro h
  have h64 : 64 ≤ Nat.card F ^ 2 := by nlinarith
  have : 8 * 63 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul hF (by omega)
  omega

theorem good427_inner (hF : 8 ≤ Nat.card F) {y : StatedProj (StatedSp 2 F)} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) : Good427 (Subgroup.centralizer ({y} : Set (StatedProj (StatedSp 2 F)))) := by
  set x := (projEquiv (F := F)).symm y with hx
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hy3, map_one]
  have hx1 : x ≠ 1 := by
    rw [hx, Ne, map_eq_one_iff _ (MulEquiv.injective _)]
    exact hy1
  obtain ⟨φ, hφ⟩ := KFacts.exists_mulAut_apply_sp4T_eq hx3 hx1
  set ψ : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) := φ.trans projEquiv with hψ
  have hψt : ψ (KFacts.sp4T F) = y := by
    rw [hψ, MulEquiv.trans_apply, hφ, hx, MulEquiv.apply_symm_apply]
  rw [← hψt, ← centralizer_map_mulEquiv]
  exact Good427.map_mulEquiv ψ (good427_C hF)

theorem good427_field {σ : F ≃+* F} (hk : 4 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ)) :
    Good427 (Sec4.autFix (fieldAut 2 F σ)) := by
  set k := CFSG.GH74.GLS.IVK.fixedField σ
  have hC : Sec4.autFix (fieldAut 2 F σ) = ((proj 2 F).comp (KFacts.spIncl σ)).range := by
    ext y
    rw [KFacts.mem_range_proj_spIncl_iff]
    rfl
  let e : StatedSp 2 k ≃* ((proj 2 F).comp (KFacts.spIncl σ)).range :=
    MonoidHom.ofInjective (KFacts.proj_spIncl_injective σ)
  have hq : IsQuasisimple (StatedSp 2 k) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 2 k (by norm_num) (Or.inl (Or.inr hk))
  obtain ⟨hs, hna⟩ := CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple hq
    KFacts.center_statedSp_eq_bot
  rw [hC]
  haveI : IsSimpleGroup ((proj 2 F).comp (KFacts.spIncl σ)).range :=
    (MulEquiv.isSimpleGroup_congr e).mp hs
  refine good427_of_le_simple le_rfl ?_ ?_ fun K hKC _ => hKC
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  · rw [← Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
    intro h
    have h256 : 256 ≤ Nat.card k ^ (2 ^ 2) := by
      calc 256 = 4 ^ (2 ^ 2) := by norm_num
        _ ≤ Nat.card k ^ (2 ^ 2) := Nat.pow_le_pow_left hk _
    have h1 : 1 ≤ (Nat.card k ^ (2 * 1) - 1) * (Nat.card k ^ (2 * 2) - 1) := by
      have a1 : 16 ≤ Nat.card k ^ (2 * 1) := by
        calc 16 = 4 ^ (2 * 1) := by norm_num
          _ ≤ Nat.card k ^ (2 * 1) := Nat.pow_le_pow_left hk _
      have a2 : 256 ≤ Nat.card k ^ (2 * 2) := by
        calc 256 = 4 ^ (2 * 2) := by norm_num
          _ ≤ Nat.card k ^ (2 * 2) := Nat.pow_le_pow_left hk _
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have := Nat.mul_le_mul h256 h1
    omega

theorem noCfgS427_sp4 {n : ℕ} (hn : 4 ≤ n) (hF : Nat.card F = 2 ^ n) :
    NoCfgS427 (StatedProj (StatedSp 2 F)) := by
  have hF8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  intro α h3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf α = 3 := orderOf_eq_prime h3 h1
  by_cases hD : α ∈ (conjAut 2 F).range
  · obtain ⟨A, hA⟩ := hD
    have hin : α ∈ (MulAut.conj : StatedProj (StatedSp 2 F) →* _).range := by
      rw [← hA]
      exact KFacts.conjAut_mem_inner_of_charTwo A
    obtain ⟨y, rfl, hy3, hy1⟩ := RonanKChevTwo.exists_conj_of_isInnerAut
      (RonanKChevTwo.conj_injective_of_center_eq_bot center_statedProj_eq_bot) hord hin
    rw [autFix_conj]
    exact good427_inner hF8 hy3 hy1
  · obtain ⟨σ, hσ, H, rfl⟩ := KFacts.sp4_even_order_three_field_descent α h3 hD
    have hpow := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ, hF] at hpow
    have hk : 4 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) := by
      by_contra hlt
      push Not at hlt
      have h16 : 16 ≤ 2 ^ n := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      interval_cases h : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) <;> omega
    rw [autFix_conj_eq_map]
    exact Good427.map_mulEquiv _ (good427_field hk)

theorem not_mem_of_qs (hF : 4 ≤ Nat.card F) {S' : Type} [Group S'] (e : S' ≃* StatedSp 2 F)
    {y : S'} (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) (K : Subgroup S')
    (hKC : K ≤ Subgroup.centralizer ({y} : Set S')) (hKq : IsQuasisimple K)
    (hKs : (K.subgroupOf (Subgroup.centralizer ({y} : Set S'))).IsSubnormal) : y ∉ K := by
  have hx3 : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hx1 : e y ≠ 1 := by
    rw [Ne, map_eq_one_iff _ e.injective]
    exact hy1
  obtain ⟨φ, hφ⟩ := KFacts.exists_mulAut_apply_sp4T_eq hx3 hx1
  set θ : StatedSp 2 F ≃* S' := φ.trans e.symm with hθ
  have hθt : θ (KFacts.sp4T F) = y := by
    rw [hθ, MulEquiv.trans_apply, hφ, MulEquiv.symm_apply_apply]
  have hqs := (qsList_C hF).map θ
  rw [centralizer_map_mulEquiv, hθt] at hqs
  have hKT := hqs K hKC hKq hKs
  intro hyK
  rw [hKT] at hyK
  obtain ⟨s, hs, hsy⟩ := hyK
  have hst : s = KFacts.sp4T F := by
    apply θ.injective
    rw [hθt]
    exact hsy
  rw [hst] at hs
  exact sp4T_not_mem_T hs

end Sp4

open Sp4

section Rows


theorem isQuasisimple_of_simple_nonab_r
    {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : CFSG.IsQuasisimple S := by
  have hZ : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup hs hna
  have e : (S ⧸ Subgroup.center S) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have hmem : ⁅a, b⁆ ∈ commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
      apply hab
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [hmem, one_mul]
    · exact h
  · haveI := hs
    exact e.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hna
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this

theorem rowOf427_sp48
    : RowOf427 (projSp 2 (GaloisField 2 3)) := by
  haveI : Finite (projSp 2 (GaloisField 2 3)) :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.PGLModel.card_projSp_two_eight]; norm_num)
  refine rowOf427_of_noCfg (fun S _ _ ⟨e⟩ => ?_)
    (by rw [CFSG.PGLModel.card_projSp_two_eight]; norm_num)
  haveI : Finite (StatedProj (StatedSp 2 (GaloisField 2 3))) :=
    Finite.of_equiv _ (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 3)).toEquiv
  exact NoCfgS427.of_mulEquiv (e.trans (CFSG.PGLModel.projSpEquivStatedProj 2 _))
    (noCfgS427_of_compShape not_isA5Type_of_spCompType fun β h3 h1 =>
      CFSG.HardMathSupport.Dickson.Bal207.compShape_psp (GaloisField.card 2 3 (by norm_num))
        (Or.inr rfl) le_rfl (by decide) β h3 h1)

theorem rowOf427_sp4
    : ∀ n : ℕ, 1 ≤ n → RowOf427 (projSp 2 (GaloisField 2 n)) := by
  intro n hn
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | rfl | hn4
  · intro S _ _ hs hna ⟨e⟩
    exact (RonanKChevTwo.SpFour.false_of_isQuasisimple_projSp_two_one
      (isQuasisimple_of_simple_nonab_r hs hna) e).elim
  · exact rowOf427_sp44
  · exact rowOf427_sp48
  · intro S _ _ hs hna ⟨eSX⟩
    have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have hF4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    let eP : S ≃* StatedSp 2 (GaloisField 2 n) :=
      (eSX.trans (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))).trans
        (RonanKChevTwo.SpFour.projEquiv (F := GaloisField 2 n)).symm
    refine row427_of_noCfg_qs ?_ ?_ ?_
    · intro L _ _ _ hL hZ3 ⟨e'⟩
      haveI : Group.IsPerfect L := hL.1
      have hodd : Odd (Nat.card (Subgroup.center L)) := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
        rw [hk]
        exact Odd.pow (by decide)
      exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic
        (K := GaloisField 2 n) (n := 2) hodd
        (e'.trans (eSX.trans (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))))
    · intro S' _ _ ⟨e'⟩
      exact NoCfgS427.of_mulEquiv ((e'.trans eP).trans RonanKChevTwo.SpFour.projEquiv)
        (noCfgS427_sp4 hn4 hF)
    · intro S' _ _ ⟨e'⟩ y hy1 hy3 K hKC hKq hKs
      exact not_mem_of_qs hF4 (e'.trans eP) hy1 hy3 K hKC hKq hKs

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
