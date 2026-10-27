module

public import CFSG.Quasithin.Vol2.Ch12Sec5St
public import CFSG.Quasithin.Vol2.Ch12Sec5Pb
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.LieType.SteinbergBRParabolicResidualImage
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.HSL3S77Case
public import CFSG.Quasithin.Background.HSL3S77SD
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St Matrix
open CFSG.LieType.SteinbergBR.BlockPar CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125Tr

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem autOn_inSubgroup_perfectResidual {X : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (CFSG.inSubgroup CFSG.perfectResidual X) V =
      (CFSG.perfectResidual ↥(autOn X V)).map (autOn X V).subtype := by
  let φ : ↥X →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hXV)
  have hrange : φ.range = autOn X V := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_autOn_iff_exists.mpr ⟨x, hXV x.2, x.2, rfl⟩
    · intro ha
      obtain ⟨x, hx, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
      exact ⟨⟨x, hxX⟩, rfl⟩
  have h1 := (CFSG.perfect_residual_transport φ).1
  rw [perfectResidual_map_subtype_congr hrange] at h1
  rw [← h1]
  ext a
  constructor
  · intro ha
    obtain ⟨x, hx, hxR, rfl⟩ := mem_autOn_iff_exists.mp ha
    obtain ⟨y, hy, rfl⟩ := hxR
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact mem_autOn_iff_exists.mpr ⟨y, hXV y.2, ⟨y, hy, rfl⟩, rfl⟩

theorem autOn_inf_eq_mi (F : Frame125 T L V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    {W : Subgroup G} (hWV : W ≤ V) :
    autOn (L ⊓ Subgroup.normalizer (W : Set G)) V = autOn (mi T L W) V := by
  apply le_antisymm
  · exact A4.autOn_mono (inf_le_inf_right _ le_sup_left)
  · intro a ha
    have haL : a ∈ autOn L V := autOn_mi_le F hLV hTV W ha
    obtain ⟨l, hl, hlL, rfl⟩ := mem_autOn_iff_exists.mp haL
    have hmap := (mem_autOn_mi_iff hWV ⟨_, haL⟩).1 ha
    have hlW : l ∈ Subgroup.normalizer (W : Set G) := by
      apply mem_normalizer_of_conj_le
      intro w hw
      exact hmap ⟨w, hWV hw⟩ hw
    exact mem_autOn_iff_exists.mpr ⟨l, hl, ⟨hlL, hlW⟩, rfl⟩

@[expose] noncomputable def lbarSub (F : Frame125 T L V) (P : Subgroup SL5) :
    Subgroup (MulAut ↥V) :=
  (P.map F.γ.symm.toMonoidHom).map (autOn L V).subtype

omit [Finite G] in
theorem mem_lbarSub {F : Frame125 T L V} {P : Subgroup SL5} {a : MulAut ↥V} :
    a ∈ lbarSub F P ↔ ∃ h : a ∈ autOn L V, F.γ ⟨a, h⟩ ∈ P := by
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨(F.γ.symm g).2, ?_⟩
    change F.γ (F.γ.symm g) ∈ P
    rw [MulEquiv.apply_symm_apply]
    exact hg
  · rintro ⟨h, hP⟩
    exact ⟨⟨a, h⟩, ⟨F.γ ⟨a, h⟩, hP, MulEquiv.symm_apply_apply _ _⟩, rfl⟩

@[expose] noncomputable def lbarSubEquiv (F : Frame125 T L V) (P : Subgroup SL5) :
    ↥(lbarSub F P) ≃* ↥P :=
  ((Subgroup.equivMapOfInjective _ _ (autOn L V).subtype_injective).symm.trans
    (Subgroup.equivMapOfInjective _ _ F.γ.symm.injective).symm)

@[expose] noncomputable def stabK (k : ℕ) : Subgroup SL5 := stabilizer (flagSpace 5 (ZMod 2) k)

theorem mem_stabK {k : ℕ} {g : SL5} : g ∈ stabK k ↔ StabGam k g := by
  rw [stabK, mem_stabilizer_flagSpace_iff]
  exact ⟨fun h i j hj hi => h i j hi hj, fun h i j hi hj => h i j hj hi⟩

omit [Finite G] in
theorem autOn_eq_of_isStab {F : Frame125 T L V} {X : Subgroup G} {k : ℕ} (h : F.IsStab X k) :
    autOn X V = lbarSub F (stabK k) := by
  ext a
  rw [mem_lbarSub]
  constructor
  · intro ha
    exact ⟨h.1 ha, mem_stabK.2 ((h.2 ⟨a, h.1 ha⟩).1 ha)⟩
  · rintro ⟨haL, hst⟩
    exact (h.2 ⟨a, haL⟩).2 (mem_stabK.1 hst)

theorem map_parQ_eq_stabK {d e : ℕ} (hde : d + e = 5) :
    (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))).map
      (reindexSL (ZMod 2) hde).toMonoidHom = stabK d := by
  ext g
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact (mem_parQ_iff_reindex hde M).1 hM
  · intro hg
    refine ⟨(reindexSL (ZMod 2) hde).symm g, (mem_parQ_iff_reindex hde _).2 ?_,
      MulEquiv.apply_symm_apply _ _⟩
    rw [MulEquiv.apply_symm_apply]
    exact hg

@[expose] noncomputable def stabEquivParQ {d e : ℕ} (hde : d + e = 5) :
    ↥(stabK d) ≃* ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))) :=
  ((MulEquiv.subgroupCongr (map_parQ_eq_stabK hde)).symm.trans
    ((reindexSL (ZMod 2) hde).subgroupMap _).symm)

@[expose] noncomputable def autOnEquivParQ {F : Frame125 T L V} {X : Subgroup G} {d e : ℕ}
    (h : F.IsStab X d) (hde : d + e = 5) :
    ↥(autOn X V) ≃*
      ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))) :=
  (MulEquiv.subgroupCongr (autOn_eq_of_isStab h)).trans
    ((lbarSubEquiv F (stabK d)).trans (stabEquivParQ hde))

omit [Finite G] in
theorem quotient_pCore_of_isStab {F : Frame125 T L V} {X : Subgroup G} {d e : ℕ}
    (h : F.IsStab X d) (hde : d + e = 5)
    (hO : S125Pb.NoO2 (GL (Fin e) (ZMod 2) × GL (Fin d) (ZMod 2))) :
    Nonempty (↥(autOn X V) ⧸ CFSG.pCore 2 ↥(autOn X V) ≃*
      Matrix.SpecialLinearGroup (Fin e) (ZMod 2) × Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
  obtain ⟨q⟩ := S125Pb.quotient_pCore_parQ (a := Fin d) (b := Fin e) hO
  exact ⟨(QuotientGroup.congr _ _ (autOnEquivParQ h hde)
    (CFSG.pCore_map_iso 2 _)).trans q⟩

end S125Tr

end CFSG.Quasithin.H13
