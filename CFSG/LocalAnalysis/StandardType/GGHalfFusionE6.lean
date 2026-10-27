module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoNum
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoOrder3
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoTransAux
import CFSG.LocalAnalysis.StandardType.GGHalfFrame
import CFSG.LocalAnalysis.StandardType.GGHalfJoinSLCard
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldAlign
import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowOverlap
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutFacts
import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowFieldCover
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapRee
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B1MoreElevenF
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace HalfFusE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.StandardType.GGSixE6Two CFSG.Timmesfeld.LieEmbed

local instance halfFusE6NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

private theorem commutator_map_conj {G : Type*} [Group G] {J : Subgroup G}
    (hJ : commutator ↥J = ⊤) (g : G) :
    commutator ↥(J.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  let e : ↥J ≃* ↥(J.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulEquiv.injective _)
  have hmap : Subgroup.map e.toMonoidHom (commutator ↥J) =
      commutator ↥(J.map (MulAut.conj g).toMonoidHom) := by
    simp only [commutator]
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  rw [hJ, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  exact hmap.symm

private theorem conj_normalizer_mem {G : Type*} [Group G] {g n a : G} {T : Subgroup G}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ T : Subgroup G) : Set G))
    (hT : n * a * n⁻¹ ∈ T) (hne : n * a * n⁻¹ ≠ 1) :
    g * n * g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers (g * a * g⁻¹) ⊔
        T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ ∈
        T.map (MulAut.conj g).toMonoidHom ∧
      (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ ≠ 1 := by
  have hmap : ((Subgroup.zpowers a ⊔ T : Subgroup G).map (MulAut.conj g).toMonoidHom) =
      (Subgroup.zpowers (g * a * g⁻¹) ⊔ T.map (MulAut.conj g).toMonoidHom :
        Subgroup G) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom
      (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  · have heq : (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ =
        (MulAut.conj g) (n * a * n⁻¹) := by
      rw [MulAut.conj_apply]
      group
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨n * a * n⁻¹, hT, rfl⟩
  · intro h
    apply hne
    have h' : g * (n * a * n⁻¹) * g⁻¹ = 1 := by
      calc g * (n * a * n⁻¹) * g⁻¹ =
          (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ := by group
        _ = 1 := h
    calc n * a * n⁻¹ = g⁻¹ * (g * (n * a * n⁻¹) * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h']
      _ = 1 := by group

private def wE6 : List (Fin (Tag.rank .E6)) := [2, 1, 3, 4, 5, 2, 1, 3, 4, 2, 3, 0, 2, 1]

private def wAct (ω : List (Fin (Tag.rank .E6))) (δ : Fin (Tag.rank .E6) → ℤ) :
    Fin (Tag.rank .E6) → ℤ :=
  ω.foldr (fun i v => reflect .E6 i v) δ

private theorem wAct_theta : wAct wE6 (highRoot .E6) = Pi.single 0 1 := by decide +kernel
private theorem wAct_neg_theta : wAct wE6 (-highRoot .E6) = -Pi.single 0 1 := by decide +kernel
private theorem wAct_a0 : wAct wE6 (Pi.single 0 1) = Pi.single 5 1 := by decide +kernel
private theorem wAct_neg_a0 : wAct wE6 (-Pi.single 0 1) = -Pi.single 5 1 := by decide +kernel
private theorem wAct_a3 : wAct wE6 (Pi.single 3 1) = highRoot .E6 := by decide +kernel
private theorem wAct_neg_a3 : wAct wE6 (-Pi.single 3 1) = -highRoot .E6 := by decide +kernel
private theorem wAct_a5 : wAct wE6 (Pi.single 5 1) = Pi.single 3 1 := by decide +kernel
private theorem wAct_neg_a5 : wAct wE6 (-Pi.single 5 1) = -Pi.single 3 1 := by decide +kernel

private theorem wordProd_smul_eq
    (ω : List (Fin (Tag.rank .E6))) (δ : Fin (Tag.rank .E6) → ℤ) :
    (coxeterSystem .E6).wordProd ω • δ = wAct ω δ := by
  induction ω with
  | nil => simp [wAct]
  | cons i ω ih =>
    rw [(coxeterSystem .E6).wordProd_cons, mul_smul, ih, simple_smul]
    rfl

private noncomputable def nW : EC :=
  ⟨E6Pilot.q2WordElt F2 wE6, E6Pilot.q2WordElt_mem_adjointGroup wE6⟩

private noncomputable def uR
    (β : Fin (Tag.rank .E6) → ℤ) : EC :=
  xr β * xr (-β)

private noncomputable def bT :
    Subgroup EC :=
  Subgroup.zpowers (uR (Pi.single 0 1)) ⊔ Subgroup.zpowers (uR (Pi.single 3 1)) ⊔
    Subgroup.zpowers (uR (Pi.single 5 1))

private theorem nW_conj_xr
    {δ : Fin (Tag.rank .E6) → ℤ} (hδ : IsRoot .E6 δ) :
    nW * xr δ * nW⁻¹ = xr (wAct wE6 δ) := by
  haveI : CharP F2 2 := inferInstance
  apply Subtype.ext
  simp only [nW, xr, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [E6Pilot.q2WordElt_conj_pinnedX wE6 hδ, wordProd_smul_eq]

private theorem nW_conj_uR
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    nW * uR β * nW⁻¹ = xr (wAct wE6 β) * xr (wAct wE6 (-β)) := by
  calc nW * uR β * nW⁻¹ = (nW * xr β * nW⁻¹) * (nW * xr (-β) * nW⁻¹) := by
        simp only [uR]; group
    _ = _ := by rw [nW_conj_xr hβ, nW_conj_xr (IsRoot.neg hβ)]

private theorem fusion_model
    {b : EC}
    (hb : b = zE ∨ b = zE⁻¹) :
    nW ∈ Subgroup.normalizer ((Subgroup.zpowers b ⊔ bT : Subgroup EC) : Set EC) ∧
      nW * b * nW⁻¹ ∈ bT ∧ nW * b * nW⁻¹ ≠ 1 := by
  have hθ : IsRoot .E6 (highRoot .E6) := isRoot_highRoot .E6
  have h0 : IsRoot .E6 (Pi.single 0 1 : Fin (Tag.rank .E6) → ℤ) := IsRoot.basis 0
  have h3 : IsRoot .E6 (Pi.single 3 1 : Fin (Tag.rank .E6) → ℤ) := IsRoot.basis 3
  have h5 : IsRoot .E6 (Pi.single 5 1 : Fin (Tag.rank .E6) → ℤ) := IsRoot.basis 5
  have cz : nW * zE * nW⁻¹ = uR (Pi.single 0 1) := by
    have := nW_conj_uR hθ
    rw [wAct_theta, wAct_neg_theta] at this
    exact this
  have c0 : nW * uR (Pi.single 0 1) * nW⁻¹ = uR (Pi.single 5 1) := by
    rw [nW_conj_uR h0, wAct_a0, wAct_neg_a0]; rfl
  have c3 : nW * uR (Pi.single 3 1) * nW⁻¹ = zE := by
    rw [nW_conj_uR h3, wAct_a3, wAct_neg_a3]; rfl
  have c5 : nW * uR (Pi.single 5 1) * nW⁻¹ = uR (Pi.single 3 1) := by
    rw [nW_conj_uR h5, wAct_a5, wAct_neg_a5]; rfl
  have hzb : Subgroup.zpowers b = Subgroup.zpowers zE := by
    rcases hb with rfl | rfl
    · rfl
    · exact Subgroup.zpowers_inv
  have hmap : (Subgroup.zpowers zE ⊔ bT : Subgroup EC).map (MulAut.conj nW).toMonoidHom =
      (Subgroup.zpowers zE ⊔ bT : Subgroup EC) := by
    unfold bT
    simp only [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, cz, c0, c3, c5]
    ac_rfl
  have hu0 : uR (Pi.single 0 1) ∈ bT :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hu0ne : uR (Pi.single 0 1) ≠ 1 := by
    intro h
    have hz : zE = 1 := by
      have h' := congrArg (fun g => nW⁻¹ * g * nW) (cz.trans h)
      simpa [mul_assoc] using h'
    have ho := orderOf_zE
    rw [hz, orderOf_one] at ho
    exact absurd ho (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [hzb]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq
      (H := (Subgroup.zpowers zE ⊔ bT : Subgroup EC))).mpr hmap
  · rcases hb with rfl | rfl
    · rw [cz]; exact hu0
    · rw [show nW * zE⁻¹ * nW⁻¹ = (nW * zE * nW⁻¹)⁻¹ by group, cz]
      exact bT.inv_mem hu0
  · rcases hb with rfl | rfl
    · rw [cz]; exact hu0ne
    · rw [show nW * zE⁻¹ * nW⁻¹ = (nW * zE * nW⁻¹)⁻¹ by group, cz]
      exact inv_ne_one.mpr hu0ne

private theorem card_F2 : Nat.card F2 = 2 := by
  rw [GaloisField.card 2 1 (by omega), pow_one]

private theorem slToAdjointE6_injective :
    Function.Injective (E6Pilot.slToAdjointE6 F2) :=
  E6Pilot.injective_slToAdjointE6_two card_F2

private theorem slToAdjointE6_omegaBlock
    (k : Fin 5) :
    E6Pilot.slToAdjointE6 F2 (omegaBlock 5 k) =
      xr (a5Root k.castSucc k.succ) * xr (a5Root k.succ k.castSucc) := by
  have hm1 : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  apply Subtype.ext
  simp only [omegaBlock, CFSG.LieType.Universal.SpecialLinear.weylRep, map_mul, Subgroup.coe_mul,
    xr, hm1]
  erw [E6Pilot.coe_slToAdjointE6_transvection, E6Pilot.coe_slToAdjointE6_transvection]
  rw [mul_assoc (pinnedX .E6 F2 _ 1 * pinnedX .E6 F2 _ 1), ← pinnedX_add, one_add_one_eq_two,
    gf2_two, pinnedX_zero, mul_one]

private theorem a5Root_b0 : a5Root (Fin.castSucc (0 : Fin 5)) (Fin.succ 0) = Pi.single 0 1 := by
  decide
private theorem a5Root_b0' : a5Root (Fin.succ (0 : Fin 5)) (Fin.castSucc 0) = -Pi.single 0 1 := by
  decide
private theorem a5Root_b2 : a5Root (Fin.castSucc (2 : Fin 5)) (Fin.succ 2) = Pi.single 3 1 := by
  decide
private theorem a5Root_b2' : a5Root (Fin.succ (2 : Fin 5)) (Fin.castSucc 2) = -Pi.single 3 1 := by
  decide
private theorem a5Root_b4 : a5Root (Fin.castSucc (4 : Fin 5)) (Fin.succ 4) = Pi.single 5 1 := by
  decide
private theorem a5Root_b4' : a5Root (Fin.succ (4 : Fin 5)) (Fin.castSucc 4) = -Pi.single 5 1 := by
  decide

private theorem omegaBlock_img0 :
    E6Pilot.slToAdjointE6 F2 (omegaBlock 5 0) = uR (Pi.single 0 1) := by
  rw [slToAdjointE6_omegaBlock, a5Root_b0, a5Root_b0']
  rfl

private theorem omegaBlock_img2 :
    E6Pilot.slToAdjointE6 F2 (omegaBlock 5 2) = uR (Pi.single 3 1) := by
  rw [slToAdjointE6_omegaBlock, a5Root_b2, a5Root_b2']
  rfl

private theorem omegaBlock_img4 :
    E6Pilot.slToAdjointE6 F2 (omegaBlock 5 4) = uR (Pi.single 5 1) := by
  rw [slToAdjointE6_omegaBlock, a5Root_b4, a5Root_b4']
  rfl

private theorem map_halfTorus :
    (halfTorus 5).map (E6Pilot.slToAdjointE6 F2) = bT := by
  rw [halfTorus, MonoidHom.map_closure]
  unfold bT
  simp only [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ⟨k, hk, rfl⟩, rfl⟩
    fin_cases k
    · exact Or.inl (Or.inl omegaBlock_img0)
    · exact absurd hk (by decide)
    · exact Or.inl (Or.inr omegaBlock_img2)
    · exact absurd hk (by decide)
    · exact Or.inr omegaBlock_img4
  · rintro ((rfl | rfl) | rfl)
    · exact ⟨omegaBlock 5 0, ⟨0, rfl, rfl⟩, omegaBlock_img0⟩
    · exact ⟨omegaBlock 5 2, ⟨2, rfl, rfl⟩, omegaBlock_img2⟩
    · exact ⟨omegaBlock 5 4, ⟨4, rfl, rfl⟩, omegaBlock_img4⟩

private theorem exists_conj_bT
    {T' : Subgroup EC} (hTL : T' ≤ lE)
    (hTc : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x) (hT3 : ∀ x ∈ T', x ^ 3 = 1)
    (hcard : Nat.card T' = 27) :
    ∃ l ∈ lE, T'.map (MulAut.conj l).toMonoidHom = bT := by
  have hinj : Function.Injective (E6Pilot.slToAdjointE6 F2) := slToAdjointE6_injective
  have hrange : (E6Pilot.slToAdjointE6 F2).range = lE := E6Pilot.range_slToAdjointE6
  set S : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F2) :=
    T'.comap (E6Pilot.slToAdjointE6 F2)
  have hSmap : S.map (E6Pilot.slToAdjointE6 F2) = T' := Subgroup.map_comap_eq_self (hrange ▸ hTL)
  have hScard : Nat.card S = 27 := by
    rw [← hcard, ← hSmap, Subgroup.card_map_of_injective hinj]
  have hSc : ∀ x ∈ (S : Set (Matrix.SpecialLinearGroup (Fin 6) F2)), ∀ y ∈ (S : Set _),
      x * y = y * x := by
    intro x hx y hy
    apply hinj
    simpa [map_mul] using hTc (E6Pilot.slToAdjointE6 F2 x) hx (E6Pilot.slToAdjointE6 F2 y) hy
  have hS3 : ∀ x ∈ (S : Set (Matrix.SpecialLinearGroup (Fin 6) F2)), x ^ 3 = 1 := by
    intro x hx
    apply hinj
    simpa [map_pow] using hT3 (E6Pilot.slToAdjointE6 F2 x) hx
  obtain ⟨A, hA⟩ := exists_conj_into_halfTorus (n := 5) (S : Set _) hSc hS3
  have hle : S.map (MulAut.conj A⁻¹).toMonoidHom ≤ halfTorus 5 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hA x hx
  have heq : S.map (MulAut.conj A⁻¹).toMonoidHom = halfTorus 5 := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_halfTorus, Subgroup.card_map_of_injective (MulEquiv.injective _), hScard]
    norm_num
  refine ⟨E6Pilot.slToAdjointE6 F2 A⁻¹, hrange ▸ ⟨A⁻¹, rfl⟩, ?_⟩
  rw [← hSmap, ← map_halfTorus, ← heq, Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  simp only [map_mul, map_inv]

private theorem card_sl6_eq_card_lE :
    Nat.card (Matrix.SpecialLinearGroup (Fin (5 + 1)) GGHalf.F2) = Nat.card ↥lE := by
  have hrange : (E6Pilot.slToAdjointE6 GGHalf.F2).range = lE := E6Pilot.range_slToAdjointE6
  show Nat.card (Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2) = _
  rw [Nat.card_congr (MonoidHom.ofInjective slToAdjointE6_injective).toEquiv, hrange]

private theorem le_lE_of_perfect
    {P : Subgroup EC}
    (hP : commutator ↥P = ⊤) (hPZ : P ≤ Subgroup.centralizer ({zE} : Set EC)) : P ≤ lE := by
  set Z : Subgroup EC := Subgroup.centralizer ({zE} : Set EC) with hZdef
  have hZ : Z = Subgroup.zpowers zE ⊔ lE := by rw [hZdef]; exact centralizer_zE.1
  have hlE_le_Z : lE ≤ Z := by rw [hZ]; exact le_sup_right
  have hzp_le_Z : Subgroup.zpowers zE ≤ Z := by rw [hZ]; exact le_sup_left
  have hZ_norm : Z ≤ Subgroup.normalizer (lE : Set EC) := by
    rw [hZ]
    exact sup_le
      (centralizer_zE.2.2.trans (Subgroup.centralizer_le_normalizer (lE : Set EC)))
      (Subgroup.le_normalizer (H := lE))
  have hNnormal : (lE.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hlE_le_Z).2 hZ_norm
  have hsup : (lE.subgroupOf Z) ⊔ (Subgroup.zpowers zE).subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hlE_le_Z hzp_le_Z, Subgroup.subgroupOf_eq_top]
    simpa [sup_comm] using (le_of_eq hZ)
  haveI : (lE.subgroupOf Z).Normal := hNnormal
  haveI : IsMulCommutative (Subgroup.zpowers zE) := Subgroup.zpowers_isMulCommutative zE
  have hHcomm : IsMulCommutative ((Subgroup.zpowers zE).subgroupOf Z) :=
    Subgroup.subgroupOf_isMulCommutative Z (Subgroup.zpowers zE)
  have hcommZ : _root_.commutator ↥Z ≤ lE.subgroupOf Z :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hHcomm
  have hcommZ' : ⁅Z, Z⁆ ≤ lE := by
    have hmap : (_root_.commutator ↥Z).map Z.subtype ≤ (lE.subgroupOf Z).map Z.subtype :=
      Subgroup.map_mono (f := Z.subtype) hcommZ
    rw [Subgroup.map_subtype_commutator Z, Subgroup.map_subgroupOf_eq_of_le hlE_le_Z] at hmap
    exact hmap
  have hPeq : P = ⁅P, P⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_le_self P)
    rw [← Subgroup.map_subtype_commutator P, hP, Subgroup.map_top]
    exact le_of_eq (Subgroup.range_subtype P).symm
  exact hPeq.le.trans ((Subgroup.commutator_mono hPZ hPZ).trans hcommZ')

private theorem lieModel_of_hasLabel_E6 {X : Type} [Group X] (hX : GGHasLabel ⟨.E6, 0, 1⟩ X) :
    CFSG.Blueprint.LieModel X .E6 0 2 1 := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  refine CFSG.Blueprint.LieModel.of_mulEquiv e.symm ?_
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩,
    untwistedChevalleyModel_largeEven .E6 hK⟩)

private theorem exists_ecLift
    {G : Type} [Group G] [Finite G]
    {K' : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple ↥K')
    (hlab : GGHasLabel ⟨.E6, 0, 1⟩ (↥K' ⧸ Subgroup.center ↥K')) :
    ∃ φ : EC →* G, Function.Injective φ ∧ φ.range = K' := by
  obtain ⟨θ⟩ := nonempty_mulEquiv_EC hq.1 (lieModel_of_hasLabel_E6 hlab)
  let φ : EC →* G := K'.subtype.comp θ.symm.toMonoidHom
  refine ⟨φ, ?_, ?_⟩
  · intro p q hpq
    exact θ.symm.injective (Subtype.ext hpq)
  · apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (θ.symm y).2
    · intro x hx
      exact ⟨θ ⟨x, hx⟩, by
        show K'.subtype (θ.symm (θ ⟨x, hx⟩)) = x
        rw [MulEquiv.symm_apply_apply]
        rfl⟩

end HalfFusE6

open CFSG.StandardType.GGSixE6Two HalfFusE6 in
theorem ggHalfFusionE6Input_of_centT31
    (hA1 : E6TwoCentT31) :
    GGHalfFusionE6Input := by
  show GGHalfFusionAt ⟨.E6, 0, 1⟩ 5
  intro G _ _ K' J T kx hq _ hlabK hkx hkxK hJc hZJ hlabJ hTJ hT hTcard
  obtain ⟨φ, hφi, hφr⟩ := exists_ecLift hq hlabK
  rw [← hφr, MonoidHom.range_eq_map] at hkxK
  obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hkxK
  have ha : orderOf a = 3 := (orderOf_injective φ hφi a).symm.trans hkx
  haveI : Finite EC := finite_EC
  have hJK' : J ≤ K' := fun x hx => (hJc.1 hx).1
  have hJrange : J ≤ φ.range := by rw [hφr]; exact hJK'
  have hmapJ : (J.comap φ).map φ = J := Subgroup.map_comap_eq_self hJrange
  let e : ↥(J.comap φ) ≃* ↥J :=
    (Subgroup.equivMapOfInjective (J.comap φ) φ hφi).trans (MulEquiv.subgroupCongr hmapJ)
  have hq₀ : CFSG.Assembly.IsQuasisimple ↥(J.comap φ) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hJc.2.2
  have hJ₀a : J.comap φ ≤ Subgroup.centralizer ({a} : Set EC) := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hφx : φ x * φ a = φ a * φ x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJc.1 hx).2
    apply hφi
    rw [map_mul, map_mul]
    exact hφx
  have hcardJ : Nat.card ↥J = Nat.card (Matrix.SpecialLinearGroup (Fin (5 + 1)) GGHalf.F2) :=
    GGHalfJoin.card_eq_of_hasLabel_typeA (m := 5) (by norm_num) hZJ hlabJ
  have h31J : 31 ∣ Nat.card ↥(J.comap φ) := by
    rw [Nat.card_congr e.toEquiv, hcardJ, card_sl6_eq_card_lE, card_lE]
    exact thirtyOne_dvd_ordA
  have h31 : 31 ∣ Nat.card (Subgroup.centralizer ({a} : Set EC)) :=
    h31J.trans (Subgroup.card_dvd_of_le hJ₀a)
  obtain ⟨g, hg⟩ := e6Two_order3Conj hA1 a ha h31
  set b : EC := g * a * g⁻¹ with hbdef
  have hCb : Subgroup.centralizer ({b} : Set EC) = Subgroup.centralizer ({zE} : Set EC) := by
    rcases hg with h | h
    · rw [h]
    · rw [h, centralizer_zE_inv]
  set J₁ : Subgroup EC := (J.comap φ).map (MulAut.conj g).toMonoidHom
  have hJ₁perf : commutator ↥J₁ = ⊤ := commutator_map_conj hq₀.1 g
  have hJ₁C : J₁ ≤ Subgroup.centralizer ({zE} : Set EC) := by
    rw [← hCb]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp (hJ₀a hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hbdef]
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  have hJ₁L : J₁ ≤ lE := le_lE_of_perfect hJ₁perf hJ₁C
  have hTrange : T ≤ φ.range := by rw [hφr]; exact hTJ.trans hJK'
  have hTmap : (T.comap φ).map φ = T := Subgroup.map_comap_eq_self hTrange
  set T₁ : Subgroup EC := (T.comap φ).map (MulAut.conj g).toMonoidHom with hT₁def
  have hT₁L : T₁ ≤ lE := (Subgroup.map_mono (Subgroup.comap_mono hTJ)).trans hJ₁L
  have hT₁c : ∀ x ∈ T₁, ∀ y ∈ T₁, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxy : x * y = y * x := by
      apply hφi
      have h := hT.1.is_comm.comm (⟨φ x, hx⟩ : ↥T) ⟨φ y, hy⟩
      simpa [map_mul] using congrArg Subtype.val h
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hxy]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  have hT₁3 : ∀ x ∈ T₁, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx3 : x ^ 3 = 1 := by
      apply hφi
      simpa [map_pow] using hT.2 (φ x) hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hx3]
    group
  have hT₁card : Nat.card ↥T₁ = 27 := by
    have h1 : Nat.card ↥T₁ = Nat.card ↥(T.comap φ) :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    have h2 : Nat.card ↥(T.comap φ) = Nat.card ↥T := by
      have h := (Subgroup.card_map_of_injective (f := φ) (K := T.comap φ) hφi).symm
      rw [hTmap] at h
      exact h
    rw [h1, h2, hTcard]
    norm_num
  obtain ⟨l, hlL, hlT⟩ := exists_conj_bT hT₁L hT₁c hT₁3 hT₁card
  have hlb : l * b * l⁻¹ = b := by
    have hlz : l ∈ Subgroup.centralizer ({b} : Set EC) := by
      rw [hCb]; exact lE_le_centralizer_zE hlL
    rw [Subgroup.mem_centralizer_singleton_iff] at hlz
    rw [hlz]; group
  set c : EC := l * g with hcdef
  have hcab : c * a * c⁻¹ = b := by
    calc c * a * c⁻¹ = l * (g * a * g⁻¹) * l⁻¹ := by rw [hcdef]; group
      _ = b := hlb
  have hca : c⁻¹ * b * c⁻¹⁻¹ = a := by
    rw [← hcab]; group
  have hcT : bT.map (MulAut.conj c⁻¹).toMonoidHom = T.comap φ := by
    rw [← hlT, hT₁def, Subgroup.map_map, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id (T.comap φ)]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply, hcdef]
    group
  obtain ⟨hn, hnT, hnne⟩ := fusion_model hg
  obtain ⟨hm, hmT, hmne⟩ := conj_normalizer_mem (g := c⁻¹) hn hnT hnne
  rw [hca, hcT] at hm hmT
  rw [hca] at hmne
  set m : EC := c⁻¹ * nW * c⁻¹⁻¹
  refine ⟨φ m, ?_, ?_, ?_, ?_⟩
  · rw [← hφr, MonoidHom.range_eq_map]
    exact Subgroup.mem_map.mpr ⟨m, Subgroup.mem_top m, rfl⟩
  · have hmap : ((Subgroup.zpowers a ⊔ T.comap φ).map φ) = Subgroup.zpowers (φ a) ⊔ T := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hTmap]
    have hmem : φ m ∈ Subgroup.normalizer (((Subgroup.zpowers a ⊔ T.comap φ).map φ) : Set G) :=
      Subgroup.le_normalizer_map φ (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
    rwa [hmap] at hmem
  · have hmemT : φ (m * a * m⁻¹) ∈ T := by
      rw [← hTmap]
      exact Subgroup.mem_map.mpr ⟨m * a * m⁻¹, hmT, rfl⟩
    simpa only [map_mul, map_inv] using hmemT
  · intro h
    apply hmne
    apply hφi
    simpa only [map_mul, map_inv, map_one] using h

end CFSG.StandardType

end
