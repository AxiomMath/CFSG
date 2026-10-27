module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1G24P
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1G2Even

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11
open CFSG.LieType.Multipliers.G24 CFSG.Fischer CFSG.Quasithin.G2U

namespace G24

section Model


variable {K : Type} [Field K]

@[expose] noncomputable def adjEquiv (σ : K ≃+* F4) (hK : Nat.card K = 4) :
    ↥(adjointGroup .G2 K) ≃* grp :=
  ((adjointGroup .G2 K).equivMapOfInjective _ (glHom_injective σ)).trans
    (MulEquiv.subgroupCongr (map_adjointGroup_eq σ hK))

theorem coe_adjEquiv (σ : K ≃+* F4) (hK : Nat.card K = 4) (x : adjointGroup .G2 K) :
    ((adjEquiv σ hK x : grp) : GL (Fin 14) F4) = glHom σ (x : ModGL .G2 K) :=
  rfl

theorem glHom_xUnit (σ : K ≃+* F4) (i : Fin Tag.G2.rank) (c : K) :
    glHom σ (xUnit .G2 K i c) = FreeGroup.lift genGL (FreeGroup.mk (genWordX i (σ c))) := by
  have hr := root_check
  rw [rootCheck, List.all_eq_true] at hr
  have hic := List.all_eq_true.mp (hr i (List.mem_finRange i)) (σ c) (mem_allF4 _)
  rw [Bool.and_eq_true] at hic
  refine Units.ext ?_
  rw [glHom_apply, coe_glEquiv]
  change endEquiv σ (xOp .G2 K i c) = _
  rw [endEquiv_xOp, val_lift_genGL, ← of_decide_eq_true hic.1, toMat_ofMat]

theorem glHom_yUnit (σ : K ≃+* F4) (i : Fin Tag.G2.rank) (c : K) :
    glHom σ (yUnit .G2 K i c) = FreeGroup.lift genGL (FreeGroup.mk (genWordY i (σ c))) := by
  have hr := root_check
  rw [rootCheck, List.all_eq_true] at hr
  have hic := List.all_eq_true.mp (hr i (List.mem_finRange i)) (σ c) (mem_allF4 _)
  rw [Bool.and_eq_true] at hic
  refine Units.ext ?_
  rw [glHom_apply, coe_glEquiv]
  change endEquiv σ (yOp .G2 K i c) = _
  rw [endEquiv_yOp, val_lift_genGL, ← of_decide_eq_true hic.2, toMat_ofMat]

theorem card_F4 : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card, F4.card]

@[expose] noncomputable def s0 : adjointGroup .G2 F4 :=
  ⟨xUnit .G2 F4 g2s 1 * yUnit .G2 F4 g2s 1,
    mul_mem (Subgroup.subset_closure ⟨g2s, 1, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨g2s, 1, Or.inr rfl⟩)⟩

theorem adjEquiv_s0 : adjEquiv (RingEquiv.refl F4) card_F4 s0 = G24P.z0 := by
  apply Subtype.ext
  rw [coe_adjEquiv, G24P.z0, G24P.wordElt, coe_lift_gen, G24P.z0Word, ← FreeGroup.mul_mk,
    map_mul]
  change glHom (RingEquiv.refl F4) (xUnit .G2 F4 g2s 1 * yUnit .G2 F4 g2s 1) = _
  rw [map_mul, glHom_xUnit, glHom_yUnit]
  rfl

end Model

section ThreeA


theorem good427_threeA_four
    {z : adjointGroup .G2 F4} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 F4)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    Good427 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F4))) := by
  have h31 : 3 ∣ Nat.card F4 - 1 := by
    rw [card_F4]
  obtain ⟨m, φ, hφinj, hNC, hcomm⟩ := Ronan148H.exists_sl3_threeA h31 hzS hz3 hz1
  set x : adjointGroup .G2 F4 := m * z * m⁻¹ with hx
  let eR : Matrix.SpecialLinearGroup (Fin 3) F4 ≃* φ.range := MonoidHom.ofInjective hφinj
  have hRq : IsQuasisimple φ.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv eR
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  have hodd : Odd (Nat.card (Subgroup.center φ.range)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eR).toEquiv]
    exact G2Even.odd_card_center_sl3
  have hcard : Nat.card φ.range = 60480 := by
    rw [← Nat.card_congr eR.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL,
      CFSG.Open.StatedAPI.card_statedSL_three, card_F4]
    try norm_num
  have hle : ∀ K : Subgroup (adjointGroup .G2 F4),
      K ≤ Subgroup.centralizer ({x} : Set (adjointGroup .G2 F4)) → Group.IsPerfect K →
        K ≤ φ.range := fun K hKC hKp =>
    Ronan148H.le_of_commutators_mem hKC (Subgroup.isPerfect_iff.mp hKp) hcomm
  obtain ⟨hG, -⟩ := good427_onFree_of_perfect_le_qs (y := x) hNC hle hRq hodd
    (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
  exact Good427.of_isConj (isConj_iff.mpr ⟨m, rfl⟩).symm hG

theorem s0_cube
    : s0 ^ 3 = 1 := by
  apply (adjEquiv (RingEquiv.refl F4) card_F4).injective
  rw [map_pow, adjEquiv_s0, G24P.z0_cube, map_one]

theorem s0_ne_one
    : s0 ≠ 1 := by
  intro h
  apply G24P.z0_ne_one
  rw [← adjEquiv_s0, h, map_one]

@[expose] noncomputable def nV : adjointGroup .G2 F4 :=
  ⟨canonicalRep (coxeterSystem .G2) F4 KS11Lie4Proof.wV,
    canonicalRep_mem_adjointGroup _ _ _⟩

theorem conj_s0_mem
    : nV * s0 * nV⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 F4 := by
  rw [KS11Lie4Proof.mem_g2ShortSL2_iff]
  refine ⟨uSL 1 * vSL 1, ?_⟩
  rw [KS11Lie4Proof.rhoV_apply, map_mul, simpleRootSL2_uSL, simpleRootSL2_vSL]
  rfl

theorem good427_s0
    : Good427 (Subgroup.centralizer ({s0} : Set (adjointGroup .G2 F4))) := by
  have hx3 : (nV * s0 * nV⁻¹) ^ 3 = 1 := by rw [conj_pow, s0_cube, mul_one, mul_inv_cancel]
  have hx1 : nV * s0 * nV⁻¹ ≠ 1 := fun h => s0_ne_one (conj_eq_one_iff.mp h)
  exact Good427.of_isConj (isConj_iff.mpr ⟨nV⁻¹, by group⟩)
    (good427_threeA_four conj_s0_mem hx3 hx1)

theorem good427_z0
    : Good427 (Subgroup.centralizer ({G24P.z0} : Set grp)) := by
  refine Good427.of_mulEquiv_centralizer (adjEquiv (RingEquiv.refl F4) card_F4).symm ?_
  rw [← adjEquiv_s0, MulEquiv.symm_apply_apply]
  exact good427_s0

theorem e9MoveBad_grp
    : E9MoveBad grp :=
  G24P.e9MoveBad_grp good427_z0

theorem cubeInner_adj
    : CubeInner (adjointGroup .G2 F4) := by
  intro τ hτ
  by_contra hout
  have hF : Nat.card F4 = 2 ^ 2 := card_F4
  have hchar3 : ringChar F4 ≠ 3 := by
    rw [ringChar.eq F4 2]
    norm_num
  obtain ⟨φ, hφ, -⟩ := CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hchar3
    (by rw [card_F4]) hτ hout
  obtain ⟨h3, -⟩ := CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
    Nat.prime_two (by norm_num) hF hφ
  omega

theorem rankTwo_grp
    : RankTwoData grp :=
  ⟨cubeInner_of_mulEquiv (adjEquiv (RingEquiv.refl F4) card_F4).symm cubeInner_adj,
    G24P.card_le_nine_grp, ⟨_, G24P.e9_grp⟩⟩

theorem center_eq_bot_g24
    {F : Type} [Field F] (hF : Nat.card F = 4) {L : Type} [Group L]
    [Finite L] (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (θ : L ⧸ Subgroup.center L ≃* adjointGroup .G2 F) : Subgroup.center L = ⊥ := by
  haveI : Group.IsPerfect L := hL.1
  set ψ : L →* adjointGroup .G2 F := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψker : ψ.ker = Subgroup.center L := Res6Seitz.ker_centralQuotient θ
  have hψs : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card ψ.ker) := by
    rw [hψker]
    exact Res6Seitz.odd_card_of_isPGroup_three hZ3
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.G2Four.g2_four_exists_section_of_odd hF L ψ
    hψs hψker.le hodd
  have h := CFSG.SectionRank.ker_eq_bot_of_section_of_perfect ψ hψker.le σ hσ
  rwa [hψker] at h

end ThreeA

end G24

open G24

section Row


theorem rowOf427_g2_four
    : ∀ q : TauCeti.PrimePower, q.p = 2 → q.exponent = 2 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowOf427 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 hexp hq S _ _ hs hna ⟨eSX⟩
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 eSX
  rw [hq2, hexp] at hF
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  let eG : S ≃* adjointGroup .G2 F := eA.trans (Ronan148H.adjointQuotientEquivG2 F)
  obtain ⟨σ⟩ := nonempty_ringEquiv_F4 hF4
  let eS : S ≃* grp := eG.trans (adjEquiv σ hF4)
  refine row427_of_e9MoveBad ?_ (RankTwoData.of_mulEquiv eS rankTwo_grp)
    (e9MoveBad_grp.of_mulEquiv eS) ?_
  · intro L _ _ _ hL hZ3 ⟨e'⟩
    exact center_eq_bot_g24 hF4 hL hZ3 (e'.trans eG)
  · rw [Nat.card_congr eS.toEquiv, card_grp]
    norm_num

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
