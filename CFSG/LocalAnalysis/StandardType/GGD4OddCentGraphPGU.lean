module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeSecond
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

private noncomputable def ggP_Frob1
    {L : Type} [Field L] [CharP L 2] (Fr : L →+* L) :
    ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (weylElt TwistTag.D4.tag L 2 1)).toMonoidHom.comp
    (Units.map (entrywiseHom Fr))

private theorem ggP_Frob1_apply
    {L : Type} [Field L] [CharP L 2] (Fr : L →+* L)
    (m : ModGL TwistTag.D4.tag L) :
    ggP_Frob1 Fr m = weylElt TwistTag.D4.tag L 2 1 * Units.map (entrywiseHom Fr) m *
      (weylElt TwistTag.D4.tag L 2 1)⁻¹ := rfl

private theorem ggP_entrywise_secZ
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {μ : Lˣ}
    (hμ : (μ : L) ^ 2 + μ + 1 = 0) {Fr : L →+* L} (hFrμ : Fr (μ : L) = (μ : L) ^ 2) :
    Units.map (entrywiseHom Fr) (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1) =
      yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 *
        weylElt TwistTag.D4.tag L 2 1 := by
  set P := diagramMap TwistTag.D4 L with hPdef
  set z := yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 with hzdef
  have hPz : P * Units.map (entrywiseHom Fr) z * P⁻¹ = Units.map (entrywiseHom Fr) z := by
    rw [hzdef, map_mul, TriBridge.units_map_entrywiseHom_yUnit,
      TriBridge.units_map_entrywiseHom_xUnit, map_one, hPdef]
    have hPa : diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) =
        yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * diagramMap TwistTag.D4 L :=
      diagramMap_commute_yUnit_two _
    have hPb : diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 2 1 =
        xUnit TwistTag.D4.tag L 2 1 * diagramMap TwistTag.D4 L :=
      diagramMap_commute_xUnit_two _
    have hPab : diagramMap TwistTag.D4 L *
          (yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * xUnit TwistTag.D4.tag L 2 1) =
        (yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * xUnit TwistTag.D4.tag L 2 1) *
          diagramMap TwistTag.D4 L := by
      calc diagramMap TwistTag.D4 L *
            (yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * xUnit TwistTag.D4.tag L 2 1)
          = (diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 2 (Fr (μ : L))) *
              xUnit TwistTag.D4.tag L 2 1 := by rw [← mul_assoc]
        _ = (yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * diagramMap TwistTag.D4 L) *
              xUnit TwistTag.D4.tag L 2 1 := by rw [hPa]
        _ = yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) *
              (diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 2 1) := by rw [mul_assoc]
        _ = yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) *
              (xUnit TwistTag.D4.tag L 2 1 * diagramMap TwistTag.D4 L) := by rw [hPb]
        _ = (yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * xUnit TwistTag.D4.tag L 2 1) *
              diagramMap TwistTag.D4 L := by rw [← mul_assoc]
    calc diagramMap TwistTag.D4 L *
          (yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * xUnit TwistTag.D4.tag L 2 1) *
          (diagramMap TwistTag.D4 L)⁻¹
        = ((yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * xUnit TwistTag.D4.tag L 2 1) *
            diagramMap TwistTag.D4 L) * (diagramMap TwistTag.D4 L)⁻¹ := by rw [hPab]
      _ = yUnit TwistTag.D4.tag L 2 (Fr (μ : L)) * xUnit TwistTag.D4.tag L 2 1 := by group
  have h1 : twistHom TwistTag.D4 L Fr z = z * weylElt TwistTag.D4.tag L 2 1 :=
    twistHom_secZ hμ hFrμ
  rw [twistHom_apply] at h1
  rw [hPz] at h1
  rw [hzdef] at h1
  exact h1

private theorem ggP_graphCentralizer_y0_frob_eq
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {Fr : L →+* L}
    (hFrμ : Fr (μ : L) = (μ : L) ^ 2) :
    graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (secM μ ⊓ (ggP_Frob1 Fr).eqLocus (MonoidHom.id _)).map
        (MulAut.conj (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1)).toMonoidHom := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set z := yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 with hzdef
  have hzG : z ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (yUnit_mem_adjointGroup 2 _) (xUnit_mem_adjointGroup 2 _)
  have hFz : Units.map (entrywiseHom Fr) z = z * weylElt TwistTag.D4.tag L 2 1 := by
    rw [hzdef]
    exact ggP_entrywise_secZ hμ hFrμ
  have hcent : graphCentralizer TwistTag.D4.tag L
      (d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹) =
      (secM μ).map (MulAut.conj z).toMonoidHom := by
    rw [d4TrialityY0_mul_eq_conj h2 hμ, wordUnit_secZWord, ← hzdef, graphCentralizer_conj hzG,
      graphCentralizer_inv, graphCentralizer_secElt_eq h2 hμ]
  rw [hcent]
  ext h
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, hF⟩
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    have hF' : Units.map (entrywiseHom Fr) (z * m * z⁻¹) = z * m * z⁻¹ := hF
    have hconj : Units.map (entrywiseHom Fr) (z * m * z⁻¹) =
        z * (weylElt TwistTag.D4.tag L 2 1 * Units.map (entrywiseHom Fr) m *
          (weylElt TwistTag.D4.tag L 2 1)⁻¹) * z⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFz]
      group
    rw [hconj] at hF'
    show ggP_Frob1 Fr m = m
    rw [ggP_Frob1_apply]
    exact mul_left_cancel (mul_right_cancel hF')
  · rintro ⟨m, ⟨hm, hmF⟩, rfl⟩
    have hmF' : ggP_Frob1 Fr m = m := hmF
    refine ⟨⟨m, hm, rfl⟩, ?_⟩
    have hconj : Units.map (entrywiseHom Fr) (z * m * z⁻¹) =
        z * (weylElt TwistTag.D4.tag L 2 1 * Units.map (entrywiseHom Fr) m *
          (weylElt TwistTag.D4.tag L 2 1)⁻¹) * z⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFz]
      group
    change Units.map (entrywiseHom Fr) (z * m * z⁻¹) = z * m * z⁻¹
    rw [hconj, ← ggP_Frob1_apply, hmF']

private theorem ggP_secFrob_eq_conj
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {μ : Lˣ}
    (hμ : (μ : L) ^ 2 + μ + 1 = 0) {Fr : L →+* L} (hFrμ : Fr (μ : L) = (μ : L) ^ 2) :
    ∃ c : ModGL TwistTag.D4.tag L,
      (∀ m ∈ secM μ, secFrob Fr m = c * ggP_Frob1 Fr m * c⁻¹) ∧
        secFrob Fr (rootDiagUnit TwistTag.D4.tag (secTuple μ)) = c⁻¹ := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set db := rootDiagUnit TwistTag.D4.tag (secTuple μ) with hdbdef
  set D := Units.map (entrywiseHom Fr) db with hDdef
  have hFcomm : ∀ m ∈ secM μ,
      Units.map (entrywiseHom Fr) m * (D * diagramMap TwistTag.D4 L) =
        (D * diagramMap TwistTag.D4 L) * Units.map (entrywiseHom Fr) m := by
    intro m hm
    have h := congrArg (Units.map (entrywiseHom Fr))
      (TriBridge.mul_secElt_of_mem_secM hμ hm)
    rw [map_mul, map_mul, secElt, map_mul, ← hdbdef, units_map_entrywiseHom_diagramMap,
      ← hDdef] at h
    exact h
  have htw : ∀ m ∈ secM μ,
      twistHom TwistTag.D4 L Fr m = D⁻¹ * Units.map (entrywiseHom Fr) m * D := by
    intro m hm
    rw [twistHom_apply]
    calc diagramMap TwistTag.D4 L * Units.map (entrywiseHom Fr) m *
          (diagramMap TwistTag.D4 L)⁻¹
        = D⁻¹ * (D * diagramMap TwistTag.D4 L * Units.map (entrywiseHom Fr) m) *
            (diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = D⁻¹ * (Units.map (entrywiseHom Fr) m *
            (D * diagramMap TwistTag.D4 L)) * (diagramMap TwistTag.D4 L)⁻¹ := by
            rw [← hFcomm m hm]
      _ = D⁻¹ * Units.map (entrywiseHom Fr) m * D := by group
  have hDP' : diagramMap TwistTag.D4 L * D * (diagramMap TwistTag.D4 L)⁻¹ = D := by
    have h := congrArg (Units.map (entrywiseHom Fr))
      (diagramMap_commute_secTuple (L := L) μ)
    rw [map_mul, map_mul, units_map_entrywiseHom_diagramMap, ← hdbdef, ← hDdef] at h
    rw [← h]
    group
  have hdb : secFrob Fr (rootDiagUnit TwistTag.D4.tag (secTuple μ)) =
      (weylElt TwistTag.D4.tag L 2 1 * D⁻¹ * (weylElt TwistTag.D4.tag L 2 1)⁻¹)⁻¹ := by
    have htwdb : twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (secTuple μ)) = D := by
      rw [twistHom_apply, hDP']
    rw [secFrob_apply, htwdb]
    group
  refine ⟨weylElt TwistTag.D4.tag L 2 1 * D⁻¹ * (weylElt TwistTag.D4.tag L 2 1)⁻¹,
    ?_, hdb⟩
  intro m hm
  rw [secFrob_apply, htw m hm, ggP_Frob1_apply]
  group

private theorem ggP_exists_secM_lang2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {n : ℕ} (hn : 1 ≤ n)
    (hFrμ : iterateFrobenius L 2 n (μ : L) = (μ : L) ^ 2) :
    ∃ w ∈ secM μ, w⁻¹ * secFrob (iterateFrobenius L 2 n) w =
      secFrob (iterateFrobenius L 2 n) (rootDiagUnit TwistTag.D4.tag (secTuple μ)) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set Fr := iterateFrobenius L 2 n with hFrdef
  set Q := weylElt TwistTag.D4.tag L 2 1 * diagramMap TwistTag.D4 L with hQdef
  have hEF : entrywiseFrobGL TwistTag.D4.tag L 2 n = Units.map (entrywiseHom Fr) := by
    rw [hFrdef]
  have hsec : ∀ g, frobTwistGL TwistTag.D4.tag L 2 n Q g = secFrob Fr g := by
    intro g
    rw [frobTwistGL_apply, secFrob_apply, twistHom_apply, hQdef, hEF]
    group
  have hirr : IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L (secElt μ))) := by
    rw [graphCentralizer_secElt_eq h2 hμ]
    exact isPointIrreducible_secM h2 μ
  obtain ⟨hZ, -, -, -⟩ := graphCentralizer_realization (secElt μ) hirr
  have hQ : ∀ g ∈ graphCentralizer TwistTag.D4.tag L (secElt μ),
      frobTwistGL TwistTag.D4.tag L 2 n Q g ∈
        graphCentralizer TwistTag.D4.tag L (secElt μ) := by
    intro g hg
    rw [hsec g, graphCentralizer_secElt_eq h2 hμ] at *
    exact (secGraph_secFrob hμ hFrμ hg _ (secPhi_mem hμ ⟨g, hg⟩)).1
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction 2 hZ hn Q hQ
  have hd : rootDiagUnit TwistTag.D4.tag (secTuple μ) ∈ secM μ :=
    TriBridge.secTuple_mem_secM hμ
  have hFd : secFrob Fr (rootDiagUnit TwistTag.D4.tag (secTuple μ)) ∈
      graphCentralizer TwistTag.D4.tag L (secElt μ) := by
    rw [graphCentralizer_secElt_eq h2 hμ]
    exact (secGraph_secFrob hμ hFrμ hd _ (secPhi_mem hμ ⟨_, hd⟩)).1
  obtain ⟨w, hw, hwc⟩ := hlang _ hFd
  rw [graphCentralizer_secElt_eq h2 hμ] at hw
  refine ⟨w, hw, ?_⟩
  rw [hsec w] at hwc
  exact hwc

private theorem ggP_map_secM_frob2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {μ : Lˣ}
    (hμ : (μ : L) ^ 2 + μ + 1 = 0) {Fr : L →+* L} (hFrμ : Fr (μ : L) = (μ : L) ^ 2)
    {w : ModGL TwistTag.D4.tag L} (hw : w ∈ secM μ)
    (hwc : w⁻¹ * secFrob Fr w =
      secFrob Fr (rootDiagUnit TwistTag.D4.tag (secTuple μ))) :
    (secM μ ⊓ (ggP_Frob1 Fr).eqLocus (MonoidHom.id _)).map (MulAut.conj w).toMonoidHom =
      secFixG μ Fr := by
  obtain ⟨c, hFm, hFd⟩ := ggP_secFrob_eq_conj hμ hFrμ
  have hFw : secFrob Fr w = w * c⁻¹ := by
    have h : w⁻¹ * secFrob Fr w = c⁻¹ := by rw [hwc, hFd]
    rw [← h]
    group
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨hmM, hmF⟩ := Subgroup.mem_inf.1 hm
    have hmF' : ggP_Frob1 Fr m = m := hmF
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hw hmM) (inv_mem hw), ?_⟩
    change secFrob Fr (w * m * w⁻¹) = w * m * w⁻¹
    rw [map_mul, map_mul, map_inv, hFw, hFm m hmM, hmF']
    group
  · intro hx
    obtain ⟨hxM, hxF⟩ := Subgroup.mem_inf.1 hx
    have hxF' : secFrob Fr x = x := hxF
    have hmem : w⁻¹ * x * w ∈ secM μ := mul_mem (mul_mem (inv_mem hw) hxM) hw
    refine ⟨w⁻¹ * x * w, Subgroup.mem_inf.2 ⟨hmem, ?_⟩, ?_⟩
    · have h1 : secFrob Fr (w⁻¹ * x * w) = c * (w⁻¹ * x * w) * c⁻¹ := by
        rw [map_mul, map_mul, map_inv, hFw, hxF']
        group
      have h2 := hFm (w⁻¹ * x * w) hmem
      rw [h1] at h2
      exact (mul_left_cancel (mul_right_cancel h2)).symm
    · change w * (w⁻¹ * x * w) * w⁻¹ = x
      group

theorem ggD4OddCent_secondCent_isoPGU
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : Odd n) (hK : Nat.card K = 2 ^ n) :
    IsoPGUThree ↥(graphCentralizer TwistTag.D4.tag K
      (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹)) (2 ^ n) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure K with hL
  haveI : IsAlgClosed L := inferInstance
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c : L, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, hK]
  have hFr' : ∀ c : L, Fr c = c ^ 2 ^ n := fun c => by
    rw [hFrdef]
    exact iterateFrobenius_def 2 n c
  obtain ⟨μ, hμ⟩ := LangTwisted2Proof.exists_cube_root_unit (L := L)
  have hFrμ : Fr (μ : L) = (μ : L) ^ 2 := by
    rw [hFr']
    exact LangTwisted2Proof.pow_two_pow_odd hμ hn
  have hn1 : 1 ≤ n := hn.pos
  have hιA : baseChangeGL (algebraMap K L)
      (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹) =
      d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹ := by
    rw [map_mul, map_inv, baseChangeGL_d4TrialityY0, baseChangeGL_diagramMap]
  have h1 := TriBridge.map_graphCentralizer_eq L Fr hFr
    (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹)
  rw [hιA, ggP_graphCentralizer_y0_frob_eq hμ hFrμ] at h1
  obtain ⟨w, hw, hwc⟩ := ggP_exists_secM_lang2 hμ hn1 hFrμ
  have h5 := ggP_map_secM_frob2 hμ hFrμ hw hwc
  have hcard : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
    GaloisField.card 2 (2 * n) (by omega)
  let _ : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n
      (GaloisField 2 (2 * n)) := ⟨Nat.prime_two, hn1, hcard⟩
  let _ := ZMod.algebra L 2
  let ι : GaloisField 2 (2 * n) →+* L :=
    (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 (2 * n))
      (M := L)).toRingHom
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (Nat.succ_pos (2 ^ n))
  have hcF : c * Fr c = μ := by
    rw [hFr', ← pow_succ']
    exact hc
  have hdet : (secG0Mat (μ : L) c).det ≠ 0 := by
    rw [det_secG0Mat hμ]
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at hc
    exact Units.ne_zero μ hc.symm
  set G₀ : GL (Fin 3) L := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hG : (G₀ : Matrix (Fin 3) (Fin 3) L) *
      Matrix.transpose ((G₀ : Matrix (Fin 3) (Fin 3) L).map Fr) = secH (μ : L) :=
    secG0_mul_frob_transpose hμ hFrμ hcF
  let e1 := (graphCentralizer TwistTag.D4.tag K
    (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹)).equivMapOfInjective _
      (baseChangeGL_injective (algebraMap K L))
  let e3 := ((secM μ ⊓ (ggP_Frob1 Fr).eqLocus (MonoidHom.id _)).equivMapOfInjective
      (MulAut.conj (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1)).toMonoidHom
      (MulAut.conj (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1)).injective).symm
  let e4 := ((secM μ ⊓ (ggP_Frob1 Fr).eqLocus (MonoidHom.id _)).equivMapOfInjective
      (MulAut.conj w).toMonoidHom (MulAut.conj w).injective).trans (MulEquiv.subgroupCongr h5)
  refine ⟨GaloisField 2 (2 * n), inferInstance, inferInstance, ?_,
    ⟨e1.trans ((MulEquiv.subgroupCongr h1).trans (e3.trans (e4.trans
      ((LangTwisted2Proof.secFixEquiv hμ hFrμ).trans
        (LangTwisted2Proof.pguEquivPglFix ι hU hFr' μ hG).symm))))⟩⟩
  rw [hcard, ← pow_mul, mul_comm]

end CFSG.StandardType
