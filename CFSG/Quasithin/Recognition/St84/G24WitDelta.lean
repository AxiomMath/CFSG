module

public import CFSG.Quasithin.Recognition.St84.G24ModelFacts
public import CFSG.Quasithin.Recognition.St84.G24Checks
public import CFSG.Quasithin.Recognition.St84.G24Tools
public import CFSG.Quasithin.Recognition.St84.G24Table
public import CFSG.Quasithin.Recognition.St84.G24WitDecode
public import CFSG.LinearAlgebra.LinearGroups.FourElementFieldTransport
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalParabolic
public import CFSG.GroupTheory.AutomorphismAction.MapEqOfMapsTo

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LinearGroups CFSG.Quasithin.G2U CFSG.Quasithin.St84
open CFSG.GroupTheory CFSG.LieType.Multipliers.G24 CFSG.Certificates
open CFSG.Quasithin.St84.G24Ident CFSG.Quasithin.St84.G24Pc CFSG.Quasithin.St84.G24DC
open CFSG.Quasithin.St84.G24Wit CFSG.Quasithin.St84.G24Table

private noncomputable def phiY : MulAut Y :=
  ((exactEntrywiseAut (τ := .G2) frobeniusF4).subgroupMap (adjointGroup .G2 F4)).trans
    (MulEquiv.subgroupCongr (map_exactEntrywiseAut (τ := .G2) frobeniusF4 (Or.inl rfl)))

private theorem coe_phiY (y : Y) :
    ((phiY y : Y) : ModGL .G2 F4) =
      exactEntrywiseAut (τ := .G2) frobeniusF4 (y : ModGL .G2 F4) := by
  rw [phiY, MulEquiv.trans_apply]
  change ((MulEquiv.subgroupMap (exactEntrywiseAut (τ := .G2) frobeniusF4)
    (adjointGroup .G2 F4)) y : ModGL .G2 F4) =
      (exactEntrywiseAut (τ := .G2) frobeniusF4) (y : ModGL .G2 F4)
  exact MulEquiv.coe_subgroupMap_apply _ _ _

private theorem endEquiv_entrywise (A : ModGL .G2 F4) (a b : Fin 14) :
    CFSG.Quasithin.G2U.endEquiv (RingEquiv.refl F4)
      (entrywiseHom frobeniusF4.toRingHom A) a b =
      (CFSG.Quasithin.G2U.endEquiv (RingEquiv.refl F4) A a b) *
        (CFSG.Quasithin.G2U.endEquiv (RingEquiv.refl F4) A a b) := by
  rw [endEquiv_apply, endEquiv_apply]
  change (RingEquiv.refl F4)
      (entrywise frobeniusF4.toRingHom (A : Module.End F4 (RootModule .G2 F4))
        (Finsupp.single (lab b) 1) (lab a)) =
    (RingEquiv.refl F4) ((A : Module.End F4 (RootModule .G2 F4))
        (Finsupp.single (lab b) 1) (lab a)) *
      (RingEquiv.refl F4) ((A : Module.End F4 (RootModule .G2 F4))
        (Finsupp.single (lab b) 1) (lab a))
  rw [entrywise_single]
  simp [Finsupp.mapRange_apply, frobeniusF4_apply, pow_two]

private theorem toGL_eq_endEquiv (y : Y) :
    (toGL y : Matrix (Fin 14) (Fin 14) F4) =
      CFSG.Quasithin.G2U.endEquiv (RingEquiv.refl F4) (y : ModGL .G2 F4) := by
  rw [toGL, MonoidHom.comp_apply, glHom_apply, coe_glEquiv]
  rfl

private theorem toGL_phiY (y : Y) :
    (toGL (phiY y) : Matrix (Fin 14) (Fin 14) F4) =
      (toGL y : Matrix (Fin 14) (Fin 14) F4).map fun x => x * x := by
  ext a b
  have hL : (toGL (phiY y) : Matrix (Fin 14) (Fin 14) F4) a b =
      CFSG.Quasithin.G2U.endEquiv (RingEquiv.refl F4) (y : ModGL .G2 F4) a b *
        CFSG.Quasithin.G2U.endEquiv (RingEquiv.refl F4) (y : ModGL .G2 F4) a b := by
    rw [toGL_eq_endEquiv (phiY y), coe_phiY,
      exactEntrywiseAut_apply, Units.coe_map, endEquiv_entrywise]
  rw [hL, Matrix.map_apply, toGL_eq_endEquiv y]

private theorem phiY_mapsTo_M1 : ∀ x ∈ M1, phiY x ∈ M1 := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, coe_phiY]
  exact G2q.entrywise_mem_parabolicSubgroup (ρ := frobeniusF4) hx

private theorem phiY_mapsTo_M2 : ∀ x ∈ M2, phiY x ∈ M2 := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, coe_phiY]
  exact G2q.entrywise_mem_parabolicSubgroup (ρ := frobeniusF4) hx

private noncomputable def phiM1 (hM : Facts) : MulAut ↥M1 :=
  mulAutRestrict M1 phiY (map_eq_of_mapsTo phiY phiY_mapsTo_M1)

private noncomputable def phiM2 (hM : Facts) : MulAut ↥M2 :=
  mulAutRestrict M2 phiY (map_eq_of_mapsTo phiY phiY_mapsTo_M2)

private theorem coe_phiM1 (hM : Facts) (x : ↥M1) :
    ((phiM1 hM x : ↥M1) : Y) = phiY (x : Y) := by
  simpa [phiM1] using coe_mulAutRestrict M1 phiY _ x

private theorem coe_phiM2 (hM : Facts) (x : ↥M2) :
    ((phiM2 hM x : ↥M2) : Y) = phiY (x : Y) := by
  simpa [phiM2] using coe_mulAutRestrict M2 phiY _ x

private theorem toGL_prod_gB0 (hM : Facts) (w : List (Fin 4)) :
    (toGL (((w.map gB0).prod) : Y) : Matrix (Fin 14) (Fin 14) F4) =
      Code.decode (Native.evalF (Native.gBN ()) w) := by
  rw [decode_evalF (φ := toGL) (im := Native.gBN ()) (z := gB0)
    (fun l => (hM.toGL_gB0 l).symm) w]

private theorem toMat_wImg_eq (hM : Facts) (i k : ℕ) (hi : i < 12) (hk : k < 4) :
    toMat 14 (((wImg ()).getD i #[]).getD k CFSG.LieType.Multipliers.G24.one14) =
      (toGL ((((wWords.getD i []).getD k []).map gB0).prod) :
        Matrix (Fin 14) (Fin 14) F4) := by
  rw [wImg_getD i k hi hk, ← Code.decode_eq_toMat, toGL_prod_gB0 hM, G24DC.wWords]

private def e1P : Array Mat := (matsOf pc1).1
private def e1Pi : Array Mat := (matsOf pc1).2
private def e2P : Array Mat := (matsOf pc2).1
private def e2Pi : Array Mat := (matsOf pc2).2
private def eA1 : Array Mat := (matsOf [a1, b1, k1]).1
private def eA1i : Array Mat := (matsOf [a1, b1, k1]).2
private def eA2 : Array Mat := (matsOf [a2, b2, k2]).1
private def eA2i : Array Mat := (matsOf [a2, b2, k2]).2
private def beP : Array Mat := (e1Q.map (evalP e1P)).toArray
private def bePi : Array Mat := (e1Q.map (evalPInv e1Pi)).toArray
private def alP : Array Mat := (e1A.map (evalL (eA1, eA1i))).toArray
private def alPi : Array Mat := (e1A.map fun w => evalL (eA1, eA1i) (invW w)).toArray
private def cs : List (Array Mat × Array Mat) :=
  e2Coc.map (cocImgs (e2P, e2Pi) (eA2, eA2i))

private structure WitFacts where
  relsQ1β : ∀ r ∈ relsQ1, evalL (beP, bePi) r = one14
  βgen : ∀ j ∈ List.range 10, evalP beP (e1Q.getD j []) = e1P.getD j one14
  relsAα : ∀ r ∈ relsA, evalL (alP, alPi) r = one14
  conjData : ∀ t ∈ List.range 3, ∀ j ∈ List.range 10,
    conjArr (eA1.getD t one14) (e1P.getD j one14) (eA1i.getD t one14) =
      evalP e1P ((conjQ1.getD t []).getD j []) ∧
    evalP beP ((conjQ1.getD t []).getD j []) =
      conjArr (alP.getD t one14) (beP.getD j one14) (alPi.getD t one14)
  dec1f : ∀ k ∈ List.range 4,
    gB.getD k one14 = mulArr 14 (evalP e1P (dec1.getD k ([], [])).1)
      (evalP eA1 (dec1.getD k ([], [])).2) ∧
    ((wImg ()).getD 2 #[]).getD k one14 =
      mulArr 14 (evalP beP (dec1.getD k ([], [])).1)
        (evalP alP (dec1.getD k ([], [])).2)
  relsAc : ∀ c ∈ cs, ∀ r ∈ relsA, evalL c r = one14
  cocZ : ∀ D ∈ e2Coc, ∀ z ∈ D, ∀ l ∈ z, 6 ≤ l.val
  dec2f : ∀ k ∈ List.range 4,
    gB.getD k one14 = mulArr 14 (evalP e2P (dec2.getD k ([], [])).1)
      (evalP eA2 (dec2.getD k ([], [])).2) ∧
    ∀ s ∈ List.range 4,
      ((wImg ()).getD (4 + s) #[]).getD k one14 =
        mulArr 14 (evalP e2P (dec2.getD k ([], [])).1)
          (evalP (cs.getD s (#[], #[])).1 (dec2.getD k ([], [])).2)
  w0 : (wImg ()).getD 0 #[] = gB
  w1 : (wImg ()).getD 1 #[] = gB.map frobArr
  w3 : (wImg ()).getD 3 #[] = ((wImg ()).getD 2 #[]).map frobArr
  w8 : ∀ s ∈ List.range 4,
    (wImg ()).getD (8 + s) #[] = ((wImg ()).getD (4 + s) #[]).map frobArr

private theorem witFacts : WitFacts := by
  have h := CFSG.Quasithin.St84.wit_check
  simp only [G24Wit.witCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc,
    e1P, e1Pi, e2P, e2Pi, eA1, eA1i, eA2, eA2i, beP, bePi, alP, alPi, cs] at h
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI, hJ, hK, hL, _⟩ := h
  exact ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI, hJ, hK, hL⟩

private theorem pc1Y_mem_Q1 (i : Fin 10) : pc1Y i ∈ Q1 :=
  Subgroup.subset_closure ⟨i, rfl⟩

private theorem A1gen_mem_A1 (i : Fin 3) : A1gen i ∈ A1 :=
  Subgroup.subset_closure ⟨i, rfl⟩

private theorem A2gen_mem_A2 (i : Fin 3) : A2gen i ∈ A2 :=
  Subgroup.subset_closure ⟨i, rfl⟩

private theorem A1gen_eq (i : Fin 3) :
    A1gen i = agY ([a1, b1, k1].getD i.val []) := by
  fin_cases i <;> rfl

private theorem A2gen_eq (i : Fin 3) :
    A2gen i = agY ([a2, b2, k2].getD i.val []) := by
  fin_cases i <;> rfl

private theorem toMat_e1P (hM : Facts) (i : Fin 10) :
    toMat 14 (e1P.getD i.val one14) = (toGL (pc1Y i) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [e1P, matsOf_fst, pc1Y, hM.toGL_agY]

private theorem toMat_e1Pi (hM : Facts) (i : Fin 10) :
    toMat 14 (e1Pi.getD i.val one14) =
      ((toGL (pc1Y i))⁻¹ : GL (Fin 14) F4) := by
  rw [e1Pi, matsOf_snd, ← wordArr_invW, ← hM.toGL_agY, hM.agY_invW, map_inv, pc1Y]

private theorem toMat_e2P (hM : Facts) (i : Fin 10) :
    toMat 14 (e2P.getD i.val one14) = (toGL (pc2Y i) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [e2P, matsOf_fst, pc2Y, hM.toGL_agY]

private theorem toMat_e2Pi (hM : Facts) (i : Fin 10) :
    toMat 14 (e2Pi.getD i.val one14) =
      ((toGL (pc2Y i))⁻¹ : GL (Fin 14) F4) := by
  rw [e2Pi, matsOf_snd, ← wordArr_invW, ← hM.toGL_agY, hM.agY_invW, map_inv, pc2Y]

private theorem toMat_eA1 (hM : Facts) (i : Fin 3) :
    toMat 14 (eA1.getD i.val one14) = (toGL (A1gen i) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [eA1, matsOf_fst, A1gen_eq i, hM.toGL_agY]

private theorem toMat_eA1i (hM : Facts) (i : Fin 3) :
    toMat 14 (eA1i.getD i.val one14) =
      ((toGL (A1gen i))⁻¹ : GL (Fin 14) F4) := by
  rw [eA1i, matsOf_snd, ← wordArr_invW, ← hM.toGL_agY, hM.agY_invW, map_inv, A1gen_eq i]

private theorem toMat_eA2 (hM : Facts) (i : Fin 3) :
    toMat 14 (eA2.getD i.val one14) = (toGL (A2gen i) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [eA2, matsOf_fst, A2gen_eq i, hM.toGL_agY]

private theorem toMat_eA2i (hM : Facts) (i : Fin 3) :
    toMat 14 (eA2i.getD i.val one14) =
      ((toGL (A2gen i))⁻¹ : GL (Fin 14) F4) := by
  rw [eA2i, matsOf_snd, ← wordArr_invW, ← hM.toGL_agY, hM.agY_invW, map_inv, A2gen_eq i]

private def betaQ (j : Fin 10) : ↥Q1 :=
  ⟨((e1Q.getD j.val []).map pc1Y).prod,
    Subgroup.list_prod_mem Q1 (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact pc1Y_mem_Q1 i)⟩

private def alphaY (t : Fin 3) : Y := signedProd A1gen (e1A.getD t.val [])

private def alphaQ (t : Fin 3) : ↥A1 :=
  ⟨alphaY t, signedProd_mem (fun i => A1gen_mem_A1 i) (e1A.getD t.val [])⟩

private theorem toMat_beP (hM : Facts) (j : Fin 10) :
    toMat 14 (beP.getD j.val one14) = (toGL (betaQ j) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [beP, getD_toArray_map (f := evalP e1P) (l := e1Q) (i := j.val) (d := one14)
    (e := []) j.isLt, toMat_evalP (φ := toGL) (y := pc1Y) (G := e1P) (hG := toMat_e1P hM)]
  rfl

private theorem toMat_bePi (hM : Facts) (j : Fin 10) :
    toMat 14 (bePi.getD j.val one14) =
      ((toGL (betaQ j))⁻¹ : GL (Fin 14) F4) := by
  rw [bePi, getD_toArray_map (f := evalPInv e1Pi) (l := e1Q) (i := j.val) (d := one14)
    (e := []) j.isLt, toMat_evalPInv (φ := toGL) (y := pc1Y) (Gi := e1Pi)
    (hGi := toMat_e1Pi hM)]
  rfl

private theorem toMat_alP (hM : Facts) (t : Fin 3) :
    toMat 14 (alP.getD t.val one14) = (toGL (alphaQ t) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [alP, getD_toArray_map (f := evalL (eA1, eA1i)) (l := e1A) (i := t.val) (d := one14)
    (e := []) t.isLt, toMat_evalL (φ := toGL) (y := A1gen) (G := (eA1, eA1i))
    (hG1 := toMat_eA1 hM) (hG2 := toMat_eA1i hM)]
  rfl

private theorem toMat_alPi (hM : Facts) (t : Fin 3) :
    toMat 14 (alPi.getD t.val one14) =
      ((toGL (alphaQ t))⁻¹ : GL (Fin 14) F4) := by
  rw [alPi, getD_toArray_map (f := fun w => evalL (eA1, eA1i) (invW w)) (l := e1A)
    (i := t.val) (d := one14) (e := []) t.isLt,
    toMat_evalL (φ := toGL) (y := A1gen) (G := (eA1, eA1i))
    (hG1 := toMat_eA1 hM) (hG2 := toMat_eA1i hM), invW_eq_invWord (e1A.getD t.val []),
    CFSG.Timmesfeld.Moufang.Exc.signedProd_invWord A1gen (e1A.getD t.val []), map_inv]
  rfl

private theorem normQ1A1 (hM : Facts) : A1 ≤ Subgroup.normalizer (Q1 : Set Y) :=
  hM.A1_le_M1.trans hM.M1_le_normalizer_Q1

private theorem disjoint_Q1_A1 (hM : Facts) : Disjoint Q1 A1 := by
  rw [disjoint_iff, inf_comm, hM.inf_A1_Q1]

private theorem A1Q_coe (t : Fin 3) : ((A1Q t : ↥A1) : Y) = A1gen t := rfl

private theorem pc1Q_coe (j : Fin 10) : ((pc1Q j : ↥Q1) : Y) = pc1Y j := rfl

private theorem pc1Q_prod_coe (w : List (Fin 10)) :
    (((w.map pc1Q).prod : ↥Q1) : Y) = (w.map pc1Y).prod := by
  rw [Subgroup.val_list_prod, List.map_map]
  rfl

private theorem betaQ_rels (hM : Facts) :
    ∀ r ∈ relsQ1, signedProd betaQ r = 1 := by
  intro r hr
  have h := witFacts.relsQ1β r hr
  have hmat : toMat 14 (evalL (beP, bePi) r) = 1 := by
    rw [h, toMat_one14]
  rw [toMat_evalL (φ := toGL.comp Q1.subtype) (y := betaQ) (G := (beP, bePi))
    (hG1 := toMat_beP hM) (hG2 := toMat_bePi hM)] at hmat
  exact Subtype.ext (hM.toGL_injective (Units.ext (by
    simpa [MonoidHom.comp_apply] using hmat)))

private theorem betaQ_gen (hM : Facts) :
    Subgroup.closure (Set.range betaQ) = ⊤ := by
  apply top_unique
  rw [← hM.closure_range_pc1Q]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  have hB := witFacts.βgen j.val (List.mem_range.mpr j.isLt)
  have hmat : toMat 14 (evalP beP (e1Q.getD j.val [])) =
      toMat 14 (e1P.getD j.val one14) := congrArg (toMat 14) hB
  rw [toMat_evalP (φ := toGL.comp Q1.subtype) (y := betaQ) (G := beP)
      (hG := toMat_beP hM), toMat_e1P hM j] at hmat
  have hY : ((((e1Q.getD j.val []).map betaQ).prod : ↥Q1) : Y) = pc1Y j :=
    hM.toGL_injective (Units.ext hmat)
  have hEq : ((e1Q.getD j.val []).map betaQ).prod = pc1Q j := Subtype.ext (by
    rw [hY]
    rfl)
  rw [← hEq]
  exact Subgroup.list_prod_mem (Subgroup.closure (Set.range betaQ)) (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure ⟨i, rfl⟩)

private theorem alphaQ_rels (hM : Facts) :
    ∀ r ∈ relsA, signedProd alphaQ r = 1 := by
  intro r hr
  have h := witFacts.relsAα r hr
  have hmat : toMat 14 (evalL (alP, alPi) r) = 1 := by
    rw [h, toMat_one14]
  rw [toMat_evalL (φ := toGL.comp A1.subtype) (y := alphaQ) (G := (alP, alPi))
    (hG1 := toMat_alP hM) (hG2 := toMat_alPi hM)] at hmat
  exact Subtype.ext (hM.toGL_injective (Units.ext (by
    simpa [MonoidHom.comp_apply] using hmat)))

private theorem alphaQ_gen (hM : Facts) :
    Subgroup.closure (Set.range alphaQ) = ⊤ := by
  apply top_unique
  rw [← hM.closure_range_A1Q]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨t, rfl⟩
  fin_cases t
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · have h2 : A1Q 2 = (alphaQ 2)⁻¹ := by
      apply Subtype.ext
      simp [alphaQ, alphaY, e1A, signedProd, A1Q, A1gen]
    simp only [Fin.reduceFinMk] at h2 ⊢
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨2, rfl⟩)

private noncomputable def beta (hM : Facts) : MulAut ↥Q1 :=
  (pcIso CFSG.Quasithin.St84.pc_checkQ1 pc1Q hM.rels_pc1Q hM.closure_range_pc1Q
    hM.card_Q1).symm.trans
  (pcIso CFSG.Quasithin.St84.pc_checkQ1 betaQ (betaQ_rels hM) (betaQ_gen hM)
    hM.card_Q1)

private noncomputable def alpha (hM : Facts) : MulAut ↥A1 :=
  (pcIso CFSG.Quasithin.St84.pc_checkA A1Q hM.rels_A1Q hM.closure_range_A1Q
    hM.card_A1).symm.trans
  (pcIso CFSG.Quasithin.St84.pc_checkA alphaQ (alphaQ_rels hM) (alphaQ_gen hM)
    hM.card_A1)

private theorem beta_of (hM : Facts) (j : Fin 10) : beta hM (pc1Q j) = betaQ j := by
  rw [beta, MulEquiv.trans_apply]
  have h1 : (pcIso CFSG.Quasithin.St84.pc_checkQ1 pc1Q hM.rels_pc1Q
      hM.closure_range_pc1Q hM.card_Q1).symm (pc1Q j) = PresentedGroup.of j := by
    rw [← pcIso_of CFSG.Quasithin.St84.pc_checkQ1 pc1Q hM.rels_pc1Q
      hM.closure_range_pc1Q hM.card_Q1 j, MulEquiv.symm_apply_apply]
  rw [h1]
  exact pcIso_of CFSG.Quasithin.St84.pc_checkQ1 betaQ (betaQ_rels hM) (betaQ_gen hM)
    hM.card_Q1 j

private theorem alpha_of (hM : Facts) (t : Fin 3) : alpha hM (A1Q t) = alphaQ t := by
  rw [alpha, MulEquiv.trans_apply]
  have h1 : (pcIso CFSG.Quasithin.St84.pc_checkA A1Q hM.rels_A1Q
      hM.closure_range_A1Q hM.card_A1).symm (A1Q t) = PresentedGroup.of t := by
    rw [← pcIso_of CFSG.Quasithin.St84.pc_checkA A1Q hM.rels_A1Q
      hM.closure_range_A1Q hM.card_A1 t, MulEquiv.symm_apply_apply]
  rw [h1]
  exact pcIso_of CFSG.Quasithin.St84.pc_checkA alphaQ (alphaQ_rels hM) (alphaQ_gen hM)
    hM.card_A1 t

private theorem beta_prod (hM : Facts) (w : List (Fin 10)) :
    beta hM ((w.map pc1Q).prod) = (w.map betaQ).prod := by
  change (beta hM).toMonoidHom ((w.map pc1Q).prod) = (w.map betaQ).prod
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact beta_of hM i

private theorem alpha_prod (hM : Facts) (w : List (Fin 3)) :
    alpha hM ((w.map A1Q).prod) = (w.map alphaQ).prod := by
  change (alpha hM).toMonoidHom ((w.map A1Q).prod) = (w.map alphaQ).prod
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact alpha_of hM i

private theorem beta_conj_coe (hM : Facts) (t : Fin 3) (j : Fin 10) :
    (((beta hM (conjHom Q1 A1 (normQ1A1 hM) (A1Q t) (pc1Q j)) : ↥Q1) : Y)) =
      (((conjHom Q1 A1 (normQ1A1 hM) (alpha hM (A1Q t)) (beta hM (pc1Q j)) : ↥Q1) : Y)) := by
  obtain ⟨hD1, hD2⟩ := witFacts.conjData t.val (List.mem_range.mpr t.isLt)
    j.val (List.mem_range.mpr j.isLt)
  have hY1 : conjHom Q1 A1 (normQ1A1 hM) (A1Q t) (pc1Q j) =
      ((((conjQ1.getD t.val []).getD j.val []).map pc1Q).prod : ↥Q1) := by
    apply Subtype.ext
    rw [conjHom_apply]
    rw [A1Q_coe, pc1Q_coe, pc1Q_prod_coe]
    have hmat : (toGL ((A1gen t * pc1Y j * (A1gen t)⁻¹) : Y) :
        Matrix (Fin 14) (Fin 14) F4) =
        (toGL ((((conjQ1.getD t.val []).getD j.val []).map pc1Y).prod : Y) :
          Matrix (Fin 14) (Fin 14) F4) := by
      have h1 := congrArg (toMat 14) hD1
      rw [toMat_conjArr, toMat_eA1 hM t, toMat_e1P hM j, toMat_eA1i hM t] at h1
      rw [toMat_evalP (φ := toGL) (y := pc1Y) (G := e1P) (hG := toMat_e1P hM)] at h1
      rw [← map_inv, ← Units.val_mul, ← map_mul, ← Units.val_mul, ← map_mul] at h1
      exact h1
    exact hM.toGL_injective (Units.ext hmat)
  have hY2 : (((((conjQ1.getD t.val []).getD j.val []).map betaQ).prod : ↥Q1) : Y) =
      (alphaQ t : Y) * (betaQ j : Y) * ((alphaQ t : Y))⁻¹ := by
    have hmat : (toGL ((((conjQ1.getD t.val []).getD j.val []).map betaQ).prod : ↥Q1) :
        Matrix (Fin 14) (Fin 14) F4) =
        (toGL ((alphaQ t : Y) * (betaQ j : Y) * ((alphaQ t : Y))⁻¹) :
          Matrix (Fin 14) (Fin 14) F4) := by
      have h1 := congrArg (toMat 14) hD2
      rw [toMat_evalP (φ := toGL.comp Q1.subtype) (y := betaQ) (G := beP)
        (hG := toMat_beP hM)] at h1
      rw [toMat_conjArr, toMat_alP hM t, toMat_beP hM j, toMat_alPi hM t] at h1
      rw [← map_inv, ← Units.val_mul, ← map_mul, ← Units.val_mul, ← map_mul] at h1
      exact h1
    exact hM.toGL_injective (Units.ext (by simpa [alphaQ, betaQ] using hmat))
  calc
    (beta hM (conjHom Q1 A1 (normQ1A1 hM) (A1Q t) (pc1Q j)) : Y)
        = (beta hM ((((conjQ1.getD t.val []).getD j.val []).map pc1Q).prod) : Y) := by
          rw [hY1]
    _ = (((((conjQ1.getD t.val []).getD j.val []).map betaQ).prod : ↥Q1) : Y) := by
          rw [beta_prod]
    _ = (alphaQ t : Y) * (betaQ j : Y) * ((alphaQ t : Y))⁻¹ := hY2
    _ = (conjHom Q1 A1 (normQ1A1 hM) (alpha hM (A1Q t)) (beta hM (pc1Q j)) : Y) := by
          rw [conjHom_apply, alpha_of, beta_of]

private theorem beta_equivariant (hM : Facts) :
    ∀ (a : ↥A1) (q : ↥Q1),
      beta hM (conjHom Q1 A1 (normQ1A1 hM) a q) =
        conjHom Q1 A1 (normQ1A1 hM) (alpha hM a) (beta hM q) := by
  intro a q
  exact equivariant_of_gens (φ := conjHom Q1 A1 (normQ1A1 hM))
    (φ' := conjHom Q1 A1 (normQ1A1 hM)) (β := (beta hM).toMonoidHom)
    (α := (alpha hM).toMonoidHom) (sA := Set.range A1Q) hM.closure_range_A1Q
    (sV := Set.range pc1Q) hM.closure_range_pc1Q (by
      rintro _ ⟨t, rfl⟩ _ ⟨j, rfl⟩
      exact Subtype.ext (beta_conj_coe hM t j)) a q

private theorem exists_e1Sup (hM : Facts) :
    ∃ α₀ : ↥(Q1 ⊔ A1) ≃* ↥(Q1 ⊔ A1),
      (∀ q : ↥Q1, (α₀ ⟨q, Subgroup.mem_sup_left q.2⟩ : Y) = (beta hM q : Y)) ∧
      (∀ a : ↥A1, (α₀ ⟨a, Subgroup.mem_sup_right a.2⟩ : Y) = (alpha hM a : Y)) :=
  CFSG.GroupTheory.exists_mulEquiv_sup_extend (Q := Q1) (K := A1) (Q' := Q1) (K' := A1)
    (normQ1A1 hM) (disjoint_Q1_A1 hM) (normQ1A1 hM) (disjoint_Q1_A1 hM)
    (beta hM) (alpha hM) (fun k q hq => by
      have h := congrArg (fun x : ↥Q1 => (x : Y)) (beta_equivariant hM k q)
      rw [conjHom_val] at h
      simpa using h)

private noncomputable def e1Sup (hM : Facts) : ↥(Q1 ⊔ A1) ≃* ↥(Q1 ⊔ A1) :=
  Classical.choose (exists_e1Sup hM)

private theorem e1Sup_inl (hM : Facts) (q : ↥Q1) :
    (e1Sup hM ⟨q, Subgroup.mem_sup_left q.2⟩ : Y) = (beta hM q : Y) :=
  (Classical.choose_spec (exists_e1Sup hM)).1 q

private theorem e1Sup_inr (hM : Facts) (a : ↥A1) :
    (e1Sup hM ⟨a, Subgroup.mem_sup_right a.2⟩ : Y) = (alpha hM a : Y) :=
  (Classical.choose_spec (exists_e1Sup hM)).2 a

private noncomputable def e1 (hM : Facts) : MulAut ↥M1 :=
  (MulEquiv.subgroupCongr hM.sup_Q1_A1).symm.trans
    ((e1Sup hM).trans (MulEquiv.subgroupCongr hM.sup_Q1_A1))

private theorem e1_of_mem_Q1 (hM : Facts) (q : ↥Q1) (hq : (q : Y) ∈ M1) :
    ((e1 hM ⟨(q : Y), hq⟩ : ↥M1) : Y) = (beta hM q : Y) := by
  rw [e1, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hs : (MulEquiv.subgroupCongr hM.sup_Q1_A1).symm (⟨(q : Y), hq⟩ : ↥M1) =
      (⟨(q : Y), Subgroup.mem_sup_left q.2⟩ : ↥(Q1 ⊔ A1)) := Subtype.ext rfl
  rw [hs]
  simpa using e1Sup_inl hM q

private theorem e1_of_mem_A1 (hM : Facts) (a : ↥A1) (ha : (a : Y) ∈ M1) :
    ((e1 hM ⟨(a : Y), ha⟩ : ↥M1) : Y) = (alpha hM a : Y) := by
  rw [e1, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hs : (MulEquiv.subgroupCongr hM.sup_Q1_A1).symm (⟨(a : Y), ha⟩ : ↥M1) =
      (⟨(a : Y), Subgroup.mem_sup_right a.2⟩ : ↥(Q1 ⊔ A1)) := Subtype.ext rfl
  rw [hs]
  simpa using e1Sup_inr hM a

private def q1w (k : Fin 4) : List (Fin 10) := (dec1.getD k.val ([], [])).1
private def a1w (k : Fin 4) : List (Fin 3) := (dec1.getD k.val ([], [])).2

private theorem gB0_dec1 (hM : Facts) (k : Fin 4) :
    gB0 k = ((q1w k).map pc1Y).prod * ((a1w k).map A1gen).prod := by
  have hE := witFacts.dec1f k.val (List.mem_range.mpr k.isLt)
  have hmat := congrArg (toMat 14) hE.1
  rw [toMat_mulArr, toMat_evalP (φ := toGL) (y := pc1Y) (G := e1P)
      (hG := toMat_e1P hM), toMat_evalP (φ := toGL) (y := A1gen) (G := eA1)
      (hG := toMat_eA1 hM), gB_getD k.val k.isLt, ← Code.decode_eq_toMat,
      ← hM.toGL_gB0, ← Units.val_mul, ← map_mul] at hmat
  exact hM.toGL_injective (Units.ext hmat)

private theorem e1_gB0 (hM : Facts) (k : Fin 4) :
    ((e1 hM ⟨gB0 k, hM.B0_le_M1 (hM.gB0_mem_B0 k)⟩ : ↥M1) : Y) =
      (((wWords.getD 2 []).getD k.val []).map gB0).prod := by
  have hE := witFacts.dec1f k.val (List.mem_range.mpr k.isLt)
  have hQmem : ((q1w k).map pc1Y).prod ∈ Q1 :=
    Subgroup.list_prod_mem Q1 (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact pc1Y_mem_Q1 i)
  have hAmem : ((a1w k).map A1gen).prod ∈ A1 :=
    Subgroup.list_prod_mem A1 (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact A1gen_mem_A1 i)
  have hx : (⟨gB0 k, hM.B0_le_M1 (hM.gB0_mem_B0 k)⟩ : ↥M1) =
      (⟨((q1w k).map pc1Y).prod, by
          rw [← hM.sup_Q1_A1]
          exact Subgroup.mem_sup_left hQmem⟩ : ↥M1) *
      (⟨((a1w k).map A1gen).prod, by
          rw [← hM.sup_Q1_A1]
          exact Subgroup.mem_sup_right hAmem⟩ : ↥M1) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change gB0 k =
      ((q1w k).map pc1Y).prod * ((a1w k).map A1gen).prod
    exact gB0_dec1 hM k
  rw [hx, map_mul, Subgroup.coe_mul]
  rw [e1_of_mem_Q1 hM ⟨((q1w k).map pc1Y).prod, hQmem⟩ (by
        rw [← hM.sup_Q1_A1]; exact Subgroup.mem_sup_left hQmem),
      e1_of_mem_A1 hM ⟨((a1w k).map A1gen).prod, hAmem⟩ (by
        rw [← hM.sup_Q1_A1]; exact Subgroup.mem_sup_right hAmem)]
  have hb : beta hM ⟨((q1w k).map pc1Y).prod, hQmem⟩ = ((q1w k).map betaQ).prod := by
    rw [show (⟨((q1w k).map pc1Y).prod, hQmem⟩ : ↥Q1) = ((q1w k).map pc1Q).prod from
      Subtype.ext (pc1Q_prod_coe (q1w k)).symm]
    rw [beta_prod]
  have ha : alpha hM ⟨((a1w k).map A1gen).prod, hAmem⟩ = ((a1w k).map alphaQ).prod := by
    rw [show (⟨((a1w k).map A1gen).prod, hAmem⟩ : ↥A1) = ((a1w k).map A1Q).prod from
      Subtype.ext (by
        change (List.map A1gen (a1w k)).prod = (((a1w k).map A1Q).prod : Y)
        rw [Subgroup.val_list_prod, List.map_map]
        rfl)]
    rw [alpha_prod]
  rw [hb, ha]
  apply hM.toGL_injective
  apply Units.ext
  have hmat : (toGL (((((q1w k).map betaQ).prod : ↥Q1) : Y) *
      ((((a1w k).map alphaQ).prod : ↥A1) : Y)) : Matrix (Fin 14) (Fin 14) F4) =
      toMat 14 (mulArr 14 (evalP beP (q1w k)) (evalP alP (a1w k))) := by
    rw [toMat_mulArr, toMat_evalP (φ := toGL.comp Q1.subtype) (y := betaQ) (G := beP)
        (hG := toMat_beP hM), toMat_evalP (φ := toGL.comp A1.subtype) (y := alphaQ)
        (G := alP) (hG := toMat_alP hM), MonoidHom.comp_apply, MonoidHom.comp_apply,
        ← Units.val_mul, ← map_mul]
    rfl
  have hE2 : toMat 14 (((wImg ()).getD 2 #[]).getD k.val one14) =
      toMat 14 (mulArr 14 (evalP beP (q1w k)) (evalP alP (a1w k))) := by
    simpa [q1w, a1w] using congrArg (toMat 14) hE.2
  rw [hmat, ← hE2, toMat_wImg_eq hM 2 k.val (by norm_num) k.isLt]

private theorem mem_B0_iff_map_of_gB0 (hM : Facts) {H : Subgroup Y} (hBH : B0 ≤ H)
    (e : MulAut ↥H)
    (he : ∀ (k : Fin 4) (x : ↥H), (x : Y) = gB0 k → ((e x : ↥H) : Y) ∈ B0) (x : ↥H) :
    (x : Y) ∈ B0 ↔ ((e x : ↥H) : Y) ∈ B0 := by
  let B : Subgroup ↥H := B0.subgroupOf H
  have hgen : B = Subgroup.closure (Set.range fun k : Fin 4 =>
      (⟨gB0 k, hBH (hM.gB0_mem_B0 k)⟩ : ↥H)) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hBH, MonoidHom.map_closure]
    have hrange : H.subtype '' Set.range (fun k : Fin 4 =>
        (⟨gB0 k, hBH (hM.gB0_mem_B0 k)⟩ : ↥H)) = Set.range gB0 := by
      ext z
      constructor
      · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨⟨gB0 k, hBH (hM.gB0_mem_B0 k)⟩, ⟨k, rfl⟩, rfl⟩
    rw [hrange, hM.closure_gB0]
  have hle : B.map e.toMonoidHom ≤ B := by
    rw [hgen, MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨y, ⟨k, rfl⟩, rfl⟩
    exact hgen ▸ Subgroup.mem_subgroupOf.mpr (he k _ rfl)
  have hle' : ∀ y ∈ B, e y ∈ B := fun y hy => hle (Subgroup.mem_map_of_mem e.toMonoidHom hy)
  have hEq : B.map e.toMonoidHom = B := map_eq_of_mapsTo e hle'
  have hiff : x ∈ B ↔ e x ∈ B := (apply_mem_iff_of_mapsTo e hle' x).symm
  rwa [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hiff

theorem mem_M2_iff_of_gB0 (hM : Facts) (e : MulAut ↥M1)
    (he : ∀ (k : Fin 4) (x : ↥M1), (x : Y) = gB0 k → ((e x : ↥M1) : Y) ∈ B0) (x : ↥M1) :
    (x : Y) ∈ M2 ↔ ((e x : ↥M1) : Y) ∈ M2 := by
  have hB := mem_B0_iff_map_of_gB0 hM hM.B0_le_M1 e he x
  have h1 : (x : Y) ∈ M2 ↔ (x : Y) ∈ B0 := by
    rw [← hM.inf_M1_M2, Subgroup.mem_inf]
    exact (and_iff_right x.2).symm
  have h2 : ((e x : ↥M1) : Y) ∈ M2 ↔ ((e x : ↥M1) : Y) ∈ B0 := by
    rw [← hM.inf_M1_M2, Subgroup.mem_inf]
    exact (and_iff_right (e x).2).symm
  rw [h1, h2, hB]

theorem mem_M1_iff_of_gB0 (hM : Facts) (e : MulAut ↥M2)
    (he : ∀ (k : Fin 4) (x : ↥M2), (x : Y) = gB0 k → ((e x : ↥M2) : Y) ∈ B0) (x : ↥M2) :
    (x : Y) ∈ M1 ↔ ((e x : ↥M2) : Y) ∈ M1 := by
  have hB := mem_B0_iff_map_of_gB0 hM hM.B0_le_M2 e he x
  have h1 : (x : Y) ∈ M1 ↔ (x : Y) ∈ B0 := by
    rw [← hM.inf_M1_M2, Subgroup.mem_inf]
    exact (and_iff_left x.2).symm
  have h2 : ((e x : ↥M2) : Y) ∈ M1 ↔ ((e x : ↥M2) : Y) ∈ B0 := by
    rw [← hM.inf_M1_M2, Subgroup.mem_inf]
    exact (and_iff_left (e x).2).symm
  rw [h1, h2, hB]

private theorem phiM1_gB0 (hM : Facts) (k : Fin 4) :
    ((phiM1 hM ⟨gB0 k, hM.B0_le_M1 (hM.gB0_mem_B0 k)⟩ : ↥M1) : Y) =
      (((wWords.getD 1 []).getD k.val []).map gB0).prod := by
  apply hM.toGL_injective
  apply Units.ext
  rw [coe_phiM1, toGL_phiY]
  rw [← toMat_wImg_eq hM 1 k.val (by norm_num) k.isLt, witFacts.w1,
    getD_map_of_lt frobArr gB k.val one14 one14 (by rw [gB_size]; exact k.isLt),
    toMat_frobArr, gB_getD k.val k.isLt, ← Code.decode_eq_toMat, ← hM.toGL_gB0]

private noncomputable def phiE1 (hM : Facts) : MulAut ↥M1 :=
  (e1 hM).trans (phiM1 hM)

private theorem phiE1_coe (hM : Facts) (x : ↥M1) :
    ((phiE1 hM x : ↥M1) : Y) = phiY ((e1 hM x : ↥M1) : Y) := by
  simp [phiE1, coe_phiM1]

private theorem phiE1_gB0 (hM : Facts) (k : Fin 4) :
    ((phiE1 hM ⟨gB0 k, hM.B0_le_M1 (hM.gB0_mem_B0 k)⟩ : ↥M1) : Y) =
      (((wWords.getD 3 []).getD k.val []).map gB0).prod := by
  apply hM.toGL_injective
  apply Units.ext
  rw [phiE1_coe, toGL_phiY]
  rw [← toMat_wImg_eq hM 3 k.val (by norm_num) k.isLt, witFacts.w3,
    getD_map_of_lt frobArr ((wImg ()).getD 2 #[]) k.val one14 one14
      (by rw [wImg_row_size 2 (by norm_num)]; exact k.isLt), toMat_frobArr]
  congr 1
  rw [toMat_wImg_eq hM 2 k.val (by norm_num) k.isLt]
  exact congrArg (fun z => (toGL z : Matrix (Fin 14) (Fin 14) F4)) (e1_gB0 hM k)

private theorem aut_spec_of_gB0 (hM : Facts) {H : Subgroup Y} (hBH : B0 ≤ H)
    (e : MulAut ↥H) (w : Fin 4 → Y)
    (he : ∀ k : Fin 4, ((e ⟨gB0 k, hBH (hM.gB0_mem_B0 k)⟩ : ↥H) : Y) = w k) :
    ∀ (k : Fin 4) (x : ↥H), (x : Y) = gB0 k → ((e x : ↥H) : Y) = w k := by
  intro k x hx
  rw [show x = ⟨gB0 k, hBH (hM.gB0_mem_B0 k)⟩ from Subtype.ext hx]
  exact he k

theorem exists_aut_M1 (hM : Facts) (i : Fin 4) :
    ∃ e : MulAut ↥M1, ∀ (k : Fin 4) (x : ↥M1), (x : Y) = gB0 k →
      ((e x : ↥M1) : Y) =
        (((wWords.getD i.val []).getD k.val []).map gB0).prod := by
  fin_cases i
  · refine ⟨1, aut_spec_of_gB0 hM hM.B0_le_M1 1
      (fun k => (((wWords.getD 0 []).getD k.val []).map gB0).prod) ?_⟩
    intro k
    fin_cases k <;> rfl
  · exact ⟨phiM1 hM, aut_spec_of_gB0 hM hM.B0_le_M1 (phiM1 hM)
      (fun k => (((wWords.getD 1 []).getD k.val []).map gB0).prod) (phiM1_gB0 hM)⟩
  · exact ⟨e1 hM, aut_spec_of_gB0 hM hM.B0_le_M1 (e1 hM)
      (fun k => (((wWords.getD 2 []).getD k.val []).map gB0).prod) (e1_gB0 hM)⟩
  · exact ⟨phiE1 hM, aut_spec_of_gB0 hM hM.B0_le_M1 (phiE1 hM)
      (fun k => (((wWords.getD 3 []).getD k.val []).map gB0).prod) (phiE1_gB0 hM)⟩

private def cocWord (s : Fin 4) (t : Fin 3) : List (Fin 10) :=
  (e2Coc.getD s.val []).getD t.val []

private def cY (s : Fin 4) (t : Fin 3) : Y :=
  ((cocWord s t).map pc2Y).prod * A2gen t

private theorem pc2Y_mem_Q2 (i : Fin 10) : pc2Y i ∈ Q2 :=
  Subgroup.subset_closure ⟨i, rfl⟩

private theorem cY_mem_M2 (hM : Facts) (s : Fin 4) (t : Fin 3) : cY s t ∈ M2 := by
  refine Subgroup.mul_mem M2 ?_ (hM.A2_le_M2 (A2gen_mem_A2 t))
  exact hM.B0_le_M2 (hM.T0_le_B0 (hM.Q2_le_T0
    (Subgroup.list_prod_mem Q2 (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact pc2Y_mem_Q2 i))))

private def cQ (hM : Facts) (s : Fin 4) (t : Fin 3) : ↥M2 :=
  ⟨cY s t, cY_mem_M2 hM s t⟩

private theorem e2Coc_length : e2Coc.length = 4 := rfl

private theorem cs_length : cs.length = 4 := by
  simp [cs, e2Coc_length]

private theorem cs_getD (s : Fin 4) :
    cs.getD s.val (#[], #[]) =
      cocImgs (e2P, e2Pi) (eA2, eA2i) (e2Coc.getD s.val []) := by
  rw [cs, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [e2Coc_length]; exact s.isLt),
    List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [e2Coc_length]; exact s.isLt)]
  rfl

private theorem toMat_csP (hM : Facts) (s : Fin 4) (t : Fin 3) :
    toMat 14 (((cs.getD s.val (#[], #[])).1).getD t.val one14) =
      (toGL (cY s t) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [cs_getD s, cocImgs,
    getD_toArray_map (f := fun u : ℕ => mulArr 14 (evalP e2P ((e2Coc.getD s.val []).getD u []))
      (eA2.getD u one14)) (l := List.range 3) (i := t.val) (d := one14) (e := 0) t.isLt]
  have ht : (List.range 3).getD t.val 0 = t.val := by fin_cases t <;> rfl
  rw [ht, toMat_mulArr, toMat_evalP (φ := toGL) (y := pc2Y) (G := e2P)
      (hG := toMat_e2P hM), toMat_eA2 hM t, ← Units.val_mul, ← map_mul, cY, cocWord]

private theorem toMat_csPi (hM : Facts) (s : Fin 4) (t : Fin 3) :
    toMat 14 (((cs.getD s.val (#[], #[])).2).getD t.val one14) =
      (((toGL (cY s t))⁻¹ : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [cs_getD s, cocImgs]
  simp only [cocImgs]
  rw [getD_toArray_map (f := fun u : ℕ => mulArr 14 (eA2i.getD u one14)
      (evalPInv e2Pi ((e2Coc.getD s.val []).getD u [])))
      (l := List.range 3) (i := t.val) (d := one14) (e := 0) t.isLt]
  have ht : (List.range 3).getD t.val 0 = t.val := by fin_cases t <;> rfl
  rw [ht, toMat_mulArr, toMat_evalPInv (φ := toGL) (y := pc2Y) (Gi := e2Pi)
      (hGi := toMat_e2Pi hM), toMat_eA2i hM t, ← Units.val_mul, ← mul_inv_rev,
    ← map_mul, cY, cocWord]

private theorem cocWord_mem (s : Fin 4) (t : Fin 3) :
    cocWord s t ∈ e2Coc.getD s.val [] := by
  fin_cases s <;> fin_cases t <;> simp [cocWord, e2Coc]

private theorem e2Coc_getD_mem (s : Fin 4) : e2Coc.getD s.val [] ∈ e2Coc := by
  fin_cases s <;> simp [e2Coc]

private theorem pc2Y_mem_Z2_of_six (hM : Facts) (l : Fin 10) (hl : 6 ≤ l.val) :
    pc2Y l ∈ Z2 := by
  rw [hM.Z2_eq]
  fin_cases l
  · exfalso; norm_num at hl
  · exfalso; norm_num at hl
  · exfalso; norm_num at hl
  · exfalso; norm_num at hl
  · exfalso; norm_num at hl
  · exfalso; norm_num at hl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

private def pc2P (s : Fin 4) (t : Fin 3) : Y := ((cocWord s t).map pc2Y).prod

private theorem pc2P_mem_Z2 (hM : Facts) (s : Fin 4) (t : Fin 3) : pc2P s t ∈ Z2 := by
  apply Subgroup.list_prod_mem Z2
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact pc2Y_mem_Z2_of_six hM i (witFacts.cocZ _ (e2Coc_getD_mem s) _ (cocWord_mem s t) i hi)

private theorem cY_eq (s : Fin 4) (t : Fin 3) : cY s t = pc2P s t * A2gen t := rfl

private theorem cY_mul_inv (s : Fin 4) (t : Fin 3) :
    cY s t * ((A2Q t : ↥A2) : Y)⁻¹ = pc2P s t := by
  rw [cY_eq]
  change pc2P s t * A2gen t * (A2gen t)⁻¹ = pc2P s t
  group

private theorem lam_rels (hM : Facts) (s : Fin 4) :
    ∀ r ∈ relsA, signedProd (cQ hM s) r = 1 := by
  intro r hr
  have hmem : cs.getD s.val (#[], #[]) ∈ cs := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [cs_length]; exact s.isLt)]
    exact List.getElem_mem ..
  have h := witFacts.relsAc (cs.getD s.val (#[], #[])) hmem r hr
  have hmat : toMat 14 (evalL (cs.getD s.val (#[], #[])) r) = 1 := by
    rw [h, toMat_one14]
  rw [toMat_evalL (φ := toGL.comp M2.subtype) (y := cQ hM s)
    (G := cs.getD s.val (#[], #[])) (hG1 := toMat_csP hM s)
    (hG2 := toMat_csPi hM s)] at hmat
  exact Subtype.ext (hM.toGL_injective (Units.ext (by
    simpa [MonoidHom.comp_apply] using hmat)))

private noncomputable def lam (hM : Facts) (s : Fin 4) : ↥A2 →* Y :=
  (PresentedGroup.toGroup (rels := {r : FreeGroup (Fin 3) | r ∈ relsA.map FreeGroup.mk})
    (f := cY s) (by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      rw [lift_mk_eq_signedProd]
      change signedProd (fun t => M2.subtype (cQ hM s t)) w = 1
      rw [← map_signedProd M2.subtype (cQ hM s) w, lam_rels hM s w hw]
      rfl)).comp
  (pcIso CFSG.Quasithin.St84.pc_checkA A2Q hM.rels_A2Q hM.closure_range_A2Q
    hM.card_A2).symm.toMonoidHom

private theorem lam_of (hM : Facts) (s : Fin 4) (t : Fin 3) :
    lam hM s (A2Q t) = cY s t := by
  rw [lam, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have h1 : (pcIso CFSG.Quasithin.St84.pc_checkA A2Q hM.rels_A2Q
      hM.closure_range_A2Q hM.card_A2).symm (A2Q t) = PresentedGroup.of t := by
    rw [← pcIso_of CFSG.Quasithin.St84.pc_checkA A2Q hM.rels_A2Q
      hM.closure_range_A2Q hM.card_A2 t, MulEquiv.symm_apply_apply]
  rw [h1, PresentedGroup.toGroup.of]

private theorem conj_mem_Z2 (hM : Facts) {a : ↥A2} {z : Y} (hz : z ∈ Z2) :
    (a : Y) * z * ((a : Y))⁻¹ ∈ Z2 := by
  have hnorm := hM.M2_le_normalizer_Z2 (hM.A2_le_M2 a.2)
  exact (Subgroup.mem_normalizer_iff.mp hnorm z).mp hz

private def lamAgreeModZ2 (hM : Facts) (s : Fin 4) : Subgroup ↥A2 where
  carrier := {a | (lam hM s a : Y) * ((a : Y))⁻¹ ∈ Z2}
  one_mem' := by
    change ((lam hM s 1 : Y) * ((1 : ↥A2) : Y)⁻¹) ∈ Z2
    simp
  mul_mem' := by
    intro a b ha hb
    change ((lam hM s (a * b) : Y) * (((a * b : ↥A2) : Y))⁻¹) ∈ Z2
    have hEq : (lam hM s (a * b) : Y) * (((a * b : ↥A2) : Y))⁻¹ =
        ((lam hM s a : Y) * ((a : Y))⁻¹) *
          ((a : Y) * ((lam hM s b : Y) * ((b : Y))⁻¹) * ((a : Y))⁻¹) := by
      rw [map_mul]
      simp only [Subgroup.coe_mul]
      group
    rw [hEq]
    exact Z2.mul_mem ha (conj_mem_Z2 hM hb)
  inv_mem' := by
    intro a ha
    change ((lam hM s a⁻¹ : Y) * (((a⁻¹ : ↥A2) : Y))⁻¹) ∈ Z2
    have hEq : (lam hM s a⁻¹ : Y) * (((a⁻¹ : ↥A2) : Y))⁻¹ =
        ((a : Y))⁻¹ * ((lam hM s a : Y) * ((a : Y))⁻¹)⁻¹ * (((a : Y))⁻¹)⁻¹ := by
      rw [map_inv]
      simp only [Subgroup.coe_inv]
      group
    rw [hEq]
    exact conj_mem_Z2 (a := a⁻¹) hM (Z2.inv_mem ha)

private theorem lam_mul_inv_mem_Z2 (hM : Facts) (s : Fin 4) (a : ↥A2) :
    (lam hM s a : Y) * ((a : Y))⁻¹ ∈ Z2 := by
  have htop : lamAgreeModZ2 hM s = ⊤ := by
    apply top_unique
    rw [← hM.closure_range_A2Q]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t, rfl⟩
    change ((lam hM s (A2Q t) : Y) * (((A2Q t : ↥A2) : Y))⁻¹) ∈ Z2
    rw [lam_of, cY_mul_inv]
    exact pc2P_mem_Z2 hM s t
  have : a ∈ lamAgreeModZ2 hM s := by rw [htop]; exact Subgroup.mem_top a
  exact this

private theorem lam_injective (hM : Facts) (s : Fin 4) : Function.Injective (lam hM s) := by
  intro a b hab
  have h := lam_mul_inv_mem_Z2 hM s (a⁻¹ * b)
  rw [map_mul, map_inv, hab, inv_mul_cancel, one_mul] at h
  have hQ : (((a⁻¹ * b : ↥A2) : Y)) ∈ Q2 :=
    Subgroup.inv_mem Q2 (Subgroup.mem_inf.mp h).1
  have hmemY : (((a⁻¹ * b : ↥A2) : Y)) ∈ (⊥ : Subgroup Y) := by
    rw [← hM.inf_A2_Q2]
    exact Subgroup.mem_inf.mpr ⟨(a⁻¹ * b).2, hQ⟩
  have h1 : a⁻¹ * b = 1 := Subtype.ext (Subgroup.mem_bot.mp hmemY)
  have h2 : a * (a⁻¹ * b) = a * 1 := by rw [h1]
  have h3 : b = a := by simpa [mul_assoc] using h2
  exact h3.symm

private theorem lam_range_le_M2 (hM : Facts) (s : Fin 4) : (lam hM s).range ≤ M2 := by
  rw [MonoidHom.range_eq_map, Subgroup.map_le_iff_le_comap, ← hM.closure_range_A2Q]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨t, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, lam_of]
  exact cY_mem_M2 hM s t

private theorem lam_conj (hM : Facts) (s : Fin 4) (a : ↥A2) (q : ↥Q2) :
    (lam hM s a : Y) * (q : Y) * ((lam hM s a : Y))⁻¹ =
      (a : Y) * (q : Y) * ((a : Y))⁻¹ := by
  have hz := lam_mul_inv_mem_Z2 hM s a
  have hza : (lam hM s a : Y) = ((lam hM s a : Y) * (a : Y)⁻¹) * (a : Y) := by group
  rw [hza]
  have hq : (a : Y) * (q : Y) * ((a : Y))⁻¹ ∈ Q2 := by
    have hnorm := hM.M2_le_normalizer_Q2 (hM.A2_le_M2 a.2)
    exact (Subgroup.mem_normalizer_iff.mp hnorm q).mp q.2
  have hcomm := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2)
    ((a : Y) * (q : Y) * ((a : Y))⁻¹) hq
  calc
    ((lam hM s a : Y) * (a : Y)⁻¹) * (a : Y) * (q : Y) *
        ((((lam hM s a : Y) * (a : Y)⁻¹) * (a : Y)))⁻¹
        = ((lam hM s a : Y) * (a : Y)⁻¹) * ((a : Y) * (q : Y) * ((a : Y))⁻¹) *
            (((lam hM s a : Y) * (a : Y)⁻¹))⁻¹ := by group
    _ = (a : Y) * (q : Y) * ((a : Y))⁻¹ := by
      rw [← hcomm]
      group

private theorem disjoint_Q2_lam (hM : Facts) (s : Fin 4) : Disjoint Q2 (lam hM s).range := by
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxQ, ⟨a, rfl⟩⟩
  rw [Subgroup.mem_bot]
  have hz := lam_mul_inv_mem_Z2 hM s a
  have hzQ : ((lam hM s a : Y) * (a : Y)⁻¹)⁻¹ ∈ Q2 :=
    (Subgroup.mem_inf.mp (Subgroup.inv_mem Z2 hz)).1
  have haQ : (a : Y) ∈ Q2 := by
    have hEq : (a : Y) = ((lam hM s a : Y) * (a : Y)⁻¹)⁻¹ * (lam hM s a : Y) := by group
    rw [hEq]
    exact Q2.mul_mem hzQ hxQ
  have hmemY : (a : Y) ∈ (⊥ : Subgroup Y) := by
    rw [← hM.inf_A2_Q2]
    exact Subgroup.mem_inf.mpr ⟨a.2, haQ⟩
  have ha1 : a = 1 := Subtype.ext (Subgroup.mem_bot.mp hmemY)
  rw [ha1, map_one]

private theorem exists_eδSup (hM : Facts) (s : Fin 4) :
    ∃ α₀ : ↥(Q2 ⊔ A2) ≃* ↥(Q2 ⊔ (lam hM s).range),
      (∀ q : ↥Q2, (α₀ ⟨q, Subgroup.mem_sup_left q.2⟩ : Y) = (q : Y)) ∧
      (∀ a : ↥A2, (α₀ ⟨a, Subgroup.mem_sup_right a.2⟩ : Y) = (lam hM s a : Y)) := by
  have hQ2A2 : A2 ≤ Subgroup.normalizer (Q2 : Set Y) :=
    hM.A2_le_M2.trans hM.M2_le_normalizer_Q2
  have hQ2R : (lam hM s).range ≤ Subgroup.normalizer (Q2 : Set Y) :=
    (lam_range_le_M2 hM s).trans hM.M2_le_normalizer_Q2
  have hdQ2A2 : Disjoint Q2 A2 := by
    rw [disjoint_iff, inf_comm, hM.inf_A2_Q2]
  have hdQ2R : Disjoint Q2 (lam hM s).range := disjoint_Q2_lam hM s
  refine CFSG.GroupTheory.exists_mulEquiv_sup_extend (Q := Q2) (K := A2) (Q' := Q2)
    (K' := (lam hM s).range) hQ2A2 hdQ2A2 hQ2R hdQ2R (MulEquiv.refl ↥Q2)
    (MonoidHom.ofInjective (lam_injective hM s)) ?_
  intro k q hq
  have h := lam_conj hM s k q
  simpa [MonoidHom.ofInjective_apply] using h.symm

private noncomputable def eδSup (hM : Facts) (s : Fin 4) :
    ↥(Q2 ⊔ A2) ≃* ↥(Q2 ⊔ (lam hM s).range) :=
  Classical.choose (exists_eδSup hM s)

private theorem eδSup_inl (hM : Facts) (s : Fin 4) (q : ↥Q2) :
    (eδSup hM s ⟨q, Subgroup.mem_sup_left q.2⟩ : Y) = (q : Y) :=
  (Classical.choose_spec (exists_eδSup hM s)).1 q

private theorem eδSup_inr (hM : Facts) (s : Fin 4) (a : ↥A2) :
    (eδSup hM s ⟨a, Subgroup.mem_sup_right a.2⟩ : Y) = (lam hM s a : Y) :=
  (Classical.choose_spec (exists_eδSup hM s)).2 a

private theorem sup_Q2_lam_eq_M2 (hM : Facts) (s : Fin 4) :
    Q2 ⊔ (lam hM s).range = M2 := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · exact sup_le (hM.Q2_le_T0.trans (hM.T0_le_B0.trans hM.B0_le_M2))
      (lam_range_le_M2 hM s)
  · have hcard : Nat.card ↥(Q2 ⊔ (lam hM s).range) = Nat.card ↥M2 := by
      rw [← hM.sup_Q2_A2]
      exact (Nat.card_congr (eδSup hM s).toEquiv).symm
    exact hcard.ge

private noncomputable def eδ (hM : Facts) (s : Fin 4) : MulAut ↥M2 :=
  (MulEquiv.subgroupCongr hM.sup_Q2_A2).symm.trans
    ((eδSup hM s).trans (MulEquiv.subgroupCongr (sup_Q2_lam_eq_M2 hM s)))

private theorem lam_prod (hM : Facts) (s : Fin 4) (w : List (Fin 3)) :
    lam hM s ((w.map A2Q).prod) = (w.map (cY s)).prod := by
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  exact lam_of hM s t

private theorem eδ_of_mem_Q2 (hM : Facts) (s : Fin 4) (q : ↥Q2) (hq : (q : Y) ∈ M2) :
    ((eδ hM s ⟨(q : Y), hq⟩ : ↥M2) : Y) = (q : Y) := by
  rw [eδ, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hs : (MulEquiv.subgroupCongr hM.sup_Q2_A2).symm (⟨(q : Y), hq⟩ : ↥M2) =
      (⟨(q : Y), Subgroup.mem_sup_left q.2⟩ : ↥(Q2 ⊔ A2)) := Subtype.ext rfl
  rw [hs]
  simpa using eδSup_inl hM s q

private theorem eδ_of_mem_A2 (hM : Facts) (s : Fin 4) (a : ↥A2) (ha : (a : Y) ∈ M2) :
    ((eδ hM s ⟨(a : Y), ha⟩ : ↥M2) : Y) = (lam hM s a : Y) := by
  rw [eδ, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hs : (MulEquiv.subgroupCongr hM.sup_Q2_A2).symm (⟨(a : Y), ha⟩ : ↥M2) =
      (⟨(a : Y), Subgroup.mem_sup_right a.2⟩ : ↥(Q2 ⊔ A2)) := Subtype.ext rfl
  rw [hs]
  simpa using eδSup_inr hM s a

private def q2w (k : Fin 4) : List (Fin 10) := (dec2.getD k.val ([], [])).1
private def a2w (k : Fin 4) : List (Fin 3) := (dec2.getD k.val ([], [])).2

private theorem gB0_dec2 (hM : Facts) (k : Fin 4) :
    gB0 k = ((q2w k).map pc2Y).prod * ((a2w k).map A2gen).prod := by
  have hE := witFacts.dec2f k.val (List.mem_range.mpr k.isLt)
  have hmat := congrArg (toMat 14) hE.1
  rw [toMat_mulArr, toMat_evalP (φ := toGL) (y := pc2Y) (G := e2P)
      (hG := toMat_e2P hM), toMat_evalP (φ := toGL) (y := A2gen) (G := eA2)
      (hG := toMat_eA2 hM), gB_getD k.val k.isLt, ← Code.decode_eq_toMat,
      ← hM.toGL_gB0, ← Units.val_mul, ← map_mul] at hmat
  exact hM.toGL_injective (Units.ext hmat)

private theorem eδ_gB0 (hM : Facts) (s : Fin 4) (k : Fin 4) :
    ((eδ hM s ⟨gB0 k, hM.B0_le_M2 (hM.gB0_mem_B0 k)⟩ : ↥M2) : Y) =
      (((wWords.getD (4 + s.val) []).getD k.val []).map gB0).prod := by
  have hE := witFacts.dec2f k.val (List.mem_range.mpr k.isLt)
  have hQmem : ((q2w k).map pc2Y).prod ∈ Q2 :=
    Subgroup.list_prod_mem Q2 (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact pc2Y_mem_Q2 i)
  have hAmem : ((a2w k).map A2gen).prod ∈ A2 :=
    Subgroup.list_prod_mem A2 (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact A2gen_mem_A2 i)
  have hx : (⟨gB0 k, hM.B0_le_M2 (hM.gB0_mem_B0 k)⟩ : ↥M2) =
      (⟨((q2w k).map pc2Y).prod, by
          rw [← hM.sup_Q2_A2]
          exact Subgroup.mem_sup_left hQmem⟩ : ↥M2) *
      (⟨((a2w k).map A2gen).prod, by
          rw [← hM.sup_Q2_A2]
          exact Subgroup.mem_sup_right hAmem⟩ : ↥M2) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change gB0 k =
      ((q2w k).map pc2Y).prod * ((a2w k).map A2gen).prod
    exact gB0_dec2 hM k
  rw [hx, map_mul, Subgroup.coe_mul]
  rw [eδ_of_mem_Q2 hM s ⟨((q2w k).map pc2Y).prod, hQmem⟩ (by
        rw [← hM.sup_Q2_A2]; exact Subgroup.mem_sup_left hQmem),
      eδ_of_mem_A2 hM s ⟨((a2w k).map A2gen).prod, hAmem⟩ (by
        rw [← hM.sup_Q2_A2]; exact Subgroup.mem_sup_right hAmem)]
  have ha : lam hM s ⟨((a2w k).map A2gen).prod, hAmem⟩ =
      ((a2w k).map (cY s)).prod := by
    rw [show (⟨((a2w k).map A2gen).prod, hAmem⟩ : ↥A2) = ((a2w k).map A2Q).prod from
      Subtype.ext (by
        change (List.map A2gen (a2w k)).prod = (((a2w k).map A2Q).prod : Y)
        rw [Subgroup.val_list_prod, List.map_map]
        rfl)]
    rw [lam_prod]
  rw [ha]
  apply hM.toGL_injective
  apply Units.ext
  have hmat : (toGL (((((q2w k).map pc2Y).prod : Y) *
      (((a2w k).map (cY s)).prod : Y)) : Y) : Matrix (Fin 14) (Fin 14) F4) =
      toMat 14 (mulArr 14 (evalP e2P (q2w k))
        (evalP ((cs.getD s.val (#[], #[])).1) (a2w k))) := by
    rw [toMat_mulArr, toMat_evalP (φ := toGL) (y := pc2Y) (G := e2P)
        (hG := toMat_e2P hM), toMat_evalP (φ := toGL) (y := cY s)
        (G := (cs.getD s.val (#[], #[])).1) (hG := toMat_csP hM s),
        ← Units.val_mul, ← map_mul]
  have hE2 : toMat 14 (((wImg ()).getD (4 + s.val) #[]).getD k.val one14) =
      toMat 14 (mulArr 14 (evalP e2P (q2w k))
        (evalP ((cs.getD s.val (#[], #[])).1) (a2w k))) := by
    simpa [q2w, a2w] using congrArg (toMat 14) (hE.2 s.val (List.mem_range.mpr s.isLt))
  rw [hmat, ← hE2, toMat_wImg_eq hM (4 + s.val) k.val (by omega) k.isLt]

private noncomputable def phiEδ (hM : Facts) (s : Fin 4) : MulAut ↥M2 :=
  (eδ hM s).trans (phiM2 hM)

private theorem phiEδ_coe (hM : Facts) (s : Fin 4) (x : ↥M2) :
    ((phiEδ hM s x : ↥M2) : Y) = phiY ((eδ hM s x : ↥M2) : Y) := by
  simp [phiEδ, coe_phiM2]

private theorem phiEδ_gB0 (hM : Facts) (s : Fin 4) (k : Fin 4) :
    ((phiEδ hM s ⟨gB0 k, hM.B0_le_M2 (hM.gB0_mem_B0 k)⟩ : ↥M2) : Y) =
      (((wWords.getD (8 + s.val) []).getD k.val []).map gB0).prod := by
  apply hM.toGL_injective
  apply Units.ext
  rw [phiEδ_coe, toGL_phiY]
  rw [← toMat_wImg_eq hM (8 + s.val) k.val (by omega) k.isLt, witFacts.w8 s.val
      (List.mem_range.mpr s.isLt),
    getD_map_of_lt frobArr ((wImg ()).getD (4 + s.val) #[]) k.val one14 one14
      (by rw [wImg_row_size (4 + s.val) (by omega)]; exact k.isLt), toMat_frobArr]
  congr 1
  rw [toMat_wImg_eq hM (4 + s.val) k.val (by omega) k.isLt]
  exact congrArg (fun z => (toGL z : Matrix (Fin 14) (Fin 14) F4)) (eδ_gB0 hM s k)

theorem exists_aut_M2 (hM : Facts) (j : Fin 8) :
    ∃ e : MulAut ↥M2, ∀ (k : Fin 4) (x : ↥M2), (x : Y) = gB0 k →
      ((e x : ↥M2) : Y) =
        (((wWords.getD (4 + j.val) []).getD k.val []).map gB0).prod := by
  fin_cases j
  · exact ⟨eδ hM 0, aut_spec_of_gB0 hM hM.B0_le_M2 (eδ hM 0)
      (fun k => (((wWords.getD 4 []).getD k.val []).map gB0).prod) (eδ_gB0 hM 0)⟩
  · exact ⟨eδ hM 1, aut_spec_of_gB0 hM hM.B0_le_M2 (eδ hM 1)
      (fun k => (((wWords.getD 5 []).getD k.val []).map gB0).prod) (eδ_gB0 hM 1)⟩
  · exact ⟨eδ hM 2, aut_spec_of_gB0 hM hM.B0_le_M2 (eδ hM 2)
      (fun k => (((wWords.getD 6 []).getD k.val []).map gB0).prod) (eδ_gB0 hM 2)⟩
  · exact ⟨eδ hM 3, aut_spec_of_gB0 hM hM.B0_le_M2 (eδ hM 3)
      (fun k => (((wWords.getD 7 []).getD k.val []).map gB0).prod) (eδ_gB0 hM 3)⟩
  · exact ⟨phiEδ hM 0, aut_spec_of_gB0 hM hM.B0_le_M2 (phiEδ hM 0)
      (fun k => (((wWords.getD 8 []).getD k.val []).map gB0).prod) (phiEδ_gB0 hM 0)⟩
  · exact ⟨phiEδ hM 1, aut_spec_of_gB0 hM hM.B0_le_M2 (phiEδ hM 1)
      (fun k => (((wWords.getD 9 []).getD k.val []).map gB0).prod) (phiEδ_gB0 hM 1)⟩
  · exact ⟨phiEδ hM 2, aut_spec_of_gB0 hM hM.B0_le_M2 (phiEδ hM 2)
      (fun k => (((wWords.getD 10 []).getD k.val []).map gB0).prod) (phiEδ_gB0 hM 2)⟩
  · exact ⟨phiEδ hM 3, aut_spec_of_gB0 hM hM.B0_le_M2 (phiEδ hM 3)
      (fun k => (((wWords.getD 11 []).getD k.val []).map gB0).prod) (phiEδ_gB0 hM 3)⟩

end CFSG.Quasithin.F112R.St84.G24M
