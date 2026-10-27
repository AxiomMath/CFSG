module

public import CFSG.Monster.B.TwoA.Sp8.WordRelInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFixLayers

open _root_.Classical

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.Lifts CFSG.Monster.ScalarKernel Matrix
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix

@[expose] def XLetter.toC :
    XLetter → Cgen
  | .lift k => if h : k < 44 then h1LiftC ⟨k, h⟩ else 1
  | .pc y => pcC y
  | .sign a => if h : thetaEquiv (signPair a) ∈ Jstar then
      ⟨thetaEquiv (signPair a), Jstar_le_Cgen h⟩ else 1

@[expose] def XLetter.toD
    (ℓ : XLetter) : Dfull := iotaD (kappa ℓ.toC)

@[expose] def wordX
    (w : List XLetter) : Dfull := (w.map XLetter.toD).prod

theorem toD_lift (k : ℕ) :
    (XLetter.lift k).toD = lftD k := by
  change iotaD (kappa (if h : k < 44 then h1LiftC ⟨k, h⟩ else 1)) =
    (if h : k < 44 then h1LiftD ⟨k, h⟩ else 1)
  by_cases h : k < 44
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

theorem toD_pc
    (y : Model.Pauli) : (XLetter.pc y).toD = pcD y := rfl

theorem toD_sign_three :
    (XLetter.sign 3).toD = ghat8 := by
  have hJ : thetaEquiv (signPair 3) ∈ Jstar := by
    rw [← slPair_eq_signPair]
    exact thetaEquiv_slPair_mem_Jstar
  have hC : XLetter.toC (.sign 3) = slC := by
    rw [show XLetter.toC (.sign 3) =
        ⟨thetaEquiv (signPair 3), Jstar_le_Cgen hJ⟩ from by
      simp only [XLetter.toC, dif_pos hJ]]
    apply Subtype.ext
    show thetaEquiv (signPair 3) = thetaEquiv slPair
    rw [slPair_eq_signPair]
  change iotaD (kappa (XLetter.toC (.sign 3))) = ghat8
  rw [hC, ← ghat8_eq]

theorem wordX_nil :
    wordX [] = 1 := rfl

theorem wordX_cons
    (ℓ : XLetter) (w : List XLetter) : wordX (ℓ :: w) = ℓ.toD * wordX w := by
  rw [wordX, List.map_cons, List.prod_cons]
  rfl

theorem wordX_append
    (w w' : List XLetter) : wordX (w ++ w') = wordX w * wordX w' := by
  rw [wordX, List.map_append, List.prod_append]
  rfl

theorem wordX_map_lift
    (w : List ℕ) : wordX (w.map XLetter.lift) = wordD w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change XLetter.toD (.lift k) * wordX (w.map XLetter.lift) = lftD k * wordD w
    rw [toD_lift, ih]

theorem thetaEquiv_signPair_mem_Jstar {a : ℕ} (h : Model.conjYN a rStarN = rStarN) :
    thetaEquiv (signPair a) ∈ Jstar := by
  refine ⟨thetaEquiv_mem_Gvis _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hq : conjQ (signPair a) rStar = rStar := by
    rw [B.rStar_eq]
    exact (conjQ_sign_toQ a rStarN).trans (congrArg pauliQ h)
  have hconj := Short.thetaEquiv_conj_rhoEquiv (signPair a) rStar
  rw [hq, mul_inv_eq_iff_eq_mul] at hconj
  exact hconj

private theorem signProd_fst (as : List ℕ) :
    (((signProd as).1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      (as.map fun a => Ymat ⟨toC a, 0⟩).prod := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ih' : (((List.map signPair as).prod : Pvis).1.1 : GL SpinIdx ℚ) =
        (as.map fun a => Ymat ⟨toC a, 0⟩).prod := by
      simpa only [signProd] using ih
    simp only [signProd, List.map_cons, List.prod_cons, Subgroup.coe_mul, Prod.fst_mul,
      Units.val_mul, signPair, coe_YU, ih']

private theorem eYsN_aux (as : List ℕ) (s : Bool) (η : Bool) (c : ℕ) :
    sgn (boolZ s) • (Evec η c ᵥ* (as.map fun a => Ymat ⟨toC a, 0⟩).prod) =
      (let t := as.foldl (fun t a => let u := Model.eYN a t.2.1 t.2.2;
        (t.1 ^^ u.1, u.2.1, u.2.2)) (s, η, c)
       sgn (boolZ t.1) • Evec t.2.1 t.2.2) := by
  induction as generalizing s η c with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.prod_cons, List.foldl_cons]
    rw [← vecMul_vecMul, Evec_vecMul_Ymat, smul_vecMul, smul_smul, ← sgn_add, ← boolZ_xor]
    exact ih _ _ _

private theorem eYsN_smul_Evec (as : List ℕ) (η : Bool) (c : ℕ) :
    Evec η c ᵥ* (as.map fun a => Ymat ⟨toC a, 0⟩).prod =
      sgn (boolZ (eYsN as η c).1) • Evec (eYsN as η c).2.1 (eYsN as η c).2.2 := by
  have h := eYsN_aux as false η c
  rw [show sgn (boolZ false) = 1 from rfl, one_smul] at h
  simpa only [eYsN] using h

private theorem wFixN_testBit {a : ℕ} (h : wFixN a = true) :
    (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1 := by
  simpa [wFixN, beq_iff_eq] using h

theorem theta_signProd_keyVec_W (as : List ℕ) (ha : wFixN (xorCodes as) = true) (η : Bool)
    (c : ℕ) :
    thetaEquiv (signProd as) (keyVec (Model.Key.W η c)) =
      sgn (boolZ ((eYsN as η c).1 ^^ (Model.wordN (xorCodes as)).testBit 0)) •
        keyVec (Model.Key.W (eYsN as η c).2.1 (eYsN as η c).2.2) := by
  rw [thetaEquiv_apply]
  have hW : Model.Key.W η c = (0 + 2, if η then 1 else 0, c) := by cases η <;> rfl
  have hη : ((if η then 1 else 0 : ℕ) != 0) = η := by cases η <;> rfl
  rw [hW, theta_keyVec_W, hη, signProd_fst]
  have hsnd : (mat ((signProd as).1.2) : Matrix (Fin 24) (Fin 24) ℚ) =
      gmat (toC (xorCodes as)) := by
    rw [signProd_snd, mat_gO]
    rfl
  rw [hsnd, wvec_vecMul_gmat (xorCodes as) (wFixN_testBit ha), eYsN_smul_Evec]
  rw [tensor_smul_left, tensor_smul_right, smul_smul, Griess.inW_smul]
  rw [keyVec_W, boolZ_xor, sgn_add]

private theorem wFixN_signCodesOf : ∀ j < 11, wFixN (xorCodes (signCodesOf j)) = true := by
  intro j hj
  simp only [xorCodes, signCodesOf_xor j hj]
  interval_cases j <;> decide

private theorem fPerms_fix : ∀ j : Fin 9,
    ((fPerms[(j : ℕ)]!)[0]! = 0 ∧ (fPerms[(j : ℕ)]!)[1]! = 1) ∨
      ((fPerms[(j : ℕ)]!)[0]! = 1 ∧ (fPerms[(j : ℕ)]!)[1]! = 0) := by
  decide

private theorem keyActPauli_W (q : Model.Pauli) (η : Bool) (c : ℕ) :
    Model.keyActPauli q (Model.Key.W η c) =
      [Model.signedTerm (Model.Key.W (Model.ePauliN q η c).2.1
        (Model.ePauliN q η c).2.2) (Model.ePauliN q η c).1] := by
  cases η <;> rfl

private theorem keyActPerm_W (p : Array ℕ) (η : Bool) (c : ℕ) :
    Model.keyActPerm p (Model.Key.W η c) =
      [Model.signedTerm (Model.Key.W (Model.ePermN p η c).2.1
        (Model.ePermN p η c).2.2) ((Model.ePermN p η c).1 ^^ (p[0]! != 0))] := by
  cases η <;> rfl

private theorem keyActSign_W (a : ℕ) (η : Bool) (c : ℕ) :
    Model.keyActSign a (Model.Key.W η c) =
      [Model.signedTerm (Model.Key.W (Model.eYN a η c).2.1 (Model.eYN a η c).2.2)
        ((Model.eYN a η c).1 ^^ (Model.wordN a).testBit 0)] := by
  cases η <;> rfl

private theorem rhoEquiv_keyVec_W (q : Model.Pauli) (η : Bool) (c : ℕ) :
    (rhoEquiv (pauliQ q)) (keyVec (Model.Key.W η c)) =
      sgn (boolZ (Model.ePauliN q η c).1) •
        keyVec (Model.Key.W (Model.ePauliN q η c).2.1 (Model.ePauliN q η c).2.2) := by
  rw [keyAct_pauli_sound q (Model.Key.W η c), keyActPauli_W q η c, interp_signedTerm]

private theorem pcC_eq {y : Model.Pauli}
    (h : pauliQ y ∈ Subgroup.centralizer {rStar}) :
    pcC y = ⟨rhoEquiv (pauliQ y), rhoEquiv_mem_Cgen h⟩ := by
  change (if h : pauliQ y ∈ Subgroup.centralizer {rStar} then
    (⟨rhoEquiv (pauliQ y), rhoEquiv_mem_Cgen h⟩ : Cgen) else 1) = _
  rw [dif_pos h]

theorem toC_keyVec_W
    {ℓ : XLetter} (hℓ : ℓ.ok = true) (η : Bool) (c : ℕ) :
    (ℓ.toC : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W η c)) =
      sgn (boolZ (ℓ.actW η c).1) •
        keyVec (Model.Key.W (ℓ.actW η c).2.1 (ℓ.actW η c).2.2) := by
  cases ℓ with
  | pc q =>
    have hmem : pauliQ q ∈ Subgroup.centralizer {rStar} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hℓ
      simp only [XLetter.ok] at h
      rw [beq_iff_eq] at h
      rw [B.rStar_eq, ← pauliQ_mul, ← pauliQ_mul]
      exact congrArg pauliQ (by simpa only [rStarN] using h)
    change (pcC q : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W η c)) = _
    rw [pcC_eq hmem]
    change (rhoEquiv (pauliQ q)) (keyVec (Model.Key.W η c)) = _
    rw [rhoEquiv_keyVec_W q η c]
    simp only [XLetter.actW]
  | sign a =>
    have hok : wFixN a = true ∧ (Model.conjYN a rStarN == rStarN) = true := by
      simpa only [XLetter.ok, Bool.and_eq_true] using hℓ
    have ha : (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1 := wFixN_testBit hok.1
    have hJ : thetaEquiv (signPair a) ∈ Jstar := by
      apply thetaEquiv_signPair_mem_Jstar
      simpa only [beq_iff_eq] using hok.2
    have htoC : XLetter.toC (.sign a) = ⟨thetaEquiv (signPair a), Jstar_le_Cgen hJ⟩ := by
      simp only [XLetter.toC, dif_pos hJ]
    change (XLetter.toC (.sign a) : SpaceB ≃ₗ[ℚ] SpaceB) _ = _
    rw [htoC]
    change thetaEquiv (signPair a) (keyVec (Model.Key.W η c)) = _
    simp only [XLetter.actW]
    rw [keyAct_sign_sound a ha (Model.Key.W η c) (by
      intro h; simp [Model.Key.W] at h)]
    rw [keyActSign_W a η c, interp_signedTerm]
  | lift k =>
    have hk43 : k < 43 := by simpa only [XLetter.ok, decide_eq_true_eq] using hℓ
    have hk44 : k < 44 := by omega
    have htoC : XLetter.toC (.lift k) = h1LiftC ⟨k, hk44⟩ := by
      simp only [XLetter.toC, dif_pos hk44]
    change (XLetter.toC (.lift k) : SpaceB ≃ₗ[ℚ] SpaceB) _ = _
    rw [htoC]
    change thetaEquiv (h1Lift ⟨k, hk44⟩) (keyVec (Model.Key.W η c)) = _
    by_cases h23 : k < 23
    · rw [h1Lift_pauli (k := ⟨k, hk44⟩) h23]
      change (rhoEquiv (pauliQ (pauliGen k))) (keyVec (Model.Key.W η c)) = _
      rw [rhoEquiv_keyVec_W (pauliGen k) η c]
      simp only [XLetter.actW, if_pos h23]
    · by_cases h32 : k < 32
      · have h23le : 23 ≤ k := by omega
        have hperm : thetaEquiv (TwoA.permPair (fAut ⟨k - 23, by omega⟩))
            (keyVec (Model.Key.W η c)) =
            interp 64 (Model.keyActPerm (fPerms[k - 23]!) (Model.Key.W η c)) :=
          keyAct_perm_sound (fAut ⟨k - 23, by omega⟩) (repPerm_fAut ⟨k - 23, by omega⟩)
            (fPerms_fix ⟨k - 23, by omega⟩) (Model.Key.W η c) (by
              intro h; simp [Model.Key.W] at h)
        rw [h1Lift_perm (k := ⟨k, hk44⟩) (by simpa using h23le) h32, gPair_fAut,
          thetaEquiv_mul]
        change thetaEquiv (rhoPair (pauliQ (false, 0, epsDual (k - 23))))
          (thetaEquiv (TwoA.permPair (fAut ⟨k - 23, by omega⟩))
            (keyVec (Model.Key.W η c))) = _
        rw [hperm]
        simp only [XLetter.actW, if_neg (by omega : ¬ k < 23), if_pos h32]
        rw [keyActPerm_W (fPerms[k - 23]!) η c, interp_signedTerm, map_smul]
        change sgn (boolZ ((Model.ePermN (fPerms[k - 23]!) η c).1 ^^
            ((fPerms[k - 23]!)[0]! != 0))) •
          (rhoEquiv (pauliQ (false, 0, epsDual (k - 23))))
            (keyVec (Model.Key.W (Model.ePermN (fPerms[k - 23]!) η c).2.1
              (Model.ePermN (fPerms[k - 23]!) η c).2.2)) = _
        rw [rhoEquiv_keyVec_W (false, 0, epsDual (k - 23))
          ((Model.ePermN (fPerms[k - 23]!) η c).2.1)
          ((Model.ePermN (fPerms[k - 23]!) η c).2.2)]
        simp only [smul_smul, ← sgn_add, ← boolZ_xor]
      · have h32' : ¬ k < 32 := by omega
        have h23' : ¬ k < 23 := by omega
        rw [h1Lift_sign (k := ⟨k, hk44⟩) (by simpa using (show 32 ≤ k from by omega)) hk43]
        change thetaEquiv (signProd (signCodesOf (k - 32))) (keyVec (Model.Key.W η c)) = _
        simp only [XLetter.actW, if_neg h23', if_neg h32']
        rw [theta_signProd_keyVec_W (signCodesOf (k - 32))
          (wFixN_signCodesOf (k - 32) (by omega)) η c]

private theorem keyVec_W_ne_zero (η : Bool) (c : ℕ) :
    keyVec (Model.Key.W η c) ≠ 0 := by
  rw [keyVec_W]
  intro h
  have h' : tensor (Evec η c) wvec = 0 := by
    have hinj : Function.Injective (fun N : SpaceW => inW N) := fun x y hxy =>
      congrArg (fun z : SpaceB => z.2.2) hxy
    exact hinj (by simpa using h)
  have hw : wvec ≠ 0 := by
    intro hw0
    have := congrFun hw0 0
    simp [wvec] at this
  have hE : Evec η c ≠ 0 := by
    intro h0
    have := congrFun h0 (boolZ η, π₀ (toC c))
    simp [Evec, E] at this
  exact hE (tensor_cancel hw (by simpa [tensor] using h'))

private theorem wordC_keyVec_W
    (w : List XLetter) (hw : w.all XLetter.ok = true) (η : Bool) (c : ℕ) :
    (((w.map XLetter.toC).prod : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W η c)) =
      sgn (boolZ (xTrack w η c).1) •
        keyVec (Model.Key.W (xTrack w η c).2.1 (xTrack w η c).2.2) := by
  induction w with
  | nil => simp [xTrack, sgn]
  | cons ℓ w ih =>
    rw [List.all_cons, Bool.and_eq_true] at hw
    change ((XLetter.toC ℓ : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB)
      (((((w.map XLetter.toC).prod : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB))
        (keyVec (Model.Key.W η c))) = _
    rw [ih hw.2, map_smul, toC_keyVec_W hw.1]
    simp only [smul_smul, xTrack, List.foldr_cons, ← sgn_add, ← boolZ_xor]

private theorem conjQ_mem_centralizer {p : Pvis} {q : Q}
    (hp : conjQ p rStar = rStar) (hq : q ∈ Subgroup.centralizer {rStar}) :
    conjQ p q ∈ Subgroup.centralizer {rStar} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hq ⊢
  calc conjQ p q * rStar = conjQ p q * conjQ p rStar := by rw [hp]
    _ = conjQ p (q * rStar) := (map_mul _ _ _).symm
    _ = conjQ p (rStar * q) := by rw [hq]
    _ = conjQ p rStar * conjQ p q := map_mul _ _ _
    _ = rStar * conjQ p q := by rw [hp]

private theorem conjQ_eq_rStar_of_mem_Jstar {p : Pvis} (hp : thetaEquiv p ∈ Jstar) :
    conjQ p rStar = rStar := by
  apply rhoEquiv_injective
  rw [← Short.thetaEquiv_conj_rhoEquiv]
  exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_singleton_iff.1 hp.2)

private theorem pcC_conj_pvis {p : Pvis} (hp : thetaEquiv p ∈ Jstar) {y : Model.Pauli}
    (hy : pauliQ y ∈ Subgroup.centralizer {rStar}) {y' : Model.Pauli}
    (hq' : pauliQ y' = conjQ p (pauliQ y)) :
    pauliQ y' ∈ Subgroup.centralizer {rStar} ∧
      (⟨thetaEquiv p, Jstar_le_Cgen hp⟩ : Cgen) * pcC y *
          (⟨thetaEquiv p, Jstar_le_Cgen hp⟩ : Cgen)⁻¹ = pcC y' := by
  have hp' : conjQ p rStar = rStar := conjQ_eq_rStar_of_mem_Jstar hp
  have hy' : pauliQ y' ∈ Subgroup.centralizer {rStar} := by
    rw [hq']
    exact conjQ_mem_centralizer hp' hy
  refine ⟨hy', ?_⟩
  rw [pcC_eq hy, pcC_eq hy']
  apply Subtype.ext
  show thetaEquiv p * rhoEquiv (pauliQ y) * (thetaEquiv p)⁻¹ = rhoEquiv (pauliQ y')
  rw [hq']
  exact Short.thetaEquiv_conj_rhoEquiv p (pauliQ y)

private theorem pcD_rStarN : pcD rStarN = 1 := by
  have hstar : pauliQ rStarN = rStar := by rw [rStarN, ← B.rStar_eq]
  have hmem : pauliQ rStarN ∈ Subgroup.centralizer {rStar} := by
    rw [hstar]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hc : pcC rStarN = tStarC := by
    rw [pcC_eq hmem]
    apply Subtype.ext
    show rhoEquiv (pauliQ rStarN) = tStar
    rw [hstar]
    rfl
  rw [pcD, hc, (kappa_eq_one_iff tStarC).2 (Or.inr rfl), map_one]

private theorem wordX_eq_iotaD_prod
    (w : List XLetter) :
    wordX w = iotaD (kappa ((w.map XLetter.toC).prod)) := by
  induction w with
  | nil => rw [wordX_nil, List.map_nil, List.prod_nil, map_one, map_one]
  | cons ℓ w ih =>
    rw [wordX_cons, ih, List.map_cons, List.prod_cons, map_mul, map_mul]
    rfl


theorem letter_mem_Jhat {ℓ : XLetter} (hℓ : ℓ.ok = true) : ℓ.toD ∈ Jhat := by
  cases ℓ with
  | lift k =>
    have hk43 : k < 43 := by
      simpa only [XLetter.ok, decide_eq_true_eq] using hℓ
    have hk : k < 44 := by omega
    rw [XLetter.toD, show XLetter.toC (.lift k) = h1LiftC ⟨k, hk⟩ from by
      simp only [XLetter.toC, dif_pos hk]]
    exact h1LiftD_mem_Jhat ⟨k, hk⟩
  | pc y =>
    show pcD y ∈ Jhat
    exact Ehat_le_Jhat (pcD_mem_Ehat y)
  | sign a =>
    have hok : wFixN a = true ∧ (Model.conjYN a rStarN == rStarN) = true := by
      simpa only [XLetter.ok, Bool.and_eq_true] using hℓ
    have hJ : thetaEquiv (signPair a) ∈ Jstar := by
      apply thetaEquiv_signPair_mem_Jstar
      simpa only [beq_iff_eq] using hok.2
    rw [XLetter.toD, show XLetter.toC (.sign a) =
        ⟨thetaEquiv (signPair a), Jstar_le_Cgen hJ⟩ from by
      simp only [XLetter.toC, dif_pos hJ]]
    rw [Jhat_eq_map]
    exact ⟨kappa ⟨thetaEquiv (signPair a), Jstar_le_Cgen hJ⟩, kappa_mem_Jbar hJ, rfl⟩

theorem wordX_mem_Jhat {w : List XLetter} (hw : w.all XLetter.ok = true) : wordX w ∈ Jhat := by
  induction w with
  | nil => rw [wordX_nil]; exact Jhat.one_mem
  | cons ℓ w ih =>
    rw [List.all_cons, Bool.and_eq_true] at hw
    rw [wordX_cons]
    exact Jhat.mul_mem (letter_mem_Jhat hw.1) (ih hw.2)

private theorem letter_conj_pcD {ℓ : XLetter} (hℓ : ℓ.ok = true) {y : Model.Pauli}
    (hy : pauliQ y ∈ Subgroup.centralizer {rStar}) :
    pauliQ (ℓ.conjN y) ∈ Subgroup.centralizer {rStar} ∧
      ℓ.toD * pcD y * (ℓ.toD)⁻¹ = pcD (ℓ.conjN y) := by
  cases ℓ with
  | pc q =>
    have hq : pauliQ q ∈ Subgroup.centralizer {rStar} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hℓ
      simp only [XLetter.ok] at h
      rw [beq_iff_eq] at h
      rw [B.rStar_eq, ← pauliQ_mul, ← pauliQ_mul]
      exact congrArg pauliQ (by simpa only [rStarN] using h)
    have hpJ : thetaEquiv (rhoPair (pauliQ q)) ∈ Jstar :=
      rhoCQ_le_Jstar (mem_rhoCQ.2 ⟨pauliQ q, hq, rfl⟩)
    have hmem := (pcC_conj_pvis hpJ hy (y' := Model.conjPauliN q y)
      (conjQ_rhoPair_toQ q y).symm).1
    have hpcq : pcC q = ⟨thetaEquiv (rhoPair (pauliQ q)), Jstar_le_Cgen hpJ⟩ := by
      rw [pcC_eq hq]
      exact Subtype.ext rfl
    refine ⟨hmem, ?_⟩
    change iotaD (kappa (pcC q)) * pcD y * (iotaD (kappa (pcC q)))⁻¹ =
      pcD (Model.conjPauliN q y)
    rw [hpcq]
    have h := congrArg (fun c : Cgen => iotaD (kappa c))
      (pcC_conj_pvis hpJ hy (y' := Model.conjPauliN q y) (conjQ_rhoPair_toQ q y).symm).2
    simp only [map_mul, map_inv] at h
    exact h
  | sign a =>
    have hok : wFixN a = true ∧ (Model.conjYN a rStarN == rStarN) = true := by
      simpa only [XLetter.ok, Bool.and_eq_true] using hℓ
    have hJ : thetaEquiv (signPair a) ∈ Jstar := by
      apply thetaEquiv_signPair_mem_Jstar
      simpa only [beq_iff_eq] using hok.2
    have hmem := (pcC_conj_pvis hJ hy (y' := Model.conjYN a y)
      (conjQ_sign_toQ a y).symm).1
    refine ⟨hmem, ?_⟩
    change iotaD (kappa (if h : thetaEquiv (signPair a) ∈ Jstar then
        (⟨thetaEquiv (signPair a), Jstar_le_Cgen h⟩ : Cgen) else 1)) *
        pcD y *
        (iotaD (kappa (if h : thetaEquiv (signPair a) ∈ Jstar then
        (⟨thetaEquiv (signPair a), Jstar_le_Cgen h⟩ : Cgen) else 1)))⁻¹ =
      pcD (Model.conjYN a y)
    rw [dif_pos hJ]
    have h := congrArg (fun c : Cgen => iotaD (kappa c))
      (pcC_conj_pvis hJ hy (y' := Model.conjYN a y) (conjQ_sign_toQ a y).symm).2
    simp only [map_mul, map_inv] at h
    exact h
  | lift k =>
    have hk43 : k < 43 := by simpa only [XLetter.ok, decide_eq_true_eq] using hℓ
    have hk44 : k < 44 := by omega
    have hmem : pauliQ (h1ConjN k y) ∈ Subgroup.centralizer {rStar} :=
      pauliQ_h1ConjN_mem ⟨k, hk44⟩ hy
    refine ⟨by simpa only [XLetter.conjN] using hmem, ?_⟩
    have h := h1LiftD_conj_pcD (⟨k, hk44⟩ : Fin 44) hy
    simpa only [XLetter.toD, XLetter.toC, XLetter.conjN, h1LiftD, dif_pos hk44] using h

private theorem wordX_conj_pcD : ∀ (w : List XLetter), w.all XLetter.ok = true →
    ∀ {y : Model.Pauli}, pauliQ y ∈ Subgroup.centralizer {rStar} →
      pauliQ (xConj w y) ∈ Subgroup.centralizer {rStar} ∧
        wordX w * pcD y * (wordX w)⁻¹ = pcD (xConj w y)
  | [], _, y, hy => by
    refine ⟨by simpa only [xConj, List.foldr_nil] using hy, ?_⟩
    rw [xConj, List.foldr_nil, wordX_nil, one_mul, inv_one, mul_one]
  | ℓ :: w, hw, y, hy => by
    rw [List.all_cons, Bool.and_eq_true] at hw
    obtain ⟨h1, h2⟩ := wordX_conj_pcD w hw.2 hy
    obtain ⟨h3, h4⟩ := letter_conj_pcD hw.1 h1
    refine ⟨by simpa only [xConj, List.foldr_cons] using h3, ?_⟩
    change ℓ.toD * wordX w * pcD y * (ℓ.toD * wordX w)⁻¹ = pcD (ℓ.conjN (xConj w y))
    rw [← h4, ← h2]
    group

private theorem pauliD_eq_pcD (i : Fin 23) : pauliD i = pcD (pauliGen i) := by
  rw [pauliD, ← lftD_of_lt (show (i : ℕ) < 44 by omega), lftD_pauli i.2]

private theorem pcD_eq_of_pcEqN {y y' : Model.Pauli}
    (hy' : pauliQ y' ∈ Subgroup.centralizer {rStar}) (h : pcEqN y y' = true) :
    pcD y = pcD y' := by
  rw [pcEqN, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  have hstar : pauliQ rStarN ∈ Subgroup.centralizer {rStar} := by
    rw [show pauliQ rStarN = rStar from by rw [rStarN, ← B.rStar_eq]]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  rcases h with h | h
  · rw [h]
  · rw [h, pcD_mul hy' hstar, pcD_rStarN, one_mul]

theorem wordX_eq_of_relCheck {w w' : List XLetter} (h : relCheck w w' = true) :
    wordX w = wordX w' := by
  unfold relCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hw, hw'⟩, hpc⟩, htrack⟩ := h
  rw [List.all_eq_true] at hpc
  have htrack_eq : xTrack w false 0 = xTrack w' false 0 := beq_iff_eq.1 htrack
  have hconj : ∀ i : Fin 23, pcD (xConj w (pauliGen i)) = pcD (xConj w' (pauliGen i)) := by
    intro i
    exact pcD_eq_of_pcEqN
      (wordX_conj_pcD w' hw' (pauliQ_pauliGen_mem i i.2)).1
      (hpc i (List.mem_range.2 i.2))
  let g : Dfull := (wordX w')⁻¹ * wordX w
  have hgcomm : ∀ i : Fin 23, g * pauliD i = pauliD i * g := by
    intro i
    have h1 := (wordX_conj_pcD w hw (pauliQ_pauliGen_mem i i.2)).2
    have h2 := (wordX_conj_pcD w' hw' (pauliQ_pauliGen_mem i i.2)).2
    have h3 := hconj i
    have h4 : wordX w * pcD (pauliGen i) * (wordX w)⁻¹ =
        wordX w' * pcD (pauliGen i) * (wordX w')⁻¹ := h1.trans (h3.trans h2.symm)
    rw [pauliD_eq_pcD i]
    show g * pcD (pauliGen i) = pcD (pauliGen i) * g
    rw [show g * pcD (pauliGen i) =
        (wordX w')⁻¹ * (wordX w * pcD (pauliGen i) * (wordX w)⁻¹) * wordX w from by
      unfold g; group,
      h4,
      show pcD (pauliGen i) * g =
        (wordX w')⁻¹ * (wordX w' * pcD (pauliGen i) * (wordX w')⁻¹) * wordX w from by
      unfold g; group]
  have hgJ : g ∈ Jhat :=
    Jhat.mul_mem (Jhat.inv_mem (wordX_mem_Jhat hw')) (wordX_mem_Jhat hw)
  have hgcent : g ∈ Subgroup.centralizer (Ehat : Set Dfull) := by
    rw [Ehat_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    exact (hgcomm i).symm
  have hgz : g = 1 ∨ g = xhat := by
    have hmem : g ∈ Jhat ⊓ Subgroup.centralizer (Ehat : Set Dfull) := ⟨hgJ, hgcent⟩
    rwa [centralizer_Ehat, mem_zpowers_xhat_iff] at hmem
  rcases hgz with hg1 | hgx
  · exact (inv_mul_eq_one.1 hg1).symm
  · exfalso
    have hmain : wordX w = wordX w' * xhat := by
      rw [← hgx]
      show wordX w = wordX w' * g
      unfold g
      group
    let G : Cgen := (w.map XLetter.toC).prod
    let G' : Cgen := (w'.map XLetter.toC).prod
    have hword_w : wordX w = iotaD (kappa G) := wordX_eq_iotaD_prod w
    have hword_w' : wordX w' = iotaD (kappa G') := wordX_eq_iotaD_prod w'
    have hxhat : xhat = iotaD (kappa xC) := by
      rw [← iotaD_xbar]
      rfl
    have hk : kappa G = kappa (G' * xC) := by
      apply iotaD_injective
      simp only [map_mul]
      rw [← hword_w, ← hword_w', ← hxhat]
      exact hmain
    have hker : kappa (G * (G' * xC)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hk, ← map_mul]
      exact mul_inv_cancel _
    have hk0 : keyVec (Model.Key.W false 0) = 0 := by
      have hxC : (xC : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
          - keyVec (Model.Key.W false 0) := by
        change (rhoEquiv zQ) (keyVec (Model.Key.W false 0)) =
          - keyVec (Model.Key.W false 0)
        rw [← Census.pauliQ_z, rhoEquiv_keyVec_W (true, 0, 0) false 0]
        have he : Model.ePauliN (true, 0, 0) false 0 = (true, false, 0) := by decide
        rw [he]
        show (if (1 : ZMod 2) = 0 then (1 : ℚ) else -1) •
            keyVec (Model.Key.W false 0) = -keyVec (Model.Key.W false 0)
        rw [if_neg (by decide)]
        exact neg_one_smul ℚ (keyVec (Model.Key.W false 0))
      have htS : (tStarC : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
          keyVec (Model.Key.W false 0) := by
        change (rhoEquiv rStar) (keyVec (Model.Key.W false 0)) =
          keyVec (Model.Key.W false 0)
        rw [B.rStar_eq, rhoEquiv_keyVec_W (false, 0, 191) false 0]
        have he : Model.ePauliN (false, 0, 191) false 0 = (false, false, 0) := by decide
        rw [he]
        show (if (0 : ZMod 2) = 0 then (1 : ℚ) else -1) •
            keyVec (Model.Key.W false 0) = keyVec (Model.Key.W false 0)
        rw [if_pos rfl, one_smul]
      have hneg : (G : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
          - ((G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) := by
        rcases (kappa_eq_one_iff (G * (G' * xC)⁻¹)).1 hker with hG | hG
        · have hGe : G = G' * xC := mul_inv_eq_one.1 hG
          calc (G : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
              ((G' * xC : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) := by
                rw [hGe]
            _ = (G' : SpaceB ≃ₗ[ℚ] SpaceB)
                ((xC : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) := rfl
            _ = (G' : SpaceB ≃ₗ[ℚ] SpaceB) (- keyVec (Model.Key.W false 0)) := by rw [hxC]
            _ = - ((G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) := map_neg _ _
        · have hGe : G = (G' * xC) * tStarC := by
            calc G = tStarC * (G' * xC) := mul_inv_eq_iff_eq_mul.1 hG
              _ = (G' * xC) * tStarC :=
                (Subgroup.mem_center_iff.1 tStarC_mem_center (G' * xC)).symm
          calc (G : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
              (((G' * xC) * tStarC : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB)
                (keyVec (Model.Key.W false 0)) := by rw [hGe]
            _ = ((G' * xC : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB)
                ((tStarC : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) := rfl
            _ = ((G' * xC : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB)
                (keyVec (Model.Key.W false 0)) := by rw [htS]
            _ = (G' : SpaceB ≃ₗ[ℚ] SpaceB)
                ((xC : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) := rfl
            _ = (G' : SpaceB ≃ₗ[ℚ] SpaceB) (- keyVec (Model.Key.W false 0)) := by rw [hxC]
            _ = - ((G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) := map_neg _ _
      have htrackG : (G : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
          sgn (boolZ (xTrack w false 0).1) •
            keyVec (Model.Key.W (xTrack w false 0).2.1 (xTrack w false 0).2.2) :=
        wordC_keyVec_W w hw false 0
      have htrackG' : (G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
          sgn (boolZ (xTrack w' false 0).1) •
            keyVec (Model.Key.W (xTrack w' false 0).2.1 (xTrack w' false 0).2.2) :=
        wordC_keyVec_W w' hw' false 0
      have heq : (G : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) =
          (G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) := by
        rw [htrackG, htrackG', htrack_eq]
      have hzero : (G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) = 0 := by
        have h : - ((G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) =
            (G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0)) :=
          hneg.symm.trans heq
        have h2 : ((G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) +
            ((G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) = 0 := by
          nth_rewrite 1 [← h]
          exact neg_add_cancel _
        have h3 : (2 : ℚ) • ((G' : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec (Model.Key.W false 0))) = 0 := by
          rw [two_smul, h2]
        exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
      apply (G' : SpaceB ≃ₗ[ℚ] SpaceB).injective
      rw [hzero, map_zero]
    exact keyVec_W_ne_zero false 0 hk0

end CFSG.Monster.B.TwoA.Sp8.WordRel
