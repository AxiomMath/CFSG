module

public import CFSG.Monster.B.Cbar.GenData
public import CFSG.Monster.Visible.PermCompat

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.ScalarKernel Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

@[expose] def epsP (p : AutPerm) : ZMod 2 := kappaP p ΩC

@[expose] def gammaP (p : AutPerm) (a : C) : ZMod 2 :=
  kappaP p a + epsP p * (permC p a : Fin 24 → ZMod 2) 0

@[expose] def e0Cls : Cocode := Submodule.Quotient.mk (Pi.single 0 1)

@[expose] def hE0 : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv (DQ e0Cls)

@[expose] def permPair (p : AutPerm) : Pvis := ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩

@[expose] def gLift (p : AutPerm) : SpaceB ≃ₗ[ℚ] SpaceB :=
  hE0 ^ (epsP p).val * thetaEquiv (permPair p)

@[expose] def gPair (p : AutPerm) : Pvis := permPair p * rhoPair (DQ (epsP p • e0Cls))

theorem DQ_add (δ δ' : Cocode) : DQ (δ + δ') = DQ δ * DQ δ' := by
  rw [DQ_eq, DQ_eq, DQ_eq, ← map_mul]
  congr 1
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, pair_zero_left, add_zero]
  · simp only [SpinCoord.mul_a, add_zero]
  · simp only [SpinCoord.mul_δ]

theorem DQ_zero : DQ 0 = 1 := by
  rw [DQ_eq]
  exact map_one spinEquiv

theorem DQ_comm (δ δ' : Cocode) : DQ δ * DQ δ' = DQ δ' * DQ δ := by
  rw [← DQ_add, ← DQ_add, add_comm]

theorem rhoEquiv_DQ_smul (ε : ZMod 2) (δ : Cocode) :
    rhoEquiv (DQ (ε • δ)) = rhoEquiv (DQ δ) ^ ε.val := by
  rcases zmod2_cases ε with rfl | rfl
  · rw [zero_smul, DQ_zero, ZMod.val_zero, pow_zero, rhoEquiv_one']
  · rw [one_smul, ZMod.val_one, pow_one]

theorem gLift_eq (p : AutPerm) : gLift p = thetaEquiv (gPair p) := by
  rw [gLift, gPair, thetaEquiv_mul, hE0, ← rhoEquiv_DQ_smul]
  rfl

theorem gLift_mem_Gvis (p : AutPerm) : gLift p ∈ Gvis := by
  rw [gLift_eq]
  exact thetaEquiv_mem_Gvis _

theorem pair_smul_e0Cls (a : C) (ε : ZMod 2) :
    pair a (ε • e0Cls) = ε * (a : Fin 24 → ZMod 2) 0 := by
  rw [map_smul, e0Cls, pair_mk, smul_eq_mul, dotProduct_single, mul_one]

theorem ΩC_apply_zero : (ΩC : Fin 24 → ZMod 2) 0 = 1 := rfl

theorem conjQ_gPair (p : AutPerm) (t : Q) :
    conjQ (gPair p) t = (DQ (epsP p • e0Cls))⁻¹ * conjSp p t * DQ (epsP p • e0Cls) := by
  rw [gPair, conjQ_mul, conjQ_rhoPair]
  rfl

theorem conjQ_gPair_DQ (p : AutPerm) (δ : Cocode) : conjQ (gPair p) (DQ δ) = DQ (permD p δ) := by
  rw [conjQ_gPair, conjSp_DQ, mul_assoc, DQ_comm (permD p δ), ← mul_assoc, inv_mul_cancel,
    one_mul]

theorem coordOf_zQ_pow_mul (k : ZMod 2) (r : Q) : coordOf (zQ ^ k.val * r) = coordOf r := by
  unfold coordOf
  rw [symm_zQ_pow_mul]
  refine Prod.ext ?_ ?_
  · exact zero_add _
  · exact zero_add _

theorem coordOf_XQ (e : Parker) : coordOf (XQ e) = (e.code, thetaD e.code) := by
  unfold coordOf
  rw [XQ_eq, MulEquiv.symm_apply_apply]

theorem spinCoord_z_mul_z_mul (k k' : ZMod 2) (x : SpinCoord) :
    (⟨k, 0, 0⟩ : SpinCoord) * ((⟨k', 0, 0⟩ : SpinCoord) * x) = ⟨k' + k, 0, 0⟩ * x := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, SpinCoord.mul_a, pair_zero_right, add_zero]
    ring
  · simp only [SpinCoord.mul_a, zero_add]
  · simp only [SpinCoord.mul_δ, zero_add]

theorem conj_DQ_zQ_XQ (δ : Cocode) (k : ZMod 2) (b : C) (s : ZMod 2) :
    (DQ δ)⁻¹ * (zQ ^ k.val * XQ ⟨b, s⟩) * DQ δ = zQ ^ (k + pair b δ).val * XQ ⟨b, s⟩ := by
  apply spinEquiv.symm.injective
  have h1 := Generated.OddCocode.symm_conj_DQ δ (zQ ^ k.val * XQ ⟨b, s⟩)
  have h2 := symm_zQ_pow_mul k (XQ ⟨b, s⟩)
  have h3 := symm_zQ_pow_mul (k + pair b δ) (XQ ⟨b, s⟩)
  have h4 : (coordOf (zQ ^ k.val * XQ ⟨b, s⟩)).1 = b := by
    rw [coordOf_zQ_pow_mul, coordOf_XQ]
  rw [h1, h3, h2, h4]
  exact spinCoord_z_mul_z_mul _ _ _

theorem conjQ_gPair_XQ (p : AutPerm) (e : Parker) :
    conjQ (gPair p) (XQ e) = zQ ^ (gammaP p e.code).val * XQ ⟨permC p e.code, e.sign⟩ := by
  rw [conjQ_gPair, conjSp_XQ, conj_DQ_zQ_XQ, pair_smul_e0Cls]
  rfl

theorem conjQ_gPair_XQ_mul_DQ (p : AutPerm) (e : Parker) (δ : Cocode) :
    conjQ (gPair p) (XQ e * DQ δ) =
      zQ ^ (gammaP p e.code).val * (XQ ⟨permC p e.code, e.sign⟩ * DQ (permD p δ)) := by
  rw [map_mul, conjQ_gPair_XQ, conjQ_gPair_DQ, mul_assoc]

theorem Xlift_conjQ_gPair_XQ_mul_DQ (p : AutPerm) (e : Parker) (δ : Cocode) :
    Xlift (conjQ (gPair p) (XQ e * DQ δ)) =
      sgn (gammaP p e.code) • Xlift (XQ ⟨permC p e.code, e.sign⟩ * DQ (permD p δ)) := by
  rw [conjQ_gPair_XQ_mul_DQ, Xlift_zQ_pow_mul]

theorem gammaP_add (p : AutPerm) (a b : C) :
    gammaP p (a + b) + gammaP p a + gammaP p b = betaP p a b := by
  have h := kappaP_add p a b
  unfold gammaP
  rw [map_add, Submodule.coe_add, Pi.add_apply]
  linear_combination h + (epsP p * (permC p a : Fin 24 → ZMod 2) 0 +
    epsP p * (permC p b : Fin 24 → ZMod 2) 0) * two_eq_zero'

theorem gammaP_ΩC (p : AutPerm) : gammaP p ΩC = 0 := by
  rw [gammaP, permC_ΩC, ΩC_apply_zero, mul_one, epsP]
  linear_combination kappaP p ΩC * two_eq_zero'

theorem gammaP_add_ΩC (p : AutPerm) (c : C) : gammaP p (c + ΩC) = gammaP p c := by
  have h := gammaP_add p c ΩC
  rw [betaP_ΩC, gammaP_ΩC, add_zero] at h
  linear_combination h - gammaP p c * two_eq_zero'

theorem gammaP_add_smul_ΩC (p : AutPerm) (c : C) (m : ZMod 2) :
    gammaP p (c + m • ΩC) = gammaP p c := by
  rcases zmod2_cases m with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul, gammaP_add_ΩC]

@[expose] def gSpin (p : AutPerm) : Matrix SpinIdx SpinIdx ℚ := smat p * Dmat (epsP p • e0Cls)

theorem coe_gPair_fst (p : AutPerm) :
    (((gPair p).1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = gSpin p := by
  rw [gPair, Subgroup.coe_mul, Prod.fst_mul, coe_rhoPair, Units.val_mul]
  rfl

theorem mat_gPair_snd (p : AutPerm) : mat (gPair p).1.2 = Pmat p := by
  rw [gPair, Subgroup.coe_mul, Prod.snd_mul, coe_rhoPair, mul_one]
  rfl

theorem permC_coe_apply (p : AutPerm) (c : C) (i : Fin 24) :
    (permC p c : Fin 24 → ZMod 2) ((p : Equiv.Perm (Fin 24)) i) = (c : Fin 24 → ZMod 2) i := by
  rw [coe_permC]
  exact permWord_apply _ _ _

theorem E_vecMul_gSpin (p : AutPerm) (η : ZMod 2) (c : C₀) :
    E η c ᵥ* gSpin p = sgn (gammaP p c + η * μ₀ (permC p c)) • E η (π₀ (permC p c)) := by
  rw [gSpin, ← vecMul_vecMul, E_vecMul_smat, smul_vecMul, E_vecMul_Dmat, smul_smul,
    pair_smul_e0Cls, pair_smul_e0Cls, ΩC_apply_zero, mul_one, ← sgn_add]
  have hc : ((π₀ (permC p c) : C) : Fin 24 → ZMod 2) 0 =
      (permC p c : Fin 24 → ZMod 2) 0 + μ₀ (permC p c) := by
    rw [coe_π₀, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, coe_ΩC]
    rw [show (Ω : Fin 24 → ZMod 2) 0 = 1 from rfl, smul_eq_mul, mul_one]
  have he : η + kappaP p ΩC + epsP p = η := by
    rw [epsP]
    linear_combination kappaP p ΩC * two_eq_zero'
  rw [he, hc]
  have hs : kappaP p ↑c + (η + kappaP p ΩC) * μ₀ ((permC p) ↑c) +
      epsP p * ((permC p c : Fin 24 → ZMod 2) 0 + μ₀ (permC p c)) =
      gammaP p c + η * μ₀ (permC p c) := by
    rw [gammaP, epsP]
    linear_combination kappaP p ΩC * μ₀ (permC p c) * two_eq_zero'
  rw [hs]

theorem permWord_single (p : Equiv.Perm (Fin 24)) (i : Fin 24) :
    permWord p (Pi.single i 1) = Pi.single (p i) 1 := by
  funext k
  rw [permWord_apply']
  by_cases hk : k = p i
  · subst hk
    simp
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne]
    intro h
    exact hk (by rw [← h]; simp)

theorem permD_single (p : AutPerm) (i : Fin 24) :
    permD p (Submodule.Quotient.mk (Pi.single i 1)) =
      Submodule.Quotient.mk (Pi.single ((p : Equiv.Perm (Fin 24)) i) 1) := by
  rw [permD_mk, permWord_single]

theorem permD_deltaPair (p : AutPerm) (i j : Fin 24) :
    permD p (deltaPair i j) =
      deltaPair ((p : Equiv.Perm (Fin 24)) i) ((p : Equiv.Perm (Fin 24)) j) := by
  rw [deltaPair, permD_mk, deltaPair]
  congr 1
  have h : permWord p (Pi.single i 1 + Pi.single j 1) =
      permWord p (Pi.single i 1) + permWord p (Pi.single j 1) := rfl
  rw [h, permWord_single, permWord_single]

theorem deltaPair_comm (i j : Fin 24) : deltaPair i j = deltaPair j i := by
  rw [deltaPair, deltaPair, add_comm]

@[expose] def mapSet (p : AutPerm) (δ : Finset (Fin 24)) : Finset (Fin 24) :=
  δ.map (p : Equiv.Perm (Fin 24)).toEmbedding

theorem card_mapSet (p : AutPerm) (δ : Finset (Fin 24)) : (mapSet p δ).card = δ.card :=
  Finset.card_map _

theorem permWord_ind (p : AutPerm) (δ : Finset (Fin 24)) :
    permWord p (Octad.ind δ) = Octad.ind (mapSet p δ) := by
  funext k
  rw [permWord_apply', Octad.ind_apply, Octad.ind_apply]
  have h : (p : Equiv.Perm (Fin 24))⁻¹ k ∈ δ ↔ k ∈ mapSet p δ := by
    rw [mapSet, Finset.mem_map_equiv]
    rfl
  by_cases hk : k ∈ mapSet p δ
  · rw [ite_eq_left (h.2 hk), ite_eq_left hk]
  · rw [ite_eq_right (fun h' => hk (h.1 h')), ite_eq_right hk]

theorem permD_ind (p : AutPerm) (δ : Finset (Fin 24)) :
    permD p (Submodule.Quotient.mk (Octad.ind δ)) =
      Submodule.Quotient.mk (Octad.ind (mapSet p δ)) := by
  rw [permD_mk, permWord_ind]

theorem nOct_mapSet (p : AutPerm) (δ : Finset (Fin 24)) : nOct (mapSet p δ) = nOct δ := by
  rw [nOct, nOct, card_mapSet]

theorem mk_zero_X_smul' (s : ℚ) (x : SpaceX) :
    ((0 : symMat), s • x, (0 : SpaceW)) = s • ((0 : symMat), x, (0 : SpaceW)) := by
  rw [Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem Xlift_conj_rMinus (p : AutPerm) (i j : Fin 24) :
    Xlift (conjQ (gPair p) (rMinus i j)) =
      Xlift (rMinus ((p : Equiv.Perm (Fin 24)) i) ((p : Equiv.Perm (Fin 24)) j)) := by
  rw [rMinus, conjQ_gPair_DQ, permD_deltaPair]
  rfl

theorem Xlift_conj_rPlus (p : AutPerm) (i j : Fin 24) :
    Xlift (conjQ (gPair p) (rPlus i j)) =
      Xlift (rPlus ((p : Equiv.Perm (Fin 24)) i) ((p : Equiv.Perm (Fin 24)) j)) := by
  rw [rPlus, Xlift_conjQ_gPair_XQ_mul_DQ, gammaP_ΩC, sgn_zero, one_smul, permD_deltaPair]
  simp only [permC_ΩC]
  rfl

theorem permC_aOdd (p : AutPerm) (c : C₀) (i : Fin 24) :
    permC p (aOdd c i) = aOdd (π₀ (permC p c)) ((p : Equiv.Perm (Fin 24)) i) := by
  apply Subtype.ext
  have hP : P ((π₀ (permC p c) : C) : Fin 24 → ZMod 2) = P ((c : C) : Fin 24 → ZMod 2) := by
    rw [coe_π₀, Submodule.coe_add, Submodule.coe_smul, coe_ΩC, P_add_smul_Ω (permC p c).2,
      coe_permC, P_permWord]
  have hi : ((π₀ (permC p c) : C) : Fin 24 → ZMod 2) ((p : Equiv.Perm (Fin 24)) i) =
      ((c : C) : Fin 24 → ZMod 2) i + μ₀ (permC p c) := by
    rw [coe_π₀, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, coe_ΩC,
      permC_coe_apply, show (Ω : Fin 24 → ZMod 2) _ = 1 from rfl, smul_eq_mul, mul_one]
  have hl : ((permC p (aOdd c i) : C) : Fin 24 → ZMod 2) =
      (permC p (c : C) : Fin 24 → ZMod 2) + mOdd c i • Ω := by
    rw [aOdd, map_add, map_smul, permC_ΩC, Submodule.coe_add, Submodule.coe_smul, coe_ΩC]
  rw [hl, coe_aOdd, mOdd, mOdd, hP, hi, coe_π₀, Submodule.coe_add, Submodule.coe_smul, coe_ΩC]
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(μ₀ (permC p c) * Ω k) * two_eq_zero'

theorem Xlift_conj_rOdd (p : AutPerm) (c : C₀) (i : Fin 24) :
    Xlift (conjQ (gPair p) (rOdd c i)) =
      sgn (gammaP p c) • Xlift (rOdd (π₀ (permC p c)) ((p : Equiv.Perm (Fin 24)) i)) := by
  rw [rOdd, Xlift_conjQ_gPair_XQ_mul_DQ, aOdd, gammaP_add_smul_ΩC, permD_single]
  simp only
  rw [show permC p ((c : C) + mOdd c i • ΩC) = permC p (aOdd c i) from rfl, permC_aOdd]
  rfl

theorem permC_aOct (p : AutPerm) (d : C) (δ : Finset (Fin 24)) :
    permC p (aOct d δ) = aOct (permC p d) (mapSet p δ) := by
  rw [aOct, aOct, map_add, map_smul, permC_ΩC, nOct_mapSet]

theorem Xlift_conj_rOct (p : AutPerm) (d : C) (δ : Finset (Fin 24)) :
    Xlift (conjQ (gPair p) (rOct d δ)) =
      sgn (gammaP p d) • Xlift (rOct (permC p d) (mapSet p δ)) := by
  rw [rOct, Xlift_conjQ_gPair_XQ_mul_DQ, aOct, gammaP_add_smul_ΩC, permD_ind]
  simp only
  rw [show permC p (d + nOct δ • ΩC) = permC p (aOct d δ) from rfl, permC_aOct]
  rfl

end CFSG.Monster.B.TwoA
