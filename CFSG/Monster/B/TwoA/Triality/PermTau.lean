module

public import CFSG.Monster.B.TwoA.Triality.PermLift

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.ScalarKernel
  CFSG.Monster.B.Short CFSG.Monster.B Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem gLift_apply (p : AutPerm) (x : SpaceB) : gLift p x = theta (gPair p) x := by
  rw [gLift_eq]
  rfl

theorem theta_gPair_A (p : AutPerm) (A : symMat) :
    theta (gPair p) (A, 0, 0) = (thetaA (Pmat p) A, 0, 0) := by
  rw [theta_symMat, mat_gPair_snd]

theorem theta_gPair_X (p : AutPerm) (r : Q) :
    theta (gPair p) ((0 : symMat), Xlift r, (0 : SpaceW)) =
      ((0 : symMat), Xlift (conjQ (gPair p) r), (0 : SpaceW)) :=
  theta_Xlift _ r

theorem mk_zero_X_sub (x y : SpaceX) :
    ((0 : symMat), x - y, (0 : SpaceW)) =
      ((0 : symMat), x, (0 : SpaceW)) - ((0 : symMat), y, (0 : SpaceW)) := by
  ext <;> simp

theorem mk_zero_X_add (x y : SpaceX) :
    ((0 : symMat), x + y, (0 : SpaceW)) =
      ((0 : symMat), x, (0 : SpaceW)) + ((0 : symMat), y, (0 : SpaceW)) := by
  ext <;> simp

theorem theta_gPair_X_sub (p : AutPerm) (r r' : Q) :
    theta (gPair p) ((0 : symMat), Xlift r - Xlift r', (0 : SpaceW)) =
      ((0 : symMat), Xlift (conjQ (gPair p) r) - Xlift (conjQ (gPair p) r'), (0 : SpaceW)) :=
  (congrArg (theta (gPair p)) (mk_zero_X_sub (Xlift r) (Xlift r'))).trans
    (((theta (gPair p)).map_sub _ _).trans
      ((congrArg₂ (· - ·) (theta_gPair_X p r) (theta_gPair_X p r')).trans
        (mk_zero_X_sub _ _).symm))

theorem theta_gPair_X_add (p : AutPerm) (r r' : Q) :
    theta (gPair p) ((0 : symMat), Xlift r + Xlift r', (0 : SpaceW)) =
      ((0 : symMat), Xlift (conjQ (gPair p) r) + Xlift (conjQ (gPair p) r'), (0 : SpaceW)) :=
  (congrArg (theta (gPair p)) (mk_zero_X_add (Xlift r) (Xlift r'))).trans
    (((theta (gPair p)).map_add _ _).trans
      ((congrArg₂ (· + ·) (theta_gPair_X p r) (theta_gPair_X p r')).trans
        (mk_zero_X_add _ _).symm))

theorem theta_gPair_W (p : AutPerm) (s : ℚ) (u : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    theta (gPair p) ((0 : symMat), (0 : SpaceX), s • tensor u v) =
      ((0 : symMat), (0 : SpaceX), s • tensor (u ᵥ* gSpin p) (v ᵥ* Pmat p)) := by
  rw [Generated.OddCocode.mk_zero_zero_smul, map_smul, theta_tensor, coe_gPair_fst,
    mat_gPair_snd, Generated.OddCocode.mk_zero_zero_smul]

theorem sym2_inv_eq_iff (p : Equiv.Perm (Fin 24)) (k l : Fin 24) (z : PairIdx) :
    s(p⁻¹ k, p⁻¹ l) = z ↔ s(k, l) = z.map p := by
  constructor
  · rintro rfl
    rw [Sym2.map_mk]
    simp
  · intro h
    have e : z = Sym2.map (⇑p⁻¹) (Sym2.map p z) := by
      rw [Sym2.map_map]
      have : (⇑p⁻¹ ∘ ⇑p) = id := funext fun x => by simp
      rw [this, Sym2.map_id]
      rfl
    rw [e, ← h, Sym2.map_mk]

theorem thetaA_Pmat_basisA (p : Equiv.Perm (Fin 24)) (z : PairIdx) :
    thetaA (Pmat p) (basisA z) = basisA (z.map p) := by
  apply Subtype.ext
  rw [coe_thetaA, Pmat_transpose]
  ext k l
  rw [Pmat, Pmat, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, submatrix_apply, basisA_apply, basisA_apply]
  have e : (Equiv.symm p) l = p⁻¹ l := rfl
  simp only [id, e]
  exact if_congr (sym2_inv_eq_iff p k l z) rfl rfl

theorem gLift_diag (p : AutPerm) (i : Fin 24) :
    gLift p (tbasis (.inl i)) = tbasis (.inl ((p : Equiv.Perm (Fin 24)) i)) := by
  rw [gLift_apply, tbasis_diag, theta_gPair_A, thetaA_Pmat_basisA, Sym2.map_mk, tbasis_diag]

@[expose] def pairMap (p : AutPerm) (P : LtPair) : LtPair :=
  if h : (p : Equiv.Perm (Fin 24)) P.1.1 < (p : Equiv.Perm (Fin 24)) P.1.2 then
    ⟨((p : Equiv.Perm (Fin 24)) P.1.1, (p : Equiv.Perm (Fin 24)) P.1.2), h⟩
  else ⟨((p : Equiv.Perm (Fin 24)) P.1.2, (p : Equiv.Perm (Fin 24)) P.1.1),
    lt_of_le_of_ne (not_lt.1 h) ((p : Equiv.Perm (Fin 24)).injective.ne P.2.ne')⟩

theorem pairMap_cases (p : AutPerm) (P : LtPair) :
    ((pairMap p P).1.1 = (p : Equiv.Perm (Fin 24)) P.1.1 ∧
        (pairMap p P).1.2 = (p : Equiv.Perm (Fin 24)) P.1.2) ∨
      ((pairMap p P).1.1 = (p : Equiv.Perm (Fin 24)) P.1.2 ∧
        (pairMap p P).1.2 = (p : Equiv.Perm (Fin 24)) P.1.1) := by
  unfold pairMap
  split_ifs
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem rMinus_comm (i j : Fin 24) : rMinus i j = rMinus j i := by
  rw [rMinus, rMinus, deltaPair_comm]

theorem rPlus_comm (i j : Fin 24) : rPlus i j = rPlus j i := by
  rw [rPlus, rPlus, deltaPair_comm]

theorem sym2_pairMap (p : AutPerm) (P : LtPair) :
    s((pairMap p P).1.1, (pairMap p P).1.2) =
      s((p : Equiv.Perm (Fin 24)) P.1.1, (p : Equiv.Perm (Fin 24)) P.1.2) := by
  rcases pairMap_cases p P with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Sym2.eq_swap]

theorem rMinus_pairMap (p : AutPerm) (P : LtPair) :
    rMinus (pairMap p P).1.1 (pairMap p P).1.2 =
      rMinus ((p : Equiv.Perm (Fin 24)) P.1.1) ((p : Equiv.Perm (Fin 24)) P.1.2) := by
  rcases pairMap_cases p P with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, rMinus_comm]

theorem rPlus_pairMap (p : AutPerm) (P : LtPair) :
    rPlus (pairMap p P).1.1 (pairMap p P).1.2 =
      rPlus ((p : Equiv.Perm (Fin 24)) P.1.1) ((p : Equiv.Perm (Fin 24)) P.1.2) := by
  rcases pairMap_cases p P with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, rPlus_comm]

theorem gLift_pair (p : AutPerm) (P : LtPair) (k : Fin 3) :
    gLift p (tbasis (.inr (.inl (P, k)))) = tbasis (.inr (.inl (pairMap p P, k))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [gLift_apply, tbasis_pair_zero P, theta_gPair_A p, thetaA_Pmat_basisA, Sym2.map_mk,
      tbasis_pair_zero (pairMap p P), sym2_pairMap]
  · rw [gLift_apply, tbasis_pair_one P, theta_gPair_X_sub p, Xlift_conj_rMinus p,
      Xlift_conj_rPlus p, tbasis_pair_one (pairMap p P), rMinus_pairMap p P, rPlus_pairMap p P]
  · rw [gLift_apply, tbasis_pair_two P, theta_gPair_X_add p, Xlift_conj_rMinus p,
      Xlift_conj_rPlus p, tbasis_pair_two (pairMap p P), rMinus_pairMap p P, rPlus_pairMap p P]

theorem tensor_smul_left' (x : ℚ) (u : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    tensor (x • u) v = x • tensor u v := smul_vecMulVec x u v

theorem coe_π₀_permC_apply (p : AutPerm) (c : C₀) (i : Fin 24) :
    ((π₀ (permC p c) : C) : Fin 24 → ZMod 2) ((p : Equiv.Perm (Fin 24)) i) =
      ((c : C) : Fin 24 → ZMod 2) i + μ₀ (permC p c) := by
  rw [coe_π₀, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, coe_ΩC,
    permC_coe_apply, show (Ω : Fin 24 → ZMod 2) _ = 1 from rfl, smul_eq_mul, mul_one]

theorem P_π₀_permC (p : AutPerm) (c : C₀) :
    P ((π₀ (permC p c) : C) : Fin 24 → ZMod 2) = P ((c : C) : Fin 24 → ZMod 2) := by
  rw [coe_π₀, Submodule.coe_add, Submodule.coe_smul, coe_ΩC, P_add_smul_Ω (permC p c).2,
    coe_permC, P_permWord]

theorem sgn_odd_one (p : AutPerm) (c : C₀) (i : Fin 24) :
    sgn (((c : C) : Fin 24 → ZMod 2) i) * sgn (gammaP p c + 1 * μ₀ (permC p c)) =
      sgn (gammaP p c) * sgn (((π₀ (permC p c) : C) : Fin 24 → ZMod 2)
        ((p : Equiv.Perm (Fin 24)) i)) := by
  rw [coe_π₀_permC_apply, one_mul, sgn_add, sgn_add]
  ring

theorem sgn_odd_two (p : AutPerm) (c : C₀) :
    sgn (P ((c : C) : Fin 24 → ZMod 2)) * sgn (gammaP p c + 0 * μ₀ (permC p c)) =
      sgn (gammaP p c) * sgn (P ((π₀ (permC p c) : C) : Fin 24 → ZMod 2)) := by
  rw [P_π₀_permC, zero_mul, add_zero]
  ring

theorem gLift_odd (p : AutPerm) (c : C₀) (i : Fin 24) (k : Fin 3) :
    gLift p (tbasis (.inr (.inr (.inl (c, i, k))))) = sgn (gammaP p c) •
      tbasis (.inr (.inr (.inl (π₀ (permC p c), (p : Equiv.Perm (Fin 24)) i, k)))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [gLift_apply, tbasis_odd_zero c i, theta_gPair_X p, Xlift_conj_rOdd p c i,
      mk_zero_X_smul', tbasis_odd_zero (π₀ (permC p c)) ((p : Equiv.Perm (Fin 24)) i)]
  · rw [gLift_apply, tbasis_odd_one c i, theta_gPair_W p, E_vecMul_gSpin p 1 c,
      single_vecMul_Pmat, tensor_smul_left', smul_smul,
      tbasis_odd_one (π₀ (permC p c)) ((p : Equiv.Perm (Fin 24)) i),
      Generated.OddCocode.mk_zero_zero_smul, Generated.OddCocode.mk_zero_zero_smul, smul_smul,
      sgn_odd_one p c i]
  · rw [gLift_apply, tbasis_odd_two c i, theta_gPair_W p, E_vecMul_gSpin p 0 c,
      single_vecMul_Pmat, tensor_smul_left', smul_smul,
      tbasis_odd_two (π₀ (permC p c)) ((p : Equiv.Perm (Fin 24)) i),
      Generated.OddCocode.mk_zero_zero_smul, Generated.OddCocode.mk_zero_zero_smul, smul_smul,
      sgn_odd_two p c]

@[expose] def octMap (p : AutPerm) (d : OctadWord) : OctadWord :=
  ⟨permC p d, by rw [coe_permC, hammingNorm_permWord]; exact d.2⟩

theorem supp_permWord (p : AutPerm) (x : Fin 24 → ZMod 2) :
    supp (permWord p x) = mapSet p (supp x) := by
  ext k
  rw [mapSet, Finset.mem_map_equiv, mem_supp_iff, mem_supp_iff, permWord_apply']
  rfl

theorem octSupp_octMap (p : AutPerm) (d : OctadWord) :
    octSupp (octMap p d) = mapSet p (octSupp d) := by
  change supp ((permC p (d : C) : C) : Fin 24 → ZMod 2) = _
  rw [coe_permC, supp_permWord]

theorem mapSet_subset_octSupp (p : AutPerm) (d : OctadWord) {δ : Finset (Fin 24)}
    (h : δ ⊆ octSupp d) : mapSet p δ ⊆ octSupp (octMap p d) := by
  rw [octSupp_octMap]
  exact Finset.map_subset_map.2 h

theorem even_card_mapSet (p : AutPerm) {δ : Finset (Fin 24)} (h : Even δ.card) :
    Even (mapSet p δ).card := by
  rw [card_mapSet]
  exact h

@[expose] def octQMap (p : AutPerm) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    Octad.EvenQuot (octSupp (octMap p d)) :=
  Octad.cls (octSupp (octMap p d)) (mapSet p (octRep d v))

theorem tbasis_octQMap (p : AutPerm) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tbasis (.inr (.inr (.inr ⟨octMap p d, octQMap p d v⟩))) =
      ((0 : symMat), Xlift (rOct (permC p d) (mapSet p (octRep d v))), (0 : SpaceW)) :=
  tbasis_oct_cls (mapSet_subset_octSupp p d (octRep_spec d v).1)
    (even_card_mapSet p (octRep_spec d v).2.1)

theorem gLift_oct (p : AutPerm) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    gLift p (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      sgn (gammaP p d) • tbasis (.inr (.inr (.inr ⟨octMap p d, octQMap p d v⟩))) := by
  rw [gLift_apply, tbasis_oct, theta_gPair_X]
  change ((0 : symMat), Xlift (conjQ (gPair p) (rOct (d : C) (octRep d v))), (0 : SpaceW)) = _
  rw [Xlift_conj_rOct, mk_zero_X_smul', tbasis_octQMap]

theorem mapSet_inter (p : AutPerm) (δ ε : Finset (Fin 24)) :
    mapSet p δ ∩ mapSet p ε = mapSet p (δ ∩ ε) := (Finset.map_inter _ _).symm

theorem four_dvd_octSupp (d : OctadWord) : 4 ∣ (octSupp d).card := by
  rw [card_octSupp]
  norm_num

theorem octHD_octQMap (p : AutPerm) (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    octHD (octMap p d) (octQMap p d v) (octQMap p d w) = octHD d v w := by
  obtain ⟨hv1, hv2, hv3⟩ := octRep_spec d v
  obtain ⟨hw1, hw2, hw3⟩ := octRep_spec d w
  have e1 : octHD d v w = octHD d (Octad.cls (octSupp d) (octRep d v))
      (Octad.cls (octSupp d) (octRep d w)) := by rw [hv3, hw3]
  rw [e1, octHD_cls d hv1 hv2 hw1 hw2, octQMap, octQMap,
    octHD_cls (octMap p d) (mapSet_subset_octSupp p d hv1) (even_card_mapSet p hv2)
      (mapSet_subset_octSupp p d hw1) (even_card_mapSet p hw2), mapSet_inter, card_mapSet,
    card_mapSet]

theorem octQMap_injective (p : AutPerm) (d : OctadWord) : Function.Injective (octQMap p d) := by
  intro v w h
  obtain ⟨hv1, hv2, hv3⟩ := octRep_spec d v
  obtain ⟨hw1, hw2, hw3⟩ := octRep_spec d w
  rw [octQMap, octQMap, Octad.cls_eq_cls_iff (mapSet_subset_octSupp p d hv1)
    (even_card_mapSet p hv2) (mapSet_subset_octSupp p d hw1) (even_card_mapSet p hw2)] at h
  rcases h with h | h
  · rw [mapSet, mapSet, Finset.map_inj] at h
    rw [← hv3, ← hw3, h]
  · rw [octSupp_octMap, mapSet, mapSet, mapSet, ← Finset.map_sdiff, Finset.map_inj] at h
    rw [← hv3, ← hw3, h, Octad.cls_compl (by rw [card_octSupp]; decide) hv1 hv2]

theorem octQMap_bijective (p : AutPerm) (d : OctadWord) : Function.Bijective (octQMap p d) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨octQMap_injective p d, by rw [card_evenQuot_octSupp, card_evenQuot_octSupp]⟩

end CFSG.Monster.B.TwoA
