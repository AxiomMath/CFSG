module

public import CFSG.Monster.Generated.Data

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Generated

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible Matrix

@[expose] noncomputable def hCocode (δ : Cocode) : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv (DQ δ)

namespace OddCocode

private theorem sgn_one' : sgn 1 = -1 := rfl

theorem spinCoord_conj (δ : Cocode) (y : SpinCoord) :
    (⟨0, 0, δ⟩ : SpinCoord)⁻¹ * y * ⟨0, 0, δ⟩ = ⟨pair y.a δ, 0, 0⟩ * y := by
  ext
  · simp only [SpinCoord.mul_s, SpinCoord.inv_s, SpinCoord.inv_δ, SpinCoord.mul_δ,
      pair_zero_left, pair_zero_right]
    ring
  · simp only [SpinCoord.mul_a, SpinCoord.inv_a, add_zero, zero_add]
  · simp only [SpinCoord.mul_δ, SpinCoord.inv_δ, zero_add]
    rw [add_comm δ y.δ, add_assoc, add_self_cocode, add_zero]

theorem symm_conj_DQ (δ : Cocode) (t : Q) :
    spinEquiv.symm ((DQ δ)⁻¹ * t * DQ δ) = ⟨pair (coordOf t).1 δ, 0, 0⟩ * spinEquiv.symm t := by
  have hD : spinEquiv.symm (DQ δ) = ⟨0, 0, δ⟩ := by
    rw [DQ_eq]
    exact spinEquiv.symm_apply_apply _
  rw [map_mul, map_mul, map_inv, hD]
  exact spinCoord_conj δ (spinEquiv.symm t)

private theorem coord_of_symm_eq {r r' : Q} {e : ZMod 2}
    (h : spinEquiv.symm r' = ⟨e, 0, 0⟩ * spinEquiv.symm r) :
    coordOf r' = coordOf r ∧ centralCoord r' = e + centralCoord r := by
  unfold coordOf centralCoord
  rw [h]
  simp

theorem Xlift_conj_DQ (δ : Cocode) (t : Q) :
    Xlift ((DQ δ)⁻¹ * t * DQ δ) = sgn (pair (coordOf t).1 δ) • Xlift t :=
  have h := coord_of_symm_eq (symm_conj_DQ δ t)
  Xlift_eq_sgn_smul h.1 h.2

theorem hCocode_Xlift (δ : Cocode) (t : Q) :
    hCocode δ (0, Xlift t, 0) =
      sgn (pair (coordOf t).1 δ) • ((0 : symMat), Xlift t, (0 : SpaceW)) := by
  rw [hCocode, rhoEquiv_Xlift, Xlift_conj_DQ, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem hCocode_tensor_E (δ : Cocode) (η : ZMod 2) (c : C₀) (v : Fin 24 → ℚ) :
    hCocode δ (0, 0, tensor (E η c) v) =
      sgn (pair (c : C) δ) • ((0 : symMat), (0 : SpaceX), tensor (E (η + pair ΩC δ) c) v) := by
  have h : E η c ᵥ* (((DQ δ : Q) : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (pair (c : C) δ) • E (η + pair ΩC δ) c := E_vecMul_Dmat δ η c
  rw [hCocode, rhoEquiv_tensor, h, tensor, tensor, smul_vecMulVec, Prod.smul_mk, Prod.smul_mk,
    smul_zero, smul_zero]

theorem mk_zero_zero_smul (s : ℚ) (N : SpaceW) :
    ((0 : symMat), (0 : SpaceX), s • N) = s • ((0 : symMat), (0 : SpaceX), N) := by
  rw [Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

variable {δ : Cocode}

theorem hCocode_diag (δ : Cocode) (i : Fin 24) :
    hCocode δ (tbasis (.inl i)) = tbasis (.inl i) := by
  rw [tbasis_diag]
  exact rhoEquiv_symMat _ _

theorem pair_coordOf_rMinus (δ : Cocode) (i j : Fin 24) :
    pair (coordOf (rMinus i j)).1 δ = 0 := by
  rw [coordOf_rMinus]
  exact pair_zero_left δ

theorem pair_coordOf_rPlus (δ : Cocode) (i j : Fin 24) :
    pair (coordOf (rPlus i j)).1 δ = pair ΩC δ := by
  rw [coordOf_rPlus]

theorem hCocode_Xlift_rMinus (δ : Cocode) (i j : Fin 24) :
    hCocode δ (0, Xlift (rMinus i j), 0) = ((0 : symMat), Xlift (rMinus i j), (0 : SpaceW)) := by
  rw [hCocode_Xlift, pair_coordOf_rMinus, sgn_zero, one_smul]

theorem hCocode_Xlift_rPlus (hδ : pair ΩC δ = 1) (i j : Fin 24) :
    hCocode δ (0, Xlift (rPlus i j), 0) = -((0 : symMat), Xlift (rPlus i j), (0 : SpaceW)) := by
  rw [hCocode_Xlift, pair_coordOf_rPlus, hδ, sgn_one']
  exact neg_one_smul ℚ ((0 : symMat), Xlift (rPlus i j), (0 : SpaceW))

theorem tbasis_pair_one' (p : LtPair) :
    tbasis (.inr (.inl (p, 1))) =
      ((0 : symMat), Xlift (rMinus p.1.1 p.1.2), (0 : SpaceW)) -
        ((0 : symMat), Xlift (rPlus p.1.1 p.1.2), (0 : SpaceW)) := by
  rw [tbasis_pair_one, Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]

theorem tbasis_pair_two' (p : LtPair) :
    tbasis (.inr (.inl (p, 2))) =
      ((0 : symMat), Xlift (rMinus p.1.1 p.1.2), (0 : SpaceW)) +
        ((0 : symMat), Xlift (rPlus p.1.1 p.1.2), (0 : SpaceW)) := by
  rw [tbasis_pair_two, Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]

theorem hCocode_pair_zero (δ : Cocode) (p : LtPair) :
    hCocode δ (tbasis (.inr (.inl (p, 0)))) = tbasis (.inr (.inl (p, 0))) := by
  rw [tbasis_pair_zero]
  exact rhoEquiv_symMat _ _

theorem hCocode_pair_one (hδ : pair ΩC δ = 1) (p : LtPair) :
    hCocode δ (tbasis (.inr (.inl (p, 1)))) = tbasis (.inr (.inl (p, 2))) := by
  rw [tbasis_pair_one', tbasis_pair_two', map_sub, hCocode_Xlift_rMinus, hCocode_Xlift_rPlus hδ,
    sub_neg_eq_add]

theorem hCocode_pair_two (hδ : pair ΩC δ = 1) (p : LtPair) :
    hCocode δ (tbasis (.inr (.inl (p, 2)))) = tbasis (.inr (.inl (p, 1))) := by
  rw [tbasis_pair_one', tbasis_pair_two', map_add, hCocode_Xlift_rMinus, hCocode_Xlift_rPlus hδ,
    ← sub_eq_add_neg]

theorem hCocode_pair (hδ : pair ΩC δ = 1) (p : LtPair) (k : Fin 3) :
    hCocode δ (tbasis (.inr (.inl (p, k)))) = tbasis (.inr (.inl (p, -k))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · exact hCocode_pair_zero δ p
  · exact hCocode_pair_one hδ p
  · exact hCocode_pair_two hδ p

@[expose] noncomputable def oddEps (δ : Cocode) (c : C₀) (i : Fin 24) : ℚ :=
  sgn (pair (c : C) δ + mOdd c i)

theorem pair_aOdd (hδ : pair ΩC δ = 1) (c : C₀) (i : Fin 24) :
    pair (aOdd c i) δ = pair (c : C) δ + mOdd c i := by
  rw [aOdd, pair_add_left, pair_smul_left, hδ, mul_one]

theorem sgn_pair_coordOf_rOdd (hδ : pair ΩC δ = 1) (c : C₀) (i : Fin 24) :
    sgn (pair (coordOf (rOdd c i)).1 δ) = oddEps δ c i := by
  rw [coordOf_rOdd]
  exact congrArg sgn (pair_aOdd hδ c i)

theorem hCocode_odd_zero (hδ : pair ΩC δ = 1) (c : C₀) (i : Fin 24) :
    hCocode δ (tbasis (.inr (.inr (.inl (c, i, 0))))) =
      oddEps δ c i • tbasis (.inr (.inr (.inl (c, i, 0)))) := by
  rw [tbasis_odd_zero, hCocode_Xlift, sgn_pair_coordOf_rOdd hδ]

theorem oddEps_one (c : C₀) (i : Fin 24) :
    sgn (((c : C) : Fin 24 → ZMod 2) i) * sgn (pair (c : C) δ) =
      oddEps δ c i * sgn (P ((c : C) : Fin 24 → ZMod 2)) := by
  rw [oddEps, mOdd, sgn_add, sgn_add, mul_assoc, mul_assoc,
    sgn_mul_self (P ((c : C) : Fin 24 → ZMod 2)), mul_one, mul_comm]

theorem oddEps_two (c : C₀) (i : Fin 24) :
    sgn (P ((c : C) : Fin 24 → ZMod 2)) * sgn (pair (c : C) δ) =
      oddEps δ c i * sgn (((c : C) : Fin 24 → ZMod 2) i) := by
  rw [oddEps, mOdd, sgn_add, sgn_add, mul_assoc, mul_comm (sgn (((c : C) : Fin 24 → ZMod 2) i)),
    mul_assoc, sgn_mul_self (((c : C) : Fin 24 → ZMod 2) i), mul_one, mul_comm]

theorem hCocode_odd_one (hδ : pair ΩC δ = 1) (c : C₀) (i : Fin 24) :
    hCocode δ (tbasis (.inr (.inr (.inl (c, i, 1))))) =
      oddEps δ c i • tbasis (.inr (.inr (.inl (c, i, 2)))) := by
  rw [tbasis_odd_one, tbasis_odd_two, mk_zero_zero_smul, mk_zero_zero_smul, map_smul,
    hCocode_tensor_E, hδ, smul_smul, smul_smul, show (1 : ZMod 2) + 1 = 0 from rfl]
  exact congrArg (· • _) (oddEps_one c i)

theorem hCocode_odd_two (hδ : pair ΩC δ = 1) (c : C₀) (i : Fin 24) :
    hCocode δ (tbasis (.inr (.inr (.inl (c, i, 2))))) =
      oddEps δ c i • tbasis (.inr (.inr (.inl (c, i, 1)))) := by
  rw [tbasis_odd_one, tbasis_odd_two, mk_zero_zero_smul, mk_zero_zero_smul, map_smul,
    hCocode_tensor_E, hδ, smul_smul, smul_smul, zero_add]
  exact congrArg (· • _) (oddEps_two c i)

theorem hCocode_odd (hδ : pair ΩC δ = 1) (c : C₀) (i : Fin 24) (k : Fin 3) :
    hCocode δ (tbasis (.inr (.inr (.inl (c, i, k))))) =
      oddEps δ c i • tbasis (.inr (.inr (.inl (c, i, -k)))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · exact hCocode_odd_zero hδ c i
  · exact hCocode_odd_one hδ c i
  · exact hCocode_odd_two hδ c i

theorem pair_aOct (hδ : pair ΩC δ = 1) (d : C) (ε : Finset (Fin 24)) :
    pair (aOct d ε) δ = pair d δ + nOct ε := by
  rw [aOct, pair_add_left, pair_smul_left, hδ, mul_one]

theorem quadForm_eq_nOct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    Octad.quadForm (octSupp d) v = nOct (octRep d v) := by
  obtain ⟨h1, h2, h3⟩ := octRep_spec d v
  have h4 : 4 ∣ (octSupp d).card := by rw [card_octSupp]; norm_num
  calc Octad.quadForm (octSupp d) v =
        Octad.quadForm (octSupp d) (Octad.cls (octSupp d) (octRep d v)) := by rw [h3]
    _ = nOct (octRep d v) := Octad.quadForm_cls h4 h1 h2

theorem sgn_pair_coordOf_rOctQ (hδ : pair ΩC δ = 1) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    sgn (pair (coordOf (rOctQ d v)).1 δ) =
      sgn (pair (d : C) δ) * sgn (Octad.quadForm (octSupp d) v) := by
  have h : (coordOf (rOctQ d v)).1 = aOct (d : C) (octRep d v) := by
    rw [rOctQ, coordOf_rOct]
  rw [h, pair_aOct hδ, sgn_add, quadForm_eq_nOct]

theorem hCocode_oct (hδ : pair ΩC δ = 1) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    hCocode δ (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      (sgn (pair (d : C) δ) * sgn (Octad.quadForm (octSupp d) v)) •
        tbasis (.inr (.inr (.inr ⟨d, v⟩))) := by
  rw [tbasis_oct, hCocode_Xlift]
  exact congrArg (· • _) (sgn_pair_coordOf_rOctQ hδ d v)

theorem tauB_symm_diag (i : Fin 24) : tauB.symm (tbasis (.inl i)) = tbasis (.inl i) := by
  rw [LinearEquiv.symm_apply_eq, tauB_diag]

theorem tauB_symm_pair (p : LtPair) (k : Fin 3) :
    tauB.symm (tbasis (.inr (.inl (p, k)))) = tbasis (.inr (.inl (p, k - 1))) := by
  rw [LinearEquiv.symm_apply_eq, tauB_pair, sub_add_cancel]

theorem tauB_symm_odd (c : C₀) (i : Fin 24) (k : Fin 3) :
    tauB.symm (tbasis (.inr (.inr (.inl (c, i, k))))) =
      tbasis (.inr (.inr (.inl (c, i, k - 1)))) := by
  rw [LinearEquiv.symm_apply_eq, tauB_odd, sub_add_cancel]

theorem tauMat_apply_oct_of_notMem (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) (y : TIdx)
    (hy : y ∉ Set.range fun w : Octad.EvenQuot (octSupp d) => (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) :
    tauMat y (.inr (.inr (.inr ⟨d, v⟩))) = 0 := by
  rcases y with j | q | q | ⟨d', w⟩
  · rfl
  · rfl
  · rfl
  · have hd : d' ≠ d := by
      rintro rfl
      exact hy ⟨w, rfl⟩
    simp only [tauMat, diag2_apply_inr_inr, octBlock]
    exact blockDiagonal'_apply_ne _ _ _ hd

theorem tauB_symm_oct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tauB.symm (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      ∑ w, octHD d w v • tbasis (.inr (.inr (.inr ⟨d, w⟩))) := by
  rw [tauB_symm_apply, toLin_self]
  refine (Fintype.sum_of_injective (fun w : Octad.EvenQuot (octSupp d) =>
    (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) ?_ _ _ ?_ ?_).symm
  · intro w w' h
    simpa using h
  · intro y hy
    rw [tauMat_apply_oct_of_notMem d v y hy, zero_smul]
  · intro w
    rw [tauMat_oct_apply_oct]

theorem octHD_apply (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    octHD d v w = ((2 : ℚ) ^ 3)⁻¹ *
      sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v w) *
        sgn (Octad.quadForm (octSupp d) w) := by
  rw [octHD, octD, signMatrix, mul_diagonal, octH, fourierMatrix]

theorem octHD_mul_sgn (d : OctadWord) (s : ℚ) (v w : Octad.EvenQuot (octSupp d)) :
    octHD d v w * (s * sgn (Octad.quadForm (octSupp d) w)) =
      s * sgn (Octad.quadForm (octSupp d) v) * octHD d w v := by
  rw [octHD_apply, octHD_apply, polarBilin_symm (Octad.quadForm (octSupp d)) w v]
  have hv := sgn_mul_self (Octad.quadForm (octSupp d) v)
  have hw := sgn_mul_self (Octad.quadForm (octSupp d) w)
  linear_combination (((2 : ℚ) ^ 3)⁻¹ *
      sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v w) * s) * hw -
    (((2 : ℚ) ^ 3)⁻¹ * sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v w) * s) * hv

theorem hCocode_tauB_tbasis (hδ : pair ΩC δ = 1) (x : TIdx) :
    hCocode δ (tauB (tbasis x)) = tauB.symm (hCocode δ (tbasis x)) := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | ⟨d, v⟩
  · rw [tauB_diag, hCocode_diag, tauB_symm_diag]
  · rw [tauB_pair, hCocode_pair hδ, hCocode_pair hδ, tauB_symm_pair, neg_add']
  · rw [tauB_odd, hCocode_odd hδ, hCocode_odd hδ, map_smul, tauB_symm_odd, neg_add']
  · rw [tauB_oct, hCocode_oct hδ, map_smul, tauB_symm_oct, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, hCocode_oct hδ, smul_smul, smul_smul, octHD_mul_sgn]

theorem hCocode_mul_tauB (hδ : pair ΩC δ = 1) : hCocode δ * tauB = tauB⁻¹ * hCocode δ :=
  tbasis.ext' fun x => hCocode_tauB_tbasis hδ x

theorem DQ_mul_self (δ : Cocode) : DQ δ * DQ δ = 1 := by
  have h : (⟨0, 0, δ⟩ : SpinCoord) * ⟨0, 0, δ⟩ = 1 := by
    ext
    · simp
    · simp
    · simp [add_self_cocode]
  rw [DQ_eq, ← map_mul, h, map_one]

theorem rhoEquiv_one : rhoEquiv 1 = 1 :=
  (congrArg thetaEquiv (map_one rhoPair)).trans thetaEquiv_one

theorem hCocode_mul_self (δ : Cocode) : hCocode δ * hCocode δ = 1 := by
  rw [hCocode, ← rhoEquiv_mul, DQ_mul_self, rhoEquiv_one]

theorem hCocode_mul_tauB_mul (hδ : pair ΩC δ = 1) : hCocode δ * tauB * hCocode δ = tauB⁻¹ := by
  rw [hCocode_mul_tauB hδ, mul_assoc, hCocode_mul_self, mul_one]

theorem tauB_inv_eq_sq : tauB⁻¹ = tauB ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact tauB_pow_three)

theorem tauB_inv_mul_tauB_inv : tauB⁻¹ * tauB⁻¹ = tauB := by
  rw [tauB_inv_eq_sq, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, tauB_pow_three, one_mul]

theorem hCocode_mul_conj (hδ : pair ΩC δ = 1) :
    hCocode δ * (tauB * hCocode δ * tauB⁻¹) = tauB := by
  rw [← mul_assoc, ← mul_assoc, hCocode_mul_tauB_mul hδ, tauB_inv_mul_tauB_inv]

theorem tauB_inv_mul_hCocode (hδ : pair ΩC δ = 1) :
    tauB⁻¹ * hCocode δ * tauB * hCocode δ = tauB := by
  rw [mul_assoc, mul_assoc, ← mul_assoc (hCocode δ), hCocode_mul_tauB_mul hδ,
    tauB_inv_mul_tauB_inv]

theorem hCocode_mem_Hmat (δ : Cocode) : hCocode δ ∈ Hmat := rhoEquiv_mem_Gvis _

theorem hCocode_mem_Gmat (δ : Cocode) : hCocode δ ∈ Gmat := Hmat_le_Gmat (hCocode_mem_Hmat δ)

end OddCocode

open OddCocode

theorem odd_cocode_inverts_triality :
    (∀ δ : Cocode, pair ΩC δ = 1 →
      rhoEquiv (DQ δ) ∈ Hmat ∧
      rhoEquiv (DQ δ) * rhoEquiv (DQ δ) = 1 ∧
      rhoEquiv (DQ δ) * tauB * rhoEquiv (DQ δ) = tauB⁻¹ ∧
      rhoEquiv (DQ δ) * (tauB * rhoEquiv (DQ δ) * tauB⁻¹) = tauB ∧
      tauB⁻¹ * rhoEquiv (DQ δ) * tauB * rhoEquiv (DQ δ) = tauB) ∧
    pair ΩC (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2))) = 1 ∧
    rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)))) ∈ Hmat ∧
    rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)))) *
        (tauB * rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)))) *
          tauB⁻¹) = tauB ∧
    tauB⁻¹ * rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)))) * tauB *
        rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)))) = tauB :=
  ⟨fun δ hδ => ⟨hCocode_mem_Hmat δ, hCocode_mul_self δ, hCocode_mul_tauB_mul hδ,
    hCocode_mul_conj hδ, tauB_inv_mul_hCocode hδ⟩, pair_ΩC_mk_single, hCocode_mem_Hmat _,
    hCocode_mul_conj pair_ΩC_mk_single, tauB_inv_mul_hCocode pair_ΩC_mk_single⟩

end CFSG.Monster.Generated
