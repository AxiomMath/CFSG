module

public import CFSG.Monster.Generated.Data
public import CFSG.Monster.B.Cbar.AxisPolynomial

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated Matrix

@[expose] noncomputable def wQ : Q := XQ ⟨ΩC, 0⟩

theorem wQ_eq : wQ = spinEquiv ⟨0, ΩC, 0⟩ := by
  rw [wQ, XQ_eq, thetaD_ΩC]

theorem coe_wQ : (wQ : GL SpinIdx ℚ) = TU ΩC := by
  rw [TU, thetaD_ΩC, DU_zero, mul_one]
  rfl

theorem coe_coe_wQ : ((wQ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = Xmat ⟨ΩC, 0⟩ := rfl

theorem symm_wQ : spinEquiv.symm wQ = ⟨0, ΩC, 0⟩ := by
  rw [wQ_eq, MulEquiv.symm_apply_apply]

theorem two_omega_mem : (fun _ : Fin 24 => (2 : ℤ)) ∈ codeLattice C := by
  have h' := lamCode_mem Ω_mem_C
  rw [lamCode_of_P_zero P_Ω] at h'
  have e : (fun k => 2 * bitLift (Ω k)) = fun _ : Fin 24 => (2 : ℤ) := by
    funext k
    rfl
  rwa [e] at h'

theorem phi_wQ :
    Multiplicative.toAdd (phi (QuotientGroup.mk wQ)) = classOf (fun _ : Fin 24 => (2 : ℤ)) := by
  have h1 : phi (QuotientGroup.mk wQ) = Multiplicative.ofAdd (lamX ΩC) := phi_XQ ⟨ΩC, 0⟩
  have e : (fun k => if P ((ΩC : C) : Fin 24 → ZMod 2) = 0 then
      2 * bitLift (((ΩC : C) : Fin 24 → ZMod 2) k)
      else 2 * (1 - bitLift (((ΩC : C) : Fin 24 → ZMod 2) k))) = fun _ : Fin 24 => (2 : ℤ) := by
    funext k
    rw [ite_eq_left (show P ((ΩC : C) : Fin 24 → ZMod 2) = 0 from P_Ω)]
    rfl
  have h2 : lamX ΩC = classOf (fun _ : Fin 24 => (2 : ℤ)) := by
    rw [lamX_eq, cls_congr _ e, classOf_of_mem' two_omega_mem]
    rfl
  exact (congrArg Multiplicative.toAdd h1).trans h2

theorem symm_conj_wQ (t : Q) : spinEquiv.symm (wQ⁻¹ * t * wQ) =
    ⟨(spinEquiv.symm t).s + pair ΩC (spinEquiv.symm t).δ, (spinEquiv.symm t).a,
      (spinEquiv.symm t).δ⟩ :=
  (symm_conj wQ t).trans (by
    rw [symm_wQ, spinCoord_conj]
    simp only [pair_zero_right, add_zero])

theorem xlift_conj_wQ (t : Q) :
    Xlift (wQ⁻¹ * t * wQ) = sgn (pair ΩC (coordOf t).2) • Xlift t := by
  have hs := symm_conj_wQ t
  have hc : coordOf (wQ⁻¹ * t * wQ) = coordOf t :=
    (congrArg (fun x : SpinCoord => (x.a, x.δ)) hs).trans rfl
  have hcc : centralCoord (wQ⁻¹ * t * wQ) = pair ΩC (coordOf t).2 + centralCoord t :=
    ((congrArg SpinCoord.s hs).trans rfl).trans (add_comm _ _)
  exact Xlift_eq_sgn_smul hc hcc

theorem rhoEquiv_wQ_Xlift (t : Q) :
    rhoEquiv wQ (0, Xlift t, 0) = sgn (pair ΩC (coordOf t).2) • ((0, Xlift t, 0) : SpaceB) := by
  rw [rhoEquiv_Xlift, xlift_conj_wQ, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem E_vecMul_wQ (η : ZMod 2) (c : C₀) :
    E η c ᵥ* ((wQ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = sgn η • E η c := by
  rw [coe_coe_wQ, E_vecMul_Xmat, shift_ΩC, θ_ΩC_left, μ₀_ΩC, mul_one, zero_add, add_zero]
  have hP : P ((ΩC : C) : Fin 24 → ZMod 2) = 0 := P_Ω
  rw [hP, zero_add]

theorem rhoEquiv_wQ_tensorE (s : ℚ) (η : ZMod 2) (c : C₀) (v : Fin 24 → ℚ) :
    rhoEquiv wQ (0, 0, s • tensor (E η c) v) = sgn η • ((0, 0, s • tensor (E η c) v) : SpaceB) := by
  have h : ((0, 0, s • tensor (E η c) v) : SpaceB) = s • ((0, 0, tensor (E η c) v) : SpaceB) := by
    rw [Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]
  rw [h, map_smul, rhoEquiv_tensor, E_vecMul_wQ, smul_comm]
  congr 1
  rw [Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero, tensor, tensor, smul_vecMulVec]

theorem pair_ΩC_mk (x : Fin 24 → ZMod 2) :
    pair ΩC (Submodule.Quotient.mk x) = ∑ i, x i := by
  rw [pair_mk]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (1 : ZMod 2) * x i = x i
  rw [one_mul]

theorem pair_ΩC_deltaPair (i j : Fin 24) : pair ΩC (deltaPair i j) = 0 := by
  rw [deltaPair, pair_ΩC_mk]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  rfl

theorem pair_ΩC_single (i : Fin 24) : pair ΩC (Submodule.Quotient.mk (Pi.single i 1)) = 1 := by
  rw [pair_ΩC_mk, Finset.sum_pi_single']
  simp

theorem pair_ΩC_ind {δ : Finset (Fin 24)} (he : Even δ.card) :
    pair ΩC (Submodule.Quotient.mk (Octad.ind δ)) = 0 := by
  rw [pair_ΩC_mk]
  have h := Octad.sum_ind (d := Finset.univ) (Finset.subset_univ δ)
  rw [h]
  obtain ⟨k, hk⟩ := he
  rw [hk, Nat.cast_add]
  exact CharTwo.add_self_eq_zero _

theorem rhoEquiv_wQ_A (A : symMat) : rhoEquiv wQ (A, 0, 0) = (A, 0, 0) := rhoEquiv_symMat wQ A

theorem rhoEquiv_wQ_tbasis (t : TIdx) : rhoEquiv wQ (tbasis t) = oddSign sgnZ t • tbasis t := by
  rcases t with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o
  · rw [tbasis_diag, rhoEquiv_wQ_A]
    exact (one_smul ℚ _).symm
  · have hm : pair ΩC (coordOf (rMinus p.1.1 p.1.2)).2 = 0 := by
      rw [coordOf_rMinus]
      exact pair_ΩC_deltaPair _ _
    have hp : pair ΩC (coordOf (rPlus p.1.1 p.1.2)).2 = 0 := by
      rw [coordOf_rPlus, pair_add_right, pair_ΩC_thetaD, pair_ΩC_deltaPair, add_zero]
    have hM := rhoEquiv_wQ_Xlift (rMinus p.1.1 p.1.2)
    have hP := rhoEquiv_wQ_Xlift (rPlus p.1.1 p.1.2)
    rw [hm, sgn_zero, one_smul] at hM
    rw [hp, sgn_zero, one_smul] at hP
    have hsplit : ∀ x y : SpaceX, ((0, x - y, 0) : SpaceB) = (0, x, 0) - (0, y, 0) := by
      intro x y
      rw [Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]
    have hsplit' : ∀ x y : SpaceX, ((0, x + y, 0) : SpaceB) = (0, x, 0) + (0, y, 0) := by
      intro x y
      rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]
    fin_cases k
    · show rhoEquiv wQ (tbasis (.inr (.inl (p, 0)))) = (1 : ℚ) • tbasis (.inr (.inl (p, 0)))
      rw [tbasis_pair_zero, rhoEquiv_wQ_A, one_smul]
    · show rhoEquiv wQ (tbasis (.inr (.inl (p, 1)))) = (1 : ℚ) • tbasis (.inr (.inl (p, 1)))
      rw [tbasis_pair_one, hsplit, map_sub, hM, hP, one_smul]
    · show rhoEquiv wQ (tbasis (.inr (.inl (p, 2)))) = (1 : ℚ) • tbasis (.inr (.inl (p, 2)))
      rw [tbasis_pair_two, hsplit', map_add, hM, hP, one_smul]
  · fin_cases k
    · show rhoEquiv wQ (tbasis (.inr (.inr (.inl (c, i, 0))))) =
        (-1 : ℚ) • tbasis (.inr (.inr (.inl (c, i, 0))))
      have h1 : pair ΩC (coordOf (rOdd c i)).2 = 1 := by
        rw [coordOf_rOdd, pair_add_right, pair_ΩC_thetaD, pair_ΩC_single, zero_add]
      rw [tbasis_odd_zero, rhoEquiv_wQ_Xlift, h1, show sgn (1 : ZMod 2) = -1 from rfl]
    · show rhoEquiv wQ (tbasis (.inr (.inr (.inl (c, i, 1))))) =
        (-1 : ℚ) • tbasis (.inr (.inr (.inl (c, i, 1))))
      rw [tbasis_odd_one, rhoEquiv_wQ_tensorE, show sgn (1 : ZMod 2) = -1 from rfl]
    · show rhoEquiv wQ (tbasis (.inr (.inr (.inl (c, i, 2))))) =
        (1 : ℚ) • tbasis (.inr (.inr (.inl (c, i, 2))))
      rw [tbasis_odd_two, rhoEquiv_wQ_tensorE, sgn_zero]
  · have h0 : pair ΩC (coordOf (rOctQ o.1 o.2)).2 = 0 := by
      rw [rOctQ, coordOf_rOct, pair_add_right, pair_ΩC_thetaD,
        pair_ΩC_ind (octRep_spec o.1 o.2).2.1, add_zero]
    rw [tbasis_oct, rhoEquiv_wQ_Xlift, h0, sgn_zero]
    exact (congrArg (· • ((0, Xlift (rOctQ o.1 o.2), 0) : SpaceB))
      (show (1 : ℚ) = oddSign sgnZ (.inr (.inr (.inr o))) from rfl))

theorem rhoEquiv_wQ : rhoEquiv wQ = zB := by
  apply LinearEquiv.toLinearMap_injective
  refine tbasis.ext fun t => ?_
  change rhoEquiv wQ (tbasis t) = zB (tbasis t)
  rw [rhoEquiv_wQ_tbasis, zB_tbasis]

theorem rhoEquiv_zQ_wQ : rhoEquiv (zQ * wQ) = yB := by
  rw [rhoEquiv_mul, rhoEquiv_wQ, rhoEquiv_zQ, zB_mul_xB]

theorem triality_four_group_spin_identification :
    (wQ : GL SpinIdx ℚ) = TU ΩC ∧ wQ = XQ ⟨ΩC, 0⟩ ∧
    (fun _ : Fin 24 => (2 : ℤ)) ∈ CFSG.Monster.codeLattice C ∧
    Multiplicative.toAdd (phi (QuotientGroup.mk wQ)) = classOf (fun _ : Fin 24 => (2 : ℤ)) ∧
    xmatTau2 = rhoEquiv wQ ∧ xmatTau = rhoEquiv (zQ * wQ) ∧
    (∀ g, g ∈ Vmat ↔ g = 1 ∨ g = rhoEquiv zQ ∨ g = rhoEquiv wQ ∨ g = rhoEquiv (zQ * wQ)) ∧
    Vmat ≤ Qmat ∧
    (∃ g ∈ Gmat, g * xmat * g⁻¹ = rhoEquiv wQ) ∧
    (∃ g ∈ Gmat, g * xmat * g⁻¹ = rhoEquiv (zQ * wQ)) ∧
    (∃ g ∈ Gmat, g * rhoEquiv wQ * g⁻¹ = rhoEquiv (zQ * wQ)) := by
  have h2 : xmatTau2 = rhoEquiv wQ := by rw [xmatTau2_eq, rhoEquiv_wQ]
  have h1 : xmatTau = rhoEquiv (zQ * wQ) := by rw [xmatTau_eq, rhoEquiv_zQ_wQ]
  refine ⟨coe_wQ, rfl, two_omega_mem, phi_wQ, h2, h1, fun g => ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_Vmat, h1, h2]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
  · intro g hg
    rcases mem_Vmat.1 hg with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact xmat_mem_Qmat
    · rw [h1]; exact rhoEquiv_mem_rhoQ _
    · rw [h2]; exact rhoEquiv_mem_rhoQ _
  · exact ⟨tauB ^ 2, pow_mem tauB_mem_Gmat 2, h2⟩
  · exact ⟨tauB, tauB_mem_Gmat, h1⟩
  · refine ⟨tauB * tauB, mul_mem tauB_mem_Gmat tauB_mem_Gmat, ?_⟩
    calc tauB * tauB * rhoEquiv wQ * (tauB * tauB)⁻¹ = tauB * tauB * zB * (tauB * tauB)⁻¹ := by
          rw [rhoEquiv_wQ]
      _ = yB := by
          rw [← conj_tauB_xB, ← conj_tauB_zB]
          group
      _ = rhoEquiv (zQ * wQ) := rhoEquiv_zQ_wQ.symm

end CFSG.Monster.B
