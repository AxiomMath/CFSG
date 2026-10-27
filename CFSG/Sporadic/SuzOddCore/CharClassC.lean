module

public import CFSG.Sporadic.SuzOddCore.CharClassB

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2

@[expose] def suzThetaEquiv :
    Fin 22880 ≃ suzClassQ :=
  Equiv.ofBijective (fun i => ⟨suzTheta3 i, suzTheta3_mem i⟩)
    ⟨fun i j h => suzTheta3_injective (congrArg Subtype.val h), fun H => by
      obtain ⟨g, hg⟩ := H.2
      refine ⟨(g : Equiv.Perm (Fin 22880)) 0, Subtype.ext ?_⟩
      show suzTheta3 ((g : Equiv.Perm (Fin 22880)) 0) = (H : Subgroup suzP)
      rw [← autMap_conj_eq, hg]⟩

theorem suzThetaEquiv_apply
    (i : Fin 22880) : (suzThetaEquiv i : Subgroup suzP) = suzTheta3 i :=
  rfl

@[expose] def autClassPerm
    (α : MulAut suzP) : Equiv.Perm suzClassQ where
  toFun H := ⟨autMap α H, aut_map_mem_classQ α H.2⟩
  invFun H := ⟨autMap α⁻¹ H, aut_map_mem_classQ α⁻¹ H.2⟩
  left_inv H := Subtype.ext (by
    show autMap α⁻¹ (autMap α (H : Subgroup suzP)) = H
    rw [← autMap_mul, inv_mul_cancel, autMap_one])
  right_inv H := Subtype.ext (by
    show autMap α (autMap α⁻¹ (H : Subgroup suzP)) = H
    rw [← autMap_mul, mul_inv_cancel, autMap_one])

theorem autClassPerm_apply
    (α : MulAut suzP) (H : suzClassQ) :
    (autClassPerm α H : Subgroup suzP) = autMap α H := rfl

@[expose] def phiPerm
    (α : MulAut suzP) : Equiv.Perm (Fin 22880) :=
  suzThetaEquiv.trans ((autClassPerm α).trans suzThetaEquiv.symm)

theorem theta_phiPerm
    (α : MulAut suzP) (i : Fin 22880) :
    suzTheta3 (phiPerm α i) = autMap α (suzTheta3 i) := by
  have h : suzThetaEquiv (phiPerm α i) = autClassPerm α (suzThetaEquiv i) := by
    simp only [phiPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact congrArg Subtype.val h

theorem phiPerm_adj
    (α : MulAut suzP) (i j : Fin 22880) :
    suzGamma.Adj (phiPerm α i) (phiPerm α j) ↔ suzGamma.Adj i j := by
  by_cases hij : i = j
  · subst hij
    simp
  have hne : phiPerm α i ≠ phiPerm α j := fun h => hij ((phiPerm α).injective h)
  rw [adj_iff_commutator hne, adj_iff_commutator hij, theta_phiPerm, theta_phiPerm,
    commutator_autMap]

@[expose] def suzGraphPhi :
    MulAut suzP →* (suzGamma ≃g suzGamma) where
  toFun α := ⟨phiPerm α, phiPerm_adj α _ _⟩
  map_one' := by
    apply RelIso.ext
    intro i
    apply suzTheta3_injective
    change suzTheta3 (phiPerm 1 i) = suzTheta3 i
    rw [theta_phiPerm, autMap_one]
  map_mul' α β := by
    apply RelIso.ext
    intro i
    apply suzTheta3_injective
    change suzTheta3 (phiPerm (α * β) i) = suzTheta3 (phiPerm α (phiPerm β i))
    rw [theta_phiPerm, theta_phiPerm, theta_phiPerm, autMap_mul]

theorem suzGraphPhi_apply
    (α : MulAut suzP) (i : Fin 22880) :
    suzGraphPhi α i = phiPerm α i := rfl

theorem theta_suzGraphPhi
    (α : MulAut suzP) (i : Fin 22880) :
    suzThetaEquiv (suzGraphPhi α i) = autClassPerm α (suzThetaEquiv i) :=
  Subtype.ext (theta_phiPerm α i)

theorem suzGraphPhi_conj
    (g : suzP) (i : Fin 22880) :
    suzGraphPhi (MulAut.conj g) i = (g : Equiv.Perm (Fin 22880)) i := by
  apply suzTheta3_injective
  rw [suzGraphPhi_apply, theta_phiPerm, suzTheta3_equivariant]

theorem suzGraphPhi_injective :
    Function.Injective suzGraphPhi := by
  rw [injective_iff_map_eq_one]
  intro α hα
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have h := congrArg suzGraphPhi (aut_mul_conj α g)
  rw [map_mul, map_mul, hα, one_mul, mul_one] at h
  have := congrArg (fun σ : suzGamma ≃g suzGamma => σ x) h
  simp only [suzGraphPhi_conj] at this
  rw [MulAut.one_apply]
  exact this.symm

theorem CTUC_Suz_characteristic_three_class_and_faithful_graph_action :
    (∀ α : MulAut suzP, ∀ H ∈ suzClassQ, autMap α H ∈ suzClassQ) ∧
    (∃! θ : Fin 22880 ≃ suzClassQ, (θ 0 : Subgroup suzP) = suzQP ∧
      ∀ (g : suzP) (i : Fin 22880),
        (θ ((g : Equiv.Perm (Fin 22880)) i) : Subgroup suzP) = autMap (MulAut.conj g) (θ i)) ∧
    (∀ i j : Fin 22880, i ≠ j →
      (suzGamma.Adj i j ↔
        ⁅(suzThetaEquiv i : Subgroup suzP), (suzThetaEquiv j : Subgroup suzP)⁆ = ⊥)) ∧
    (∀ (α : MulAut suzP) (i : Fin 22880),
      suzThetaEquiv (suzGraphPhi α i) = autClassPerm α (suzThetaEquiv i)) ∧
    Function.Injective suzGraphPhi ∧
    (∀ (g : suzP) (i : Fin 22880), suzGraphPhi (MulAut.conj g) i = (g : Equiv.Perm (Fin 22880)) i) ∧
    Nat.card (MulAut suzP) ≤ Nat.card (suzGamma ≃g suzGamma) := by
  refine ⟨fun α H hH => aut_map_mem_classQ α hH, ⟨suzThetaEquiv, ⟨suzTheta3_zero,
    fun g i => suzTheta3_equivariant g i⟩, fun θ ⟨h0, heq⟩ => ?_⟩, fun i j hij =>
    adj_iff_commutator hij, theta_suzGraphPhi, suzGraphPhi_injective, suzGraphPhi_conj,
    Nat.card_le_card_of_injective _ suzGraphPhi_injective⟩
  have := suzTheta3_unique (fun i => (θ i : Subgroup suzP)) h0 heq
  exact Equiv.ext fun i => Subtype.ext (congrFun this i)

end CFSG.Sporadic.SuzOddCore
