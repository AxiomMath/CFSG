module

public import CFSG.Monster.B.Rep4371.PacketData
public import CFSG.Monster.B.Cbar.GenData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.B.Rep4371 CFSG.Monster.B.Short

theorem qElt_mem_centralizer (i : Fin 23) : qElt i ∈ Subgroup.centralizer {Short.rStar} :=
  Subgroup.mem_centralizer_singleton_iff.2 (qElt_mul_rStar i)

theorem rhoEquiv_qElt_mem_Cgen (i : Fin 23) : rhoEquiv (qElt i) ∈ Cgen :=
  rhoCQ_le_Cgen (mem_rhoCQ.2 ⟨qElt i, qElt_mem_centralizer i, rfl⟩)

theorem conjPermN_rStar : ∀ i < 12,
    Model.conjPermN Model.recPerms[i]! (false, 0, 191) = (false, 0, 191) := by
  decide +kernel

theorem conjYN_rStar : ∀ i < 11,
    Model.conjYN ([3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][i]!) (false, 0, 191) =
      (false, 0, 191) := by
  decide +kernel

theorem conjXiN_rStar : Model.conjYN 1 (Model.conjXiN (false, 0, 191)) = (false, 0, 191) := by
  decide +kernel

theorem conjQ_codeSign_pauliQ {c : C} {a : ℕ} (h : c = toC a) (y : Model.Pauli) :
    conjQ ⟨(YU ⟨c, 0⟩, gO c), YU_gO_mem_Pvis ⟨c, 0⟩⟩ (pauliQ y) = pauliQ (Model.conjYN a y) := by
  subst h
  exact conjQ_sign_toQ a y

theorem conjQ_hPair_rStar (i : Fin 24) : conjQ (hPair i) Short.rStar = Short.rStar := by
  rw [rStar_eq]
  rcases Nat.lt_or_ge (i : ℕ) 12 with h | h
  · rw [hPair_of_lt_twelve h, permPair, conjQ_perm_toQ _ (repPerm_recPerm i h),
      conjPermN_rStar _ h]
  rcases Nat.lt_or_ge (i : ℕ) 23 with h' | h'
  · rw [hPair_of_codeSign h h', conjQ_codeSign_pauliQ (recCode_eq h h'),
      conjYN_rStar _ (by omega)]
  · have hi : i = 23 := Fin.ext (by omega)
    subst hi
    rw [hPair_xi]
    show conjQ (xiPair * signPair 1) (pauliQ (false, 0, 191)) = pauliQ (false, 0, 191)
    rw [conjQ_mul]
    exact (congrArg (conjQ (signPair 1)) (conjQ_xi_toQ _)).trans
      ((conjQ_sign_toQ 1 _).trans (congrArg pauliQ conjXiN_rStar))

theorem hElt_mem_Jstar (i : Fin 24) : hElt i ∈ Jstar := by
  refine ⟨hElt_mem_Gvis i, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h := Short.thetaEquiv_conj_rhoEquiv (hPair i) Short.rStar
  rw [conjQ_hPair_rStar, mul_inv_eq_iff_eq_mul] at h
  show thetaEquiv (hPair i) * rhoEquiv Short.rStar = rhoEquiv Short.rStar * thetaEquiv (hPair i)
  exact h

theorem hElt_mem_Cgen (i : Fin 24) : hElt i ∈ Cgen := Jstar_le_Cgen (hElt_mem_Jstar i)

@[expose] noncomputable def packetGen (k : Fin 48) : Cgen :=
  if h : (k : ℕ) < 23 then ⟨rhoEquiv (qElt ⟨k, h⟩), rhoEquiv_qElt_mem_Cgen _⟩
  else if h' : (k : ℕ) < 47 then ⟨hElt ⟨k - 23, by omega⟩, hElt_mem_Cgen _⟩
  else ⟨tauB, tauB_mem_Cgen⟩

@[expose] noncomputable def packetElt (k : Fin 48) : Cbar := kappa (packetGen k)

theorem packetElt_eq (k : Fin 48) : packetElt k = kappa (packetGen k) := rfl

theorem coe_packetGen_of_lt {k : Fin 48} (h : (k : ℕ) < 23) :
    (packetGen k : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv (qElt ⟨k, h⟩) := by
  rw [packetGen, dite_eq_left h]

theorem coe_packetGen_pauli {k : Fin 48} (h : (k : ℕ) < 23) :
    (packetGen k : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv (pauliQ (Model.qPauli k)) := by
  rw [coe_packetGen_of_lt h, qElt_eq]

theorem coe_packetGen_h (i : Fin 24) :
    (packetGen ⟨23 + i, by omega⟩ : SpaceB ≃ₗ[ℚ] SpaceB) = hElt i := by
  rw [packetGen, dite_eq_right (show ¬ 23 + (i : ℕ) < 23 by omega),
    dite_eq_left (show 23 + (i : ℕ) < 47 by omega)]
  show hElt ⟨23 + (i : ℕ) - 23, _⟩ = hElt i
  congr 1
  exact Fin.ext (show 23 + (i : ℕ) - 23 = i by omega)

theorem coe_packetGen_tau : (packetGen 47 : SpaceB ≃ₗ[ℚ] SpaceB) = tauB := by
  rw [packetGen, dite_eq_right (show ¬ ((47 : Fin 48) : ℕ) < 23 by decide),
    dite_eq_right (show ¬ ((47 : Fin 48) : ℕ) < 47 by decide)]

theorem packetGen_of_lt {k : Fin 48} (h : (k : ℕ) < 23) :
    packetGen k = ⟨rhoEquiv (qElt ⟨k, h⟩), rhoEquiv_qElt_mem_Cgen _⟩ :=
  Subtype.ext (coe_packetGen_of_lt h)

theorem packetGen_h (i : Fin 24) :
    packetGen ⟨23 + i, by omega⟩ = ⟨hElt i, hElt_mem_Cgen i⟩ :=
  Subtype.ext (coe_packetGen_h i)

theorem packetGen_tau : packetGen 47 = tauC := Subtype.ext coe_packetGen_tau

theorem packetElt_of_lt {k : Fin 48} (h : (k : ℕ) < 23) :
    packetElt k = kappa ⟨rhoEquiv (pauliQ (Model.qPauli k)), qElt_eq ⟨k, h⟩ ▸
      rhoEquiv_qElt_mem_Cgen ⟨k, h⟩⟩ :=
  congrArg kappa (Subtype.ext (coe_packetGen_pauli h))

theorem packetElt_h (i : Fin 24) :
    packetElt ⟨23 + i, by omega⟩ = kappa ⟨hElt i, hElt_mem_Cgen i⟩ :=
  congrArg kappa (packetGen_h i)

theorem packetElt_tau : packetElt 47 = kappa tauC := congrArg kappa packetGen_tau

end CFSG.Monster.B
