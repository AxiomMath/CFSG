
module

public import CFSG.Monster.B.Rep4371.PacketGen
public import Certificates.Data.CFSGNative.MonsterB.DyadicReduce
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Cbar.LocalE

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot CFSG.Monster.B.Rep4371

theorem selIdx_lt (g : Fin 26) : Dyadic.Native.selIdx g < 48 := by
  unfold Dyadic.Native.selIdx
  split_ifs <;> omega

@[expose] noncomputable def selGen (g : Fin 26) : Cbar :=
  packetElt ⟨Dyadic.Native.selIdx g, selIdx_lt g⟩

theorem qElt_one : qElt 1 = TQ (basisC 1 + epsStar 1 • basisC 0) := by
  unfold qElt
  rw [ite_eq_right (by norm_num), dite_eq_left (by norm_num)]
  rfl

theorem basisC_one_add_ne_zero : basisC 1 + epsStar 1 • basisC 0 ≠ 0 := by
  intro h
  have h1 := congrArg (fun a => basisC.repr a 1) h
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
  revert h1
  decide

theorem coordOf_qElt_one : coordOf (qElt 1) = (basisC 1 + epsStar 1 • basisC 0, 0) := by
  rw [qElt_one, TQ, Griess.coordOf_spinEquiv]

theorem coordOf_rStar_fst : (coordOf rStar).1 = 0 := by
  rw [rStar_eq, pauliQ, Griess.coordOf_spinEquiv, toSC_a]
  exact toC_zero

theorem psiBar_kappa_rho_ne_one {q : Q} (hq : q ∈ Subgroup.centralizer {rStar})
    (h0 : phi0 (coordOf q) ≠ 0) (hv : phi0 (coordOf q) ≠ phi0 (coordOf rStar)) :
    psiBar ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩ ≠ 1 := by
  rw [psiBar_kappa_rho hq, Ne, ofAdd_eq_one, Submodule.Quotient.mk_eq_zero]
  intro h
  rcases (mem_vLineL.1 h : phi0 (coordOf q) = 0 ∨ phi0 (coordOf q) = phi0 (coordOf rStar)) with
    h' | h'
  · exact h0 h'
  · exact hv h'

theorem psiBar_qElt_one_ne_one :
    psiBar ⟨kappa ⟨rhoEquiv (qElt 1), rhoEquiv_mem_Cgen (qElt_mem_centralizer 1)⟩,
      kappa_rho_mem_Ebar (qElt_mem_centralizer 1)⟩ ≠ 1 := by
  refine psiBar_kappa_rho_ne_one (qElt_mem_centralizer 1) (fun h => ?_) (fun h => ?_)
  · have h' := phi0_injective (h.trans (map_zero phi0).symm)
    rw [coordOf_qElt_one] at h'
    exact basisC_one_add_ne_zero (congrArg Prod.fst h')
  · have h' := congrArg Prod.fst (phi0_injective h)
    rw [coordOf_qElt_one, coordOf_rStar_fst] at h'
    exact basisC_one_add_ne_zero h'

theorem selGen_zero : selGen 0 =
    kappa ⟨rhoEquiv (qElt 1), rhoEquiv_mem_Cgen (qElt_mem_centralizer 1)⟩ := by
  have hk : (⟨Dyadic.Native.selIdx ((0 : Fin 26) : ℕ), selIdx_lt 0⟩ : Fin 48) = 1 := Fin.ext rfl
  rw [selGen, hk, packetElt]
  exact congrArg kappa (Subtype.ext ((coe_packetGen_of_lt (k := 1) (by decide)).trans rfl))

theorem selGen_succ (i : Fin 24) :
    selGen ⟨i + 1, by omega⟩ = kappa ⟨hElt i, hElt_mem_Cgen i⟩ := by
  have hk : (⟨Dyadic.Native.selIdx ((⟨i + 1, by omega⟩ : Fin 26) : ℕ), selIdx_lt _⟩ : Fin 48) =
      ⟨23 + i, by omega⟩ := by
    apply Fin.ext
    show Dyadic.Native.selIdx ((i : ℕ) + 1) = 23 + i
    unfold Dyadic.Native.selIdx
    rw [ite_eq_right (by omega)]
    omega
  rw [selGen, hk, packetElt_h]

theorem selGen_last : selGen 25 = taubar := by
  have hk : (⟨Dyadic.Native.selIdx ((25 : Fin 26) : ℕ), selIdx_lt 25⟩ : Fin 48) = 47 := Fin.ext rfl
  rw [selGen, hk, packetElt_tau]
  rfl

end CFSG.Monster.B
