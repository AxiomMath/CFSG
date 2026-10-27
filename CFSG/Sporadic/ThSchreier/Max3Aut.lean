
module

public import CFSG.Sporadic.ThSchreier.Max3AutBase1

public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Sporadic.ThSchreier.Max3Action
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates
open scoped commutatorElement

theorem zM_ne_one : zM ≠ 1 := by
  intro h
  apply z_ne_one
  have := congrArg Subtype.val h
  simpa [zM] using this

theorem zM_mul_self :
    zM * zM = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  exact z_mul_self

theorem zM_central
    (m : ↥M) : zM * m = m * zM := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact (commute_z_of_mem_M m.2).eq

theorem finite_QM :
    Finite (Q.subgroupOf M) := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [card_Q]; norm_num)
  exact Finite.of_equiv _ eQ.symm.toEquiv

@[expose] noncomputable def piM :
    Q.subgroupOf M →* Multiplicative (Fin 8 → ZMod 2) :=
  piQ.comp (eQ : Q.subgroupOf M →* Q)

theorem piM_apply
    (g : Q.subgroupOf M) : piM g = piQ (eQ g) := rfl

theorem piM_surjective :
    Function.Surjective piM := by
  intro v
  obtain ⟨g, rfl⟩ := piQ_surjective v
  refine ⟨eQ.symm g, ?_⟩
  rw [piM_apply, MulEquiv.apply_symm_apply]

theorem piM_eq_one_iff
    (g : Q.subgroupOf M) :
    piM g = 1 ↔ g ∈ Subgroup.center (Q.subgroupOf M) := by
  rw [piM_apply, piQ_eq_one_iff, mem_center_QM_iff]

theorem mem_center_QM
    (g : Q.subgroupOf M) :
    g ∈ Subgroup.center (Q.subgroupOf M) ↔ (g : ↥M) ∈ Subgroup.zpowers zM := by
  rw [mem_center_QM_iff, center_Q, Subgroup.mem_subgroupOf, mem_zpowers_zM, eQ_coe]

theorem piM_conj
    (m : ↥M) (g : Q.subgroupOf M) :
    piM ⟨m * g * m⁻¹, normal_Q_subgroupOf_M.conj_mem g g.2 m⟩ =
      Multiplicative.ofAdd ((rhoHom m).mulVec (Multiplicative.toAdd (piM g))) := by
  rw [rhoHom_apply, rhoMat_mulVec]
  simp only [ofAdd_toAdd]
  have e : eQ ⟨m * g * m⁻¹, normal_Q_subgroupOf_M.conj_mem g g.2 m⟩ = conjQ m (eQ g) := by
    apply Subtype.ext
    rw [conjQ_apply, eQ_coe, eQ_coe, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [piM_apply, piM_apply, e, rhoM_piQ]

theorem piM_nfM
    (v : Fin 8 → ZMod 2) :
    piM ⟨nfM v, Subgroup.mem_subgroupOf.2 (nf_mem_Q 0 v)⟩ = Multiplicative.ofAdd v := by
  rw [piM_apply, ← piQ_nf v]
  congr 1

theorem comm_nfM
    (v w : Fin 8 → ZMod 2) :
    ⁅nfM v, nfM w⁆ = zM ^ (ExtraspecialNF.bil c v w).val := by
  have hdiag : ∀ i, c i i = 0 := by decide
  have h := ExtraspecialNF.commutator_eq_zpow symplectic_rel (fun i j => c_symm j i) hdiag 0 0 v w
  rw [← nf_eq_generic, ← nf_eq_generic, commutatorElement_def] at h
  apply Subtype.ext
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_inv]
  rcases ExtraspecialNF.zmod_two_cases (ExtraspecialNF.bil c v w) with hb | hb
  · rw [hb, ZMod.val_zero, pow_zero] at h ⊢
    rw [Subgroup.coe_one]
    exact h
  · rw [hb, ExtraspecialNF.val_one_two, pow_one] at h ⊢
    exact h

theorem centralizer_QM
    (m : ↥M) (hm : ∀ g ∈ Q.subgroupOf M, m * g = g * m) :
    m ∈ Subgroup.zpowers zM := by
  rw [mem_zpowers_zM, ← centralizer_Q_inf_M]
  refine ⟨Subgroup.mem_centralizer_iff.2 fun g hg => ?_, m.2⟩
  have := congrArg Subtype.val (hm ⟨g, Q_le_M hg⟩ (Subgroup.mem_subgroupOf.2 hg))
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
  exact this.symm

theorem rhoHom_eq_one_iff
    (m : ↥M) : rhoHom m = 1 ↔ m ∈ Q.subgroupOf M := by
  rw [rhoHom_apply, rhoMat_eq_one_iff, Subgroup.mem_subgroupOf]

@[expose] noncomputable def max3Data :
    AutCore.Data ↥M where
  Q := Q.subgroupOf M
  normal := normal_Q_subgroupOf_M
  core := pCore_M
  x := xM
  y := yM
  gen := closure_xM_yM
  κ := kappa
  κx := kappa_mk_x
  κy := kappa_mk_y
  ρ := rhoHom
  ρx := rhoMat_xM
  ρy := rhoMat_yM
  ρQ := rhoHom_eq_one_iff
  π := piM
  π_surj := piM_surjective
  π_ker := piM_eq_one_iff
  π_conj := piM_conj
  z := zM
  z_mem := Subgroup.mem_subgroupOf.2 z_mem_Q
  z_ne_one := zM_ne_one
  z_sq := zM_mul_self
  center := mem_center_QM
  z_central := zM_central
  s := nfM
  s_mem v := Subgroup.mem_subgroupOf.2 (nf_mem_Q 0 v)
  s_π := piM_nfM
  s_comm := comm_nfM
  Q_gen := Q_gen_M
  centralizer := centralizer_QM
  perfect := isPerfect_M

theorem max3_aut_eq_conj
    (α : MulAut ↥M) : ∃ m : ↥M, α = MulAut.conj m := by
  have : Finite ↥(max3Data.Q) := finite_QM
  exact max3Data.allInner α

theorem ctuc_Th_max3_automorphisms_inner :
    MonoidHom.range (MulAut.conj (G := ↥M)) = ⊤ := by
  refine eq_top_iff.2 fun α _ => ?_
  obtain ⟨m, rfl⟩ := max3_aut_eq_conj α
  exact ⟨m, rfl⟩

end CFSG.Sporadic.ThSchreier
