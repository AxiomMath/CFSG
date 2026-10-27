
module

public import CFSG.Monster.B.TwoA.Par2.MainBase
public import CFSG.Monster.B.TwoA.Base.GeomNativeBase
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Monster.B.TwoA.Par3.CosetBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8

theorem mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have h := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

theorem map_pCore_le_of_sylow {G : Type*} [Group G] {K H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hP : ∃ P : Sylow p K, ∀ g ∈ (P : Subgroup K), (g : G) ∈ H) :
    (CFSG.pCore p K).map K.subtype ≤ H := by
  obtain ⟨P, hP⟩ := hP
  rintro _ ⟨g, hg, rfl⟩
  have : (CFSG.pCore p K).Normal := CFSG.pCore_normal
  exact hP g (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup P hg)

theorem deltaPair_23 : deltaPair 2 3 = deltaPair 0 2 + deltaPair 0 3 := by
  rw [deltaPair, deltaPair, deltaPair, ← Submodule.Quotient.mk_add]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem dhat_23 : dhat 2 3 = dhat 0 2 * dhat 0 3 := by
  have h : DQ (deltaPair 2 3) = DQ (deltaPair 0 3) * DQ (deltaPair 0 2) := by
    rw [deltaPair_23, DQ_add, DQ_comm]
  rw [dhat, dhat, dhat, dbar, dbar, dbar, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  change rhoEquiv (rMinus 2 3) = rhoEquiv (rMinus 0 2) * rhoEquiv (rMinus 0 3)
  rw [rMinus, rMinus, rMinus, h, rhoEquiv_mul]

theorem zhat_eq : zhat = cQ * dhat 0 3 := dhat_23

theorem Ctwo_le_Jhat : Ctwo ≤ Jhat := by
  rw [← centralizer_xhat]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 xhat_mem_Vhat)

theorem C3_le_Jhat :
    C3 ≤ Jhat := by
  rw [← centralizer_xhat]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 xhat_mem_E3)

theorem C3_le_Ntwo : C3 ≤ Ntwo :=
  (Subgroup.centralizer_le fun _ h => Vhat_le_E3 h).trans Ctwo_le_Ntwo

theorem Ehat_le_Ntwo :
    Ehat ≤ Ntwo := by
  rw [Ntwo, Vhat_eq_EU]
  exact Ehat_le_normalizer_EU

theorem Ehat_le_K3 :
    Ehat ≤ K3 := by
  rw [K3, E3_eq_EU]
  exact Ehat_le_normalizer_EU

theorem R2_le_Jhat :
    R2 ≤ Jhat := R2_le_Ctwo.trans Ctwo_le_Jhat

theorem R3_le_Jhat :
    R3 ≤ Jhat := Par3.R3_le_C3.trans C3_le_Jhat

theorem R3_le_Ntwo :
    R3 ≤ Ntwo := Par3.R3_le_C3.trans C3_le_Ntwo

theorem conj_E3_of_mem
    {r : Dfull} (hr : r ∈ R2 ⊓ Subgroup.centralizer {cQ}) :
    ∀ x ∈ E3, r * x * r⁻¹ ∈ E3 := by
  have hV : ∀ v ∈ Vhat, r * v * r⁻¹ = v := fun v hv => by
    have h := Subgroup.mem_centralizer_iff.1 (R2_le_Ctwo hr.1) v hv
    rw [← h, mul_inv_cancel_right]
  have hc : r * cQ * r⁻¹ = cQ := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hr.2, mul_inv_cancel_right]
  have hS : E3 ≤ E3.comap (MulAut.conj r).toMonoidHom := by
    rw [E3, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · show r * xhat * r⁻¹ ∈ E3
      rw [hV _ xhat_mem_Vhat]
      exact xhat_mem_E3
    · show r * yhat * r⁻¹ ∈ E3
      rw [hV _ yhat_mem_Vhat]
      exact Vhat_le_E3 yhat_mem_Vhat
    · show r * zhat * r⁻¹ ∈ E3
      obtain ⟨v, hv, e⟩ := Par2.conj_blk_R2 hr.1 (Par2.dhat_mem_blk (Par2.toRest 3 (by decide)))
      have e' : r * dhat 0 3 * r⁻¹ = dhat 0 3 * v := e.symm
      rw [zhat_eq, show r * (cQ * dhat 0 3) * r⁻¹ = (r * cQ * r⁻¹) * (r * dhat 0 3 * r⁻¹) by
        group, hc, e', ← mul_assoc, ← zhat_eq]
      exact E3.mul_mem (Subgroup.subset_closure (by simp)) (Vhat_le_E3 hv)
  exact fun x hx => hS hx

theorem R2c_le_K3 :
    R2 ⊓ Subgroup.centralizer {cQ} ≤ K3 := fun r hr =>
  mem_normalizer_of_conj (conj_E3_of_mem hr) fun x hx => by
    simpa using conj_E3_of_mem (inv_mem hr) x hx

end CFSG.Monster.B.TwoA.Amalgam
