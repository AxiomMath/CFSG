
module

public import CFSG.Monster.B.TwoA.Unitary.WStabBase

public import CFSG.Monster.B.TwoA.Unitary.Orbit
public import CFSG.Monster.B.TwoA.Base.Frame
public import CFSG.Monster.B.Classical.ThreePlaneData
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import Certificates.Certificate3042
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] restAction

theorem p2Cert_ok : certOK amul permGens idArr p2Cert = true :=
  Certificates.certificate3042.1

theorem p2Cert_size : p2Cert.pts.size = 40320 :=
  Certificates.certificate3042.2

theorem natCard_closure_perms :
    Nat.card (Subgroup.closure (Set.range fun k : Fin 6 => (n6Aut k : Equiv.Perm (Fin 24)))) =
      40320 := by
  have h := (card_closure_of_certOK permGens_perm decode_idArr p2Cert_ok).1
  rw [p2Cert_size] at h
  have hs : (fun k => decode permGens[k]!) '' {k | k < permGens.size} =
      Set.range fun k : Fin 6 => (n6Aut k : Equiv.Perm (Fin 24)) := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, permGens_size]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
  rw [← hs, h]

theorem natCard_closure_n6Aut : Nat.card
    (Subgroup.closure (Set.range n6Aut)) = 40320 := by
  have e : (Subgroup.closure (Set.range n6Aut)).map AutPerm.subtype =
      Subgroup.closure (Set.range fun k : Fin 6 => (n6Aut k : Equiv.Perm (Fin 24))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← natCard_closure_perms, ← e]
  exact Nat.card_congr ((Subgroup.closure (Set.range n6Aut)).equivMapOfInjective _
    Subtype.val_injective).toEquiv

theorem closure_n6Aut :
    Subgroup.closure (Set.range n6Aut) = P2 := by
  have hle : Subgroup.closure (Set.range n6Aut) ≤ P2 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact n6Aut_mem_P2 k
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_P2, natCard_closure_n6Aut])

theorem mk_PO_mem_H6 {p : AutPerm}
    (hp : p ∈ P2) :
    (QuotientGroup.mk (PO p) : OLq) ∈ H6 := by
  have hp' : p⁻¹ ∈ (Subgroup.closure (Set.range n6Aut)) := by
    rw [closure_n6Aut]
    exact P2.inv_mem hp
  have hmap : permQ p⁻¹ ∈ (Subgroup.closure (Set.range n6Aut)).map permQ := ⟨_, hp', rfl⟩
  rw [MonoidHom.map_closure] at hmap
  have hle : Subgroup.closure (permQ '' Set.range n6Aut) ≤ H6 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have e : permQ (n6Aut k) = (n6Elt ⟨k, by omega⟩)⁻¹ := by
      rw [n6Elt_of_lt (show ((⟨k, by omega⟩ : Fin 17) : ℕ) < 6 from k.2)]
      change QuotientGroup.mk (PO (n6Aut k)⁻¹) = _
      rw [PO_inv, QuotientGroup.mk_inv]
    rw [SetLike.mem_coe, e]
    exact inv_mem (Subgroup.subset_closure ⟨_, rfl⟩)
  have h := hle hmap
  change QuotientGroup.mk (PO p⁻¹⁻¹) ∈ H6 at h
  rwa [inv_inv] at h

theorem monoSub_c012_le_H6 :
    monoSub c012Hyp ≤ H6 := by
  intro x hx
  obtain ⟨a, ha, p, hp, rfl⟩ := (mem_monoSub_iff c012Hyp).1 hx
  rw [QuotientGroup.mk_mul]
  exact mul_mem (mk_gO_mem_H6 ha) (mk_PO_mem_H6 hp)

theorem UsigW_le_H6K :
    UsigW ≤ H6K := by
  intro k hk
  have h := monoSub_c012_le_H6 ((mem_UsigW_iff k).1 hk)
  rw [← map_H6K] at h
  obtain ⟨k', hk', e⟩ := h
  rw [← Subtype.val_injective e]
  exact hk'

end CFSG.Monster.B.TwoA.Unitary
