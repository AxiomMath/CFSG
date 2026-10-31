
module

public import CFSG.Sporadic.HeldB.InnerClassCheckBase
public import CFSG.Sporadic.HeldB.OuterClassBase
public import CFSG.Sporadic.HeldB.InnerRestrict
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.CertPBridgeCheckInputs
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.InnerClassCheckInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.He.Certificate
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec

@[expose] public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native

def heT1cP : Equiv.Perm (Fin 8330) := heGenPerm 1 * heT1P * (heGenPerm 1)⁻¹

theorem rep_heT1c :
    Rep 8330 heT1cArr heT1cP := by
  rw [heT1cP, mul_assoc]
  exact rep_compA (rep_heGen (by norm_num)) (rep_compA rep_heT1 (rep_heGen_inv (by norm_num)))

theorem heT1cP_mem : heT1cP ∈ heP :=
  heP.mul_mem (heP.mul_mem (heGenPerm_mem (by norm_num)) heT1P_mem)
    (heP.inv_mem (heGenPerm_mem (by norm_num)))

theorem commB_iff_heP
    {t : Array ℕ} {τ : Equiv.Perm (Fin 8330)} (ht : Rep 8330 t τ)
    (hτ : τ ∈ heP) {w : List (Array ℕ)} {g : Equiv.Perm (Fin 8330)} (hw : RepW 8330 w g)
    (hg : g ∈ heP) : commB t heBase w = true ↔ τ * g = g * τ :=
  commB_iff heP_baseFaithful ht hw heBase_lt
    (heP.mul_mem (heP.inv_mem (heP.mul_mem hg hτ)) (heP.mul_mem hτ hg))

def heInvs : Set (Equiv.Perm (Fin 8330)) := {x | x ∈ heP ∧ orderOf x = 2}

theorem heInvs_conj {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heInvs) {h : Equiv.Perm (Fin 8330)}
    (hh : h ∈ heP) : h * x * h⁻¹ ∈ heInvs :=
  ⟨heP.mul_mem (heP.mul_mem hh hx.1) (heP.inv_mem hh), by rw [orderOf_conj_eq, hx.2]⟩

theorem conjClass_subset_heInvs {t : Equiv.Perm (Fin 8330)} (ht : t ∈ heP)
    (ht2 : orderOf t = 2) : conjClass heP t ⊆ heInvs := by
  rintro x ⟨c, hc, rfl⟩
  exact heInvs_conj ⟨ht, ht2⟩ hc

theorem conjClass_subset_of_mem {s t : Equiv.Perm (Fin 8330)} (h : t ∈ conjClass heP s) :
    conjClass heP t ⊆ conjClass heP s := by
  rintro x ⟨c, hc, rfl⟩
  obtain ⟨d, hd, e⟩ := conj_mem_of_conj hc h
  exact ⟨d, hd, e⟩

theorem sum_fixCard_conjClass {t : Equiv.Perm (Fin 8330)} (hf : (conjClass heP t).Finite) :
    ∑ x ∈ hf.toFinset, fixCard x = (conjClass heP t).ncard * fixCard t := by
  rw [Finset.sum_congr rfl (g := fun _ => fixCard t) fun x hx => ?_]
  · rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hf]
  · rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact fixCard_conj c t

def heCentralizerEquiv (s : heP) :
    Subgroup.centralizer ({s} : Set heP) ≃* centralizerIn heP (s : Equiv.Perm (Fin 8330)) :=
  ((Subgroup.centralizer ({s} : Set heP)).equivMapOfInjective heP.subtype
    heP.subtype_injective).trans (MulEquiv.subgroupCongr (map_centralizer_subtype heP s))

end CFSG.Sporadic.HeldB
