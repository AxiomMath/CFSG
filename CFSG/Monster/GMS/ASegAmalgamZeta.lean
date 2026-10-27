module

public import CFSG.Monster.GMS.ASegTitsTri
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10064
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10077
public import Certificates.Certificate8955
public import CFSG.Sporadic.Co1.Module.CoTwoData
public import Certificates.Certificate10067
public import Certificates.Kernel.Co1B.Tri2045

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Assembly CFSG.Monster.GMS.S4Family

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Inner

variable {G G' : Type*} [Group G] [Group G']

theorem exists_inner_of_isIsoOn_at {x t : G} (hAt : CentInvAutInnerAt x t) {f₁ f₂ : G → G'}
    {K : Subgroup G'} (h₁ : IsIsoOn f₁ (C[x] ⊓ C[t]) K) (h₂ : IsIsoOn f₂ (C[x] ⊓ C[t]) K)
    (hxe : f₁ x = f₂ x) (hte : f₁ t = f₂ t) :
    ∃ h ∈ C[x] ⊓ C[t], ∀ g ∈ C[x] ⊓ C[t], f₂ g = f₁ (h * g * h⁻¹) := by
  let ψ : ↥(C[x] ⊓ C[t]) ≃* ↥(C[x] ⊓ C[t]) := (isoEquiv h₂).trans (isoEquiv h₁).symm
  have hψ : ∀ g : ↥(C[x] ⊓ C[t]), f₁ (ψ g : G) = f₂ (g : G) := fun g =>
    congrArg Subtype.val ((isoEquiv h₁).apply_symm_apply (isoEquiv h₂ g))
  have hfix : ∀ (y : G), f₁ y = f₂ y → ∀ g : ↥(C[x] ⊓ C[t]), (g : G) = y → ψ g = g := by
    intro y hy g hg
    refine (isoEquiv h₁).injective (Subtype.ext ?_)
    show f₁ (ψ g : G) = f₁ (g : G)
    rw [hψ g, hg, hy]
  obtain ⟨h, hh, hψg⟩ := hAt ψ (hfix x hxe) (hfix t hte)
  refine ⟨h, hh, fun g hg => ?_⟩
  have e := hψ ⟨g, hg⟩
  rw [hψg ⟨g, hg⟩] at e
  exact e.symm

theorem exists_inner_of_isIsoOn_centralizer_at {x t : G} (hAt : CentInvAutInnerAt x t)
    (htx : t ∈ C[x]) {f₁ f₂ : G → G'} {x' t' : G'} (h₁ : IsIsoOn f₁ C[t] C[t'])
    (h₂ : IsIsoOn f₂ C[x] C[x']) (hx₁ : f₁ x = x') (hx₂ : f₂ x = x') (ht₁ : f₁ t = t')
    (ht₂ : f₂ t = t') :
    ∃ h ∈ C[x] ⊓ C[t], ∀ g ∈ C[x] ⊓ C[t], f₂ g = f₁ (h * g * h⁻¹) := by
  have hxt : x ∈ C[t] := mem_centralizer_comm.mpr htx
  have h₁' := isIsoOn_centralizer_inf h₁ hxt
  have h₂' := isIsoOn_inf_centralizer h₂ htx
  rw [hx₁] at h₁'
  rw [ht₂] at h₂'
  exact exists_inner_of_isIsoOn_at hAt h₁' h₂' (hx₁.trans hx₂.symm) (ht₁.trans ht₂.symm)

end Inner

section Zeta

variable {G G' : Type*} [Group G] [Group G']

structure AlphaZeta (a y z : G) (a' y' z' : G') (A Z : G → G') : Prop where
  hA : IsIsoOn A C[a] C[a']
  hZ : IsIsoOn Z C[z] C[z']
  A_a : A a = a'
  A_y : A y = y'
  A_z : A z = z'
  Z_a : Z a = a'
  Z_y : Z y = y'
  Z_z : Z z = z'
  Z_eq_A : ∀ g ∈ C[a] ⊓ C[z], Z g = A g

end Zeta

section Exists

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {d₀ d₀' : B}
  {a z₀ y z : G} {a' z₀' : G'}

theorem exists_alpha_zeta
    (I : GMSInterfaces d₀ G) (I' : GMSInterfaces d₀' G')
    (hG : GMSF1Type d₀ a z₀) (hG' : GMSF1Type d₀' a' z₀') (hTB : TwoBabyUnique)
    (hDC : Co1DoubleCoverTwoB) (hCB : CentInvAutInnerAt a z) (D : ASegData a z₀ y z) :
    ∃ (A Z : G → G') (y' z' : G'), ASegData a' z₀' y' z' ∧ AlphaZeta a y z a' y' z' A Z := by
  have h := D.comm3 hG
  obtain ⟨α⟩ := hTB G G' a a' (hG.1.isTwoBabyCentralizer I.sls)
    (hG'.1.isTwoBabyCentralizer I'.sls)
  have hA : IsIsoOn (extendFun α) C[a] C[a'] := isIsoOn_extendFun α
  generalize extendFun α = A at hA
  have hAa : A a = a' := apply_self_twoA I' hG' hG.1.1 (IsConj.refl a') hA
  have hfus : ∀ x ∈ C[a], IsConj a x ↔ IsConj a' (A x) := fun x hx =>
    isConj_iff_of_mulEquiv_twoA I I' co2StabFacts hG hG' (IsConj.refl a) (IsConj.refl a')
      (isoEquiv hA) ⟨x, hx⟩
  have haC : a ∈ C[a] := self_mem_centralizer a
  have hyC : y ∈ C[a] := Subgroup.mem_centralizer_singleton_iff.2 h.ya
  have hzC : z ∈ C[a] := Subgroup.mem_centralizer_singleton_iff.2 h.za
  have hyzC : y ∈ C[z] := Subgroup.mem_centralizer_singleton_iff.2 D.comm_yz
  have hay : A (a * y) = a' * A y := by rw [hA.map_mul a haC y hyC, hAa]
  have haz : A (a * z) = a' * A z := by rw [hA.map_mul a haC z hzC, hAa]
  have hyz : A (y * z) = A y * A z := hA.map_mul y hyC z hzC
  have hayz : A (a * y * z) = a' * A y * A z := by
    rw [hA.map_mul (a * y) (C[a].mul_mem haC hyC) z hzC, hay]
  have hz2' : orderOf (A z) = 2 :=
    (iso_orderOf hA hzC).trans (orderOf_eq_two_of_isConj_z₀ hG D.isConj_z)
  have hzB : IsConj z₀' (A z) := by
    rcases isConj_or_isConj_z₀ I' hG' (IsConj.refl a') (hA.map_mem z hzC) hz2' with hh | hh
    · exact absurd ((hfus z hzC).2 hh) (fun h' => not_isConj_of_isConj hG h' D.isConj_z)
    · exact hh
  have D' : ASegData a' z₀' (A y) (A z) :=
    { isConj_y := (hfus y hyC).1 D.isConj_y
      isConj_ay := by
        rw [← hay]
        exact (hfus _ (C[a].mul_mem haC hyC)).1 D.isConj_ay
      isConj_z := hzB
      comm_az := by
        have := (iso_commute hA haC hzC).2 D.comm_az
        rwa [hAa] at this
      comm_yz := (iso_commute hA hyC hzC).2 D.comm_yz
      isConj_az := by
        rw [← haz]
        exact (hfus _ (C[a].mul_mem haC hzC)).1 D.isConj_az
      isConj_yz := by
        rw [← hyz]
        exact (hfus _ (C[a].mul_mem hyC hzC)).1 D.isConj_yz
      isConj_ayz := by
        rw [← hayz]
        exact (hfus _ (C[a].mul_mem (C[a].mul_mem haC hyC) hzC)).1 D.isConj_ayz }
  have haQ : a ∈ leechQ z :=
    mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG (IsConj.refl a) D.isConj_z D.comm_az
      D.isConj_az
  have ha'Q : a' ∈ leechQ (A z) :=
    mem_leechQ_of_isConj_mul I'.sls I'.tableV I'.leech hG' (IsConj.refl a') D'.isConj_z
      D'.comm_az D'.isConj_az
  obtain ⟨f, hf, hfa⟩ := exists_isIsoOn_apply_eq I I' hG hG' hDC D.isConj_z D'.isConj_z haQ
    (IsConj.refl a) ha'Q (IsConj.refl a')
  have hfz : f z = A z :=
    apply_self_twoB hG' (orderOf_eq_two_of_isConj_z₀ hG D.isConj_z) D'.isConj_z hf
  obtain ⟨c, hc, hconj⟩ := exists_inner_of_isIsoOn_centralizer_at hCB hzC hf hA hfa hAa hfz rfl
  have hZ : IsIsoOn (fun x => f (c * x * c⁻¹)) C[z] C[A z] :=
    isIsoOn_comp (isIsoOn_conj_self (Subgroup.mem_inf.1 hc).2) hf
  have hZA : ∀ g ∈ C[a] ⊓ C[z], f (c * g * c⁻¹) = A g := fun g hg => (hconj g hg).symm
  refine ⟨A, fun x => f (c * x * c⁻¹), A y, A z, D', hA, hZ, hAa, rfl, rfl, ?_,
    hZA y ⟨hyC, hyzC⟩, ?_, hZA⟩
  · show f (c * a * c⁻¹) = a'
    rw [conj_eq_of_mem_centralizer (Subgroup.mem_inf.1 hc).1]
    exact hfa
  · show f (c * z * c⁻¹) = A z
    rw [conj_eq_of_mem_centralizer (Subgroup.mem_inf.1 hc).2]
    exact hfz

end Exists

end CFSG.Monster.GMS
