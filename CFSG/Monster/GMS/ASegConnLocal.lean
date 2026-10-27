module

public import CFSG.Monster.GMS.S4FamilyGroup
public import CFSG.Monster.GMS.S365
import CFSG.Monster.GMS.S31Three
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10043
public import Certificates.Certificate10069
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import CFSG.Monster.GMS.S365Coset
public import Certificates.Certificate10042Base

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace ASegConn

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_adj_of_not_mem_leechQ
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {w y : G}
    (hw : IsConj z₀ w) (hy : IsConj a y) (hyC : y ∈ Subgroup.centralizer ({w} : Set G))
    (hyQ : y ∉ leechQ w) :
    ∃ x : G, IsConj a x ∧ x ∈ leechQ w ∧ x * y = y * x ∧ IsConj a (x * y) := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨y₁, p, hy₁C, hpC, hpy, hy₁A, hay₁, hpA, hpa, -, hpay⟩ :=
    S4Family.exists_eight_data I hG (eightGroupExists_of I hG)
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf hG.1.1
  have hpa' : p * a = a * p := Subgroup.mem_centralizer_singleton_iff.mp hpC
  have hy₁a : y₁ * a = a * y₁ := Subgroup.mem_centralizer_singleton_iff.mp hy₁C
  have hpy₁ : p * y₁ = y₁ * p := Subgroup.mem_centralizer_singleton_iff.mp hpy
  have hcomm₁ : a * (p * a) = (p * a) * a := by rw [← mul_assoc, ← hpa']
  have hmul₁ : IsConj a (a * (p * a)) := by
    have e : a * (p * a) = p := by rw [hcomm₁, mul_assoc, haa, mul_one]
    rw [e]
    exact hpA
  have haQ : a ∈ leechQ (p * a) := h.mem_leechQ_of_isConj_mul (IsConj.refl a) hpa hcomm₁ hmul₁
  have hcomm₂ : y₁ * (p * a) = (p * a) * y₁ := by
    calc y₁ * (p * a) = (y₁ * p) * a := by rw [mul_assoc]
      _ = (p * y₁) * a := by rw [hpy₁]
      _ = p * (y₁ * a) := by rw [mul_assoc]
      _ = p * (a * y₁) := by rw [hy₁a]
      _ = (p * a) * y₁ := by rw [mul_assoc]
  have hy₁Q : y₁ ∉ leechQ (p * a) :=
    (h.not_mem_leechQ_of_isConj_mul hy₁A hpa hcomm₂ (by rw [hcomm₂]; exact hpay)).1
  obtain ⟨g₁, hg₁a, hg₁u⟩ := h.exists_conj_of_not_mem_leechQ hpa hy₁A
    (Subgroup.mem_centralizer_singleton_iff.mpr hcomm₂) hy₁Q
  obtain ⟨g₂, hg₂a, hg₂u⟩ := h.exists_conj_of_not_mem_leechQ hw hy hyC hyQ
  have hgy : (g₂ * g₁⁻¹) * y₁ * (g₂ * g₁⁻¹)⁻¹ = y := by
    rw [← hg₁a, ← hg₂a]
    group
  have hgw : (g₂ * g₁⁻¹) * (p * a) * (g₂ * g₁⁻¹)⁻¹ = w := by
    rw [← hg₁u, ← hg₂u]
    group
  refine ⟨(g₂ * g₁⁻¹) * a * (g₂ * g₁⁻¹)⁻¹, isConj_iff.mpr ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · have := conj_mem_leechQ_conj (c := g₂ * g₁⁻¹) haQ
    rwa [hgw] at this
  · rw [← hgy]
    calc (g₂ * g₁⁻¹) * a * (g₂ * g₁⁻¹)⁻¹ * ((g₂ * g₁⁻¹) * y₁ * (g₂ * g₁⁻¹)⁻¹)
        = (g₂ * g₁⁻¹) * (a * y₁) * (g₂ * g₁⁻¹)⁻¹ := by group
      _ = (g₂ * g₁⁻¹) * (y₁ * a) * (g₂ * g₁⁻¹)⁻¹ := by rw [hy₁a]
      _ = (g₂ * g₁⁻¹) * y₁ * (g₂ * g₁⁻¹)⁻¹ * ((g₂ * g₁⁻¹) * a * (g₂ * g₁⁻¹)⁻¹) := by group
  · rw [← hgy]
    have e : (g₂ * g₁⁻¹) * a * (g₂ * g₁⁻¹)⁻¹ * ((g₂ * g₁⁻¹) * y₁ * (g₂ * g₁⁻¹)⁻¹) =
        (g₂ * g₁⁻¹) * (a * y₁) * (g₂ * g₁⁻¹)⁻¹ := by group
    rw [e]
    exact hay₁.trans (isConj_iff.mpr ⟨_, rfl⟩)

section Closure

variable (P : G → Prop)
  (hadj : ∀ x y : G, IsConj a x → IsConj a y → P x → x ≠ y → IsConj a (x * y) → P y)
  (hQ : ∀ w : G, IsConj z₀ w → ∀ x y : G, IsConj a x → IsConj a y → x ∈ leechQ w →
    y ∈ leechQ w → P x → P y)

include hadj hQ

theorem mem_of_isConj_mem_centralizer
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {z x₀ : G}
    (hz : IsConj z₀ z) (hx₀ : IsConj a x₀) (hx₀Q : x₀ ∈ leechQ z) (hx₀P : P x₀) {y : G}
    (hy : IsConj a y) (hyC : y ∈ Subgroup.centralizer ({z} : Set G)) : P y := by
  by_cases hyQ : y ∈ leechQ z
  · exact hQ z hz x₀ y hx₀ hy hx₀Q hyQ hx₀P
  · obtain ⟨x, hx, hxQ, hxy, hxyA⟩ := exists_adj_of_not_mem_leechQ I hG hz hy hyC hyQ
    have hne : x ≠ y := fun e => hyQ (e ▸ hxQ)
    exact hadj x y hx hy (hQ z hz x₀ x hx₀ hx hx₀Q hxQ hx₀P) hne hxyA

theorem exists_mem_leechQ_of_isConj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {z x₀ : G}
    (hz : IsConj z₀ z) (hx₀ : IsConj a x₀) (hx₀Q : x₀ ∈ leechQ z) (hx₀P : P x₀) {s : G}
    (hs : IsConj z₀ s) (hsC : s ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ x : G, IsConj a x ∧ x ∈ leechQ s ∧ P x := by
  have hs2 : orderOf s = 2 := (orderOf_eq_of_isConj hs).symm.trans hG.2.1
  obtain ⟨y, hyC, hys, hyA⟩ := s31_four I.sls I.tableV I.leech hG I.leechInv hz hsC hs2
  have hyP : P y := mem_of_isConj_mem_centralizer P hadj hQ I hG hz hx₀ hx₀Q hx₀P hyA hyC
  by_cases hyQ : y ∈ leechQ s
  · exact ⟨y, hyA, hyQ, hyP⟩
  · obtain ⟨x, hx, hxQ, hxy, hxyA⟩ := exists_adj_of_not_mem_leechQ I hG hs hyA
      (Subgroup.mem_centralizer_singleton_iff.mpr hys) hyQ
    have hne : y ≠ x := fun e => hyQ (e ▸ hxQ)
    refine ⟨x, hx, hxQ, hadj y x hyA hx hyP hne ?_⟩
    rw [← hxy]
    exact hxyA

end Closure

end ASegConn

end CFSG.Monster.GMS
