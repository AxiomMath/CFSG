module

public import CFSG.Sporadic.HNOddCore.OddC
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2089
public import Certificates.Certificate2091
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Equiv Equiv.Perm
open CFSG.ComponentClassification.SmallLocal

theorem oddCore_bot_of_bijective {G K : Type*} [Group G] [Group K] {A : Subgroup G}
    {B : Subgroup K} (f : A →* B) (hf : Function.Bijective f) (h : CFSG.oddCore B = ⊥) :
    CFSG.oddCore A = ⊥ :=
  oddCore_bot_of_mulEquiv (MulEquiv.ofBijective f hf) h

theorem oddCore_bot_of_bijective' {G K : Type*} [Group G] [Group K] {A : Subgroup G}
    {B : Subgroup K} (f : A →* B) (hf : Function.Bijective f) (h : CFSG.oddCore A = ⊥) :
    CFSG.oddCore B = ⊥ :=
  oddCore_bot_of_mulEquiv (MulEquiv.ofBijective f hf).symm h

theorem sub_comm_of_coe {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup H} {a b : K}
    (h : (a : H) * (b : H) = (b : H) * (a : H)) : a * b = b * a :=
  Subtype.ext (by simpa using h)

theorem mulEquiv_comm_of_coe {G0 : Type*} [Group G0] {J : Subgroup G0} {V : Subgroup J}
    {P : Type*} [Group P] (θ : V ≃* P) {a b : V} (h : (a : J) * (b : J) = (b : J) * (a : J)) :
    θ a * θ b = θ b * θ a := by
  rw [← map_mul, ← map_mul, sub_comm_of_coe h]

theorem jR_mem_centralizer_iff
    (g s : JH) :
    jR g ∈ Subgroup.centralizer {jR s} ↔ g ∈ Subgroup.centralizer {s} := by
  rw [sub_mem_centralizer_iff, sub_mem_centralizer_iff, ← map_mul, ← map_mul]
  exact jR_injective.eq_iff

@[expose] def cjHomG (s : JH) :
    Subgroup.centralizer {s} →* jR.range.subgroupOf (Subgroup.centralizer {jR s}) :=
  ((jR.comp (Subgroup.centralizer {s}).subtype).codRestrict (Subgroup.centralizer {jR s})
    fun g => (jR_mem_centralizer_iff g.1 s).2 g.2).codRestrict _ fun g => ⟨g, rfl⟩

theorem cjHomG_bijective
    (s : JH) : Function.Bijective (cjHomG s) := by
  constructor
  · intro a b h
    have := congrArg (fun y : jR.range.subgroupOf (Subgroup.centralizer {jR s}) =>
      ((y : Subgroup.centralizer {jR s}) : RH)) h
    exact Subtype.ext (jR_injective this)
  · rintro ⟨⟨r, hr⟩, ⟨g, hg⟩⟩
    have hg' : jR g ∈ Subgroup.centralizer {jR s} := by
      have e : jR g = r := hg
      rw [e]
      exact hr
    refine ⟨⟨g, (jR_mem_centralizer_iff g s).1 hg'⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg

theorem sq_mem_range_jR
    (r : RH) : r ^ 2 ∈ jR.range := by
  rw [pow_two]
  by_cases hout : IsOuter r
  · obtain ⟨g, hg⟩ := exists_of_not_isOuter (not_isOuter_mul hout hout)
    exact ⟨g, hg.symm⟩
  · obtain ⟨g, rfl⟩ := exists_of_not_isOuter hout
    exact ⟨g * g, map_mul jR g g⟩

theorem subgroupOf_range_normal
    (s : JH) :
    (jR.range.subgroupOf (Subgroup.centralizer {jR s})).Normal := by
  have := range_jR_normal
  infer_instance

theorem oddCore_CJ_of_CR {s : JH}
    (h : CFSG.oddCore (Subgroup.centralizer ({jR s} : Set RH)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({s} : Set JH)) = ⊥ := by
  have := subgroupOf_range_normal s
  exact oddCore_bot_of_bijective _ (cjHomG_bijective s) (oddCore_normal_bot h _)

theorem oddCore_CR_of_CJ
    {s : JH} (h : CFSG.oddCore (Subgroup.centralizer ({s} : Set JH)) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({jR s} : Set RH)) = ⊥ := by
  have := subgroupOf_range_normal s
  refine oddCore_bot_of_sq_mem (K := jR.range.subgroupOf (Subgroup.centralizer {jR s}))
    (fun c => ?_) ?_
  · rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact sq_mem_range_jR c
  · exact oddCore_bot_of_bijective' _ (cjHomG_bijective s) h

theorem CR_c_le_RV :
    Subgroup.centralizer {cR} ≤ RV := by
  intro r hr
  rcases (mem_centralizer_cR_iff r).1 hr with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact (jR_mem_RV_iff g).2 (CJc_le_HJ hg)
  · exact (jR_mul_cR_mem_RV_iff g).2 (CJc_le_HJ hg)

@[expose] def crcHom :
    Subgroup.centralizer {cR} →*
    ↥((⊤ : Subgroup (Perm (Fin 12))) ⊓
      Subgroup.centralizer ({swap (0 : Fin 12) 1} : Set (Perm (Fin 12)))) :=
  (thetaRHom.comp (Subgroup.inclusion CR_c_le_RV)).codRestrict _ fun r => by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← thetaR_apply]
    have hr := sub_mem_centralizer_iff.1 r.2
    have e := mulEquiv_comm_of_coe thetaR (a := ⟨r, CR_c_le_RV r.2⟩) (b := t1V) hr
    rw [thetaR_cR] at e
    exact e

theorem crcHom_val
    (r : Subgroup.centralizer {cR}) :
    ((crcHom r : Perm (Fin 12))) = thetaR ⟨r, CR_c_le_RV r.2⟩ := rfl

theorem crcHom_bijective :
    Function.Bijective crcHom := by
  constructor
  · intro a b hab
    have e1 : thetaR ⟨a, CR_c_le_RV a.2⟩ = thetaR ⟨b, CR_c_le_RV b.2⟩ := by
      rw [← crcHom_val, ← crcHom_val, hab]
    have e2 := thetaR.injective e1
    have e3 := Subtype.ext_iff.1 e2
    dsimp only at e3
    exact Subtype.ext e3
  · rintro ⟨σ, hσ⟩
    obtain ⟨-, hσC⟩ := Subgroup.mem_inf.1 hσ
    obtain ⟨r, hθ⟩ : ∃ r : RV, thetaR r = σ := ⟨thetaR.symm σ, MulEquiv.apply_symm_apply _ _⟩
    have hcomm : r * t1V = t1V * r := by
      apply thetaR.injective
      rw [map_mul, map_mul, hθ, thetaR_cR]
      exact Subgroup.mem_centralizer_singleton_iff.1 hσC
    have hmem := sub_mem_centralizer_of_coe hcomm
    refine ⟨⟨r, hmem⟩, Subtype.ext ?_⟩
    rw [crcHom_val]
    exact hθ

theorem oddCore_CR_c :
    CFSG.oddCore (Subgroup.centralizer ({cR} : Set RH)) = ⊥ := by
  have h2 : swap (0 : Fin 12) 1 ^ 2 = 1 := by rw [pow_two, swap_mul_self]
  have h1 : swap (0 : Fin 12) 1 ≠ 1 := by decide
  have hfix : Nat.card {ω // swap (0 : Fin 12) 1 ω = ω} ≠ 3 := by
    have := card_fixed_of_type swap01_type
    omega
  exact oddCore_bot_of_bijective _ crcHom_bijective
    ((ComponentClassification.SymmetricLocal.involution_permutation_centralizer_odd_core
      le_top (orderOf_eq_prime h2 h1)).1 hfix)

theorem oddCore_CR_t4 :
    CFSG.oddCore (Subgroup.centralizer ({jR t4J} : Set RH)) = ⊥ :=
  oddCore_bot_of_selfCentralizing Q4_normal Q4_isPGroup centralizer_Q4_le

theorem oddCore_CR_t2 :
    CFSG.oddCore (Subgroup.centralizer ({jR t2J} : Set RH)) = ⊥ :=
  oddCore_CR_of_CJ oddCore_C2

end CFSG.Sporadic.HNOddCore
