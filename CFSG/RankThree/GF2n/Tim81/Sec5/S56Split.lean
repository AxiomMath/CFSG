module

public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaPlanes
import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55
import CFSG.GroupTheory.RankOneQuotient

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld
open CFSG.Timmesfeld.ARS.Opposite
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

private theorem exists_pow_three_eq_one_of_mem_utri {X : Type*} [Group X] {F : Type}
    [Field F] [CharP F 2] {π : X →* SL(2, F)} {A B : Subgroup X}
    (hA : A.map π = utri F) (hB : B.map π = ltri F) {a : X} (ha : a ∈ A)
    (ha1 : π a ≠ 1) :
    ∃ b ∈ B, π b ≠ 1 ∧ π ((a * b) ^ 3) = 1 := by
  have hma : π a ∈ utri F := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem π ha
  obtain ⟨s, hs⟩ := mem_utri_iff.mp hma
  have hs0 : s ≠ 0 := fun h => ha1 (by rw [hs, h, utriElt_zero])
  have hmb : ltriElt s⁻¹ ∈ B.map π := by
    rw [hB]
    exact ltriElt_mem_ltri s⁻¹
  obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp hmb
  refine ⟨b, hb, ?_, ?_⟩
  · rw [hbπ]
    exact ltriElt_ne_one (inv_ne_zero hs0)
  · rw [map_pow, map_mul, hs, hbπ]
    exact pow_three_utriElt_mul_ltriElt (mul_inv_cancel₀ hs0)

private theorem exists_pow_three_eq_one_of_mem_ltri {X : Type*} [Group X] {F : Type}
    [Field F] [CharP F 2] {π : X →* SL(2, F)} {A B : Subgroup X}
    (hA : A.map π = utri F) (hB : B.map π = ltri F) {b : X} (hb : b ∈ B)
    (hb1 : π b ≠ 1) :
    ∃ a ∈ A, π a ≠ 1 ∧ π ((a * b) ^ 3) = 1 := by
  have hmb : π b ∈ ltri F := by
    rw [← hB]
    exact Subgroup.mem_map_of_mem π hb
  obtain ⟨t, ht⟩ := mem_ltri_iff.mp hmb
  have ht0 : t ≠ 0 := fun h => hb1 (by rw [ht, h, ltriElt_zero])
  have hma : utriElt t⁻¹ ∈ A.map π := by
    rw [hA]
    exact utriElt_mem_utri t⁻¹
  obtain ⟨a, ha, haπ⟩ := Subgroup.mem_map.mp hma
  refine ⟨a, ha, ?_, ?_⟩
  · rw [haπ]
    exact utriElt_ne_one (inv_ne_zero ht0)
  · rw [map_pow, map_mul, haπ, ht]
    exact pow_three_utriElt_mul_ltriElt (inv_mul_cancel₀ ht0)

private theorem map_ne_one_of_inf_eq_bot {X K R : Subgroup G} {Y : Type*} [Group Y]
    {π : ↥X →* Y} (hker : π.ker = R.subgroupOf X) (hKR : K ⊓ R = ⊥) {x : ↥X}
    (hx : (x : G) ∈ K) (hx1 : x ≠ 1) : π x ≠ 1 := by
  intro h
  have hxker : x ∈ π.ker := MonoidHom.mem_ker.mpr h
  rw [hker] at hxker
  have hxR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hxker
  have hxbot : (x : G) ∈ (⊥ : Subgroup G) := hKR ▸ Subgroup.mem_inf.mpr ⟨hx, hxR⟩
  exact hx1 (Subtype.ext (Subgroup.mem_bot.mp hxbot))

private theorem Sec5Hyp.mem_centralizer_of_commute_mul (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V)
    {a b p : G} (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1) (hp : p ∈ Pc M V)
    (hcomm : a * b * p = p * (a * b)) :
    p ∈ Subgroup.centralizer (U' : Set G) := by
  have ha2 : a * a = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU a (Subgroup.mem_sup_left ha)
  have ha_inv : a⁻¹ = a := (inv_eq_iff_mul_eq_one).mpr ha2
  have hbp : b * p * b⁻¹ = a * p * a := by
    have h1 : b * p = a * p * a * b := by
      have h := congrArg (fun z => a * z) hcomm
      calc b * p = (a * a) * b * p := by rw [ha2, one_mul]
        _ = a * (a * b * p) := by group
        _ = a * (p * (a * b)) := h
        _ = a * p * a * b := by group
    have h2 := congrArg (fun z => z * b⁻¹) h1
    simpa [mul_assoc] using h2
  have hf_eq : ⁅b, p⁆ = ⁅a, p⁆ := by
    rw [commutatorElement_def, commutatorElement_def, hbp, ha_inv]
  have hfE' : ⁅b, p⁆ ∈ ⁅Pc M V, U'⁆ := by
    have h := Subgroup.commutator_mem_commutator (H₁ := U') (H₂ := Pc M V) hb hp
    rwa [Subgroup.commutator_comm U' (Pc M V)] at h
  have hfE : ⁅b, p⁆ ∈ ⁅Pc M V, U⁆ := by
    have h : ⁅a, p⁆ ∈ ⁅U, Pc M V⁆ :=
      Subgroup.commutator_mem_commutator (H₁ := U) (H₂ := Pc M V) ha hp
    rw [Subgroup.commutator_comm U (Pc M V)] at h
    rwa [hf_eq]
  have hfP : ⁅b, p⁆ ∈ Pc M V := hS.commutator_le_Pc hU hfE
  have hfC : ⁅b, p⁆ ∈ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hS.mul_comm_of_mem_sup_commutator hU (⁅b, p⁆) (Subgroup.mem_sup_right hfE) e
      (Subgroup.mem_sup_right he)).symm
  have hfV : ⁅b, p⁆ ∈ V := by
    have hmem : ⁅b, p⁆ ∈ ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
        ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) :=
      Subgroup.mem_inf.mpr ⟨hfE', Subgroup.mem_inf.mpr ⟨hfP, hfC⟩⟩
    rwa [hcap] at hmem
  have hpbV : ⁅p, b⁆ ∈ V := by
    rw [← commutatorElement_inv]
    exact V.inv_mem hfV
  exact hS.mem_centralizer_of_commutator_mem hU' hb hb1 hp hpbV

private theorem Sec5Hyp.eq_conj_inv_of_mem_conj (hS : Sec5Hyp M V) {U₁ : Subgroup G}
    (hU₁ : U₁ ∈ sigmaSet M V) {x y r : G} (hr : r ∈ Pc M V) (hxM : x ∈ M)
    (hx : x ∈ U₁) (hy : y ∈ conjSubgroup r U₁) (hc : y * x ∈ Pc M V) :
    y = r * x⁻¹ * r⁻¹ := by
  have hyU : r⁻¹ * y * r ∈ U₁ := mem_conjSubgroup.mp hy
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer (Pc M V : Set G) :=
    (Subgroup.normalizer (Pc M V : Set G)).inv_mem
      (hS.toRootHyp.toHyp.le_normalizer_Pc hxM)
  have hconjP : x⁻¹ * r * x ∈ Pc M V := by
    have h := (Subgroup.mem_normalizer_iff.mp hxinvN r).mp hr
    simpa using h
  have hmemP : (r⁻¹ * y * r) * x ∈ Pc M V := by
    have heq : (r⁻¹ * y * r) * x = r⁻¹ * (y * x) * (x⁻¹ * r * x) := by group
    rw [heq]
    exact (Pc M V).mul_mem ((Pc M V).mul_mem ((Pc M V).inv_mem hr) hc) hconjP
  have hmemU : (r⁻¹ * y * r) * x ∈ U₁ := U₁.mul_mem hyU hx
  have hbot : (r⁻¹ * y * r) * x = 1 := by
    have hmem : (r⁻¹ * y * r) * x ∈ U₁ ⊓ Pc M V :=
      Subgroup.mem_inf.mpr ⟨hmemU, hmemP⟩
    rw [hS.inf_Pc_eq_bot hU₁] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hu : r⁻¹ * y * r = x⁻¹ := by
    have h := congrArg (fun z => z * x⁻¹) hbot
    simpa [mul_assoc] using h
  have h2 := congrArg (fun z => r * z * r⁻¹) hu
  simpa [mul_assoc] using h2

private theorem Sec5Hyp.exists_eq_commutator_of_pow_three_mem (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V) {a b : G}
    (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1) (hab : (a * b) ^ 3 ∈ Pc M V) :
    ∃ r ∈ Pc M V, (a * b) ^ 3 = ⁅r, b * a * b⁻¹⁆ := by
  obtain ⟨r, hrP, hconj⟩ :=
    hS.exists_conj_eq_conj_of_pow_three_mem hU hU' ha hb hb1 hab
  have haM : a ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 ha
  have hbM : b ∈ M := (hS.le_M_of_mem_sigmaSet hU').1 hb
  have hU₁ : conjSubgroup b U ∈ sigmaSet M V := hS.conj_mem_sigmaSet hbM hU
  have ha2 : a * a = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU a (Subgroup.mem_sup_left ha)
  have hb2 : b * b = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU' b (Subgroup.mem_sup_left hb)
  have ha_inv : a⁻¹ = a := (inv_eq_iff_mul_eq_one).mpr ha2
  have hb_inv : b⁻¹ = b := (inv_eq_iff_mul_eq_one).mpr hb2
  have hx1U : b * a * b⁻¹ ∈ conjSubgroup b U := by
    rw [mem_conjSubgroup, show b⁻¹ * (b * a * b⁻¹) * b = a by group]
    exact ha
  have hx2U : a * b * a⁻¹ ∈ conjSubgroup a U' := by
    rw [mem_conjSubgroup, show a⁻¹ * (a * b * a⁻¹) * a = b by group]
    exact hb
  have hx2r : a * b * a⁻¹ ∈ conjSubgroup r (conjSubgroup b U) := by
    have h := hx2U
    rw [hconj] at h
    exact h
  have hx1M : b * a * b⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hbM haM) (M.inv_mem hbM)
  have hprod : (a * b * a⁻¹) * (b * a * b⁻¹) = (a * b) ^ 3 := by
    rw [ha_inv, hb_inv, pow_three]
    group
  have hc : (a * b * a⁻¹) * (b * a * b⁻¹) ∈ Pc M V := by
    rw [hprod]
    exact hab
  have hx2eq : a * b * a⁻¹ = r * (b * a * b⁻¹)⁻¹ * r⁻¹ :=
    hS.eq_conj_inv_of_mem_conj hU₁ hrP hx1M hx1U hx2r hc
  have hx1sq : (b * a * b⁻¹) * (b * a * b⁻¹) = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU₁ (b * a * b⁻¹) (Subgroup.mem_sup_left hx1U)
  have hx1inv : (b * a * b⁻¹)⁻¹ = b * a * b⁻¹ := (inv_eq_iff_mul_eq_one).mpr hx1sq
  refine ⟨r, hrP, ?_⟩
  calc (a * b) ^ 3 = (a * b * a⁻¹) * (b * a * b⁻¹) := hprod.symm
    _ = (r * (b * a * b⁻¹)⁻¹ * r⁻¹) * (b * a * b⁻¹) := by rw [hx2eq]
    _ = r * (b * a * b⁻¹)⁻¹ * r⁻¹ * (b * a * b⁻¹) := rfl
    _ = ⁅r, (b * a * b⁻¹)⁻¹⁆ := by
          rw [commutatorElement_def]
          group
    _ = ⁅r, b * a * b⁻¹⁆ := by rw [hx1inv]

private theorem Sec5Hyp.pow_three_mem_commutator (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V)
    {a b : G} (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1) (hab : (a * b) ^ 3 ∈ Pc M V) :
    (a * b) ^ 3 ∈ ⁅Pc M V, U⁆ ∧
      (a * b) ^ 3 ∈ Pc M V ⊓
        Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) := by
  have hbM : b ∈ M := (hS.le_M_of_mem_sigmaSet hU').1 hb
  have hcC : (a * b) ^ 3 ∈ Subgroup.centralizer (U' : Set G) := by
    refine hS.mem_centralizer_of_commute_mul hU hU' hcap ha hb hb1 hab ?_
    exact (Commute.self_pow (a * b) 3).eq
  obtain ⟨r, hrP, hr_eq⟩ :=
    hS.exists_eq_commutator_of_pow_three_mem hU hU' ha hb hb1 hab
  have hbC : b⁻¹ * r * b ∈ Pc M V := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (hS.toRootHyp.toHyp.le_normalizer_Pc (M.inv_mem hbM)) r).mp hrP
    simpa using h
  have hconj_c : b⁻¹ * (a * b) ^ 3 * b = ⁅b⁻¹ * r * b, a⁆ := by
    rw [hr_eq, commutatorElement_def, commutatorElement_def]
    group
  have hc_eq : (a * b) ^ 3 = b⁻¹ * (a * b) ^ 3 * b := by
    have hbc : b * (a * b) ^ 3 = (a * b) ^ 3 * b :=
      Subgroup.mem_centralizer_iff.mp hcC b hb
    calc (a * b) ^ 3 = b⁻¹ * (b * (a * b) ^ 3) := by group
      _ = b⁻¹ * ((a * b) ^ 3 * b) := by rw [hbc]
      _ = b⁻¹ * (a * b) ^ 3 * b := by group
  have hc_comm : (a * b) ^ 3 = ⁅b⁻¹ * r * b, a⁆ := hc_eq.trans hconj_c
  have hcE : (a * b) ^ 3 ∈ ⁅Pc M V, U⁆ := by
    rw [hc_comm]
    exact Subgroup.commutator_mem_commutator (H₁ := Pc M V) (H₂ := U) hbC ha
  have hcCE' : (a * b) ^ 3 ∈ Pc M V ⊓
      Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) := by
    have hmem : (a * b) ^ 3 ∈ Pc M V ⊓ Subgroup.centralizer (U' : Set G) :=
      Subgroup.mem_inf.mpr ⟨hab, hcC⟩
    rwa [hS.Pc_inf_centralizer_eq_commutator hU'] at hmem
  exact ⟨hcE, hcCE'⟩

private theorem Sec5Hyp.pow_three_mem_V (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V)
    {a b : G} (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1) (hab : (a * b) ^ 3 ∈ Pc M V) :
    (a * b) ^ 3 ∈ V := by
  obtain ⟨hcE, hcCE'⟩ := hS.pow_three_mem_commutator hU hU' hcap ha hb hb1 hab
  have hcap' : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U'⁆ : Subgroup G) : Set G)) = V :=
    (hS.cap_symm hU hU').mp hcap
  have hmem : (a * b) ^ 3 ∈ ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U'⁆ : Subgroup G) : Set G)) :=
    Subgroup.mem_inf.mpr ⟨hcE, hcCE'⟩
  rwa [hcap'] at hmem

private theorem Sec5Hyp.conj_eq_of_pow_three_mem (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V)
    {a b : G} (ha : a ∈ U) (hb : b ∈ U') (hb1 : b ≠ 1) (hab : (a * b) ^ 3 ∈ Pc M V) :
    conjSubgroup a U' = conjSubgroup b U := by
  have haM : a ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 ha
  have hbM : b ∈ M := (hS.le_M_of_mem_sigmaSet hU').1 hb
  have hU₁ : conjSubgroup b U ∈ sigmaSet M V := hS.conj_mem_sigmaSet hbM hU
  have hU₂ : conjSubgroup a U' ∈ sigmaSet M V := hS.conj_mem_sigmaSet haM hU'
  have ha2 : a * a = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU a (Subgroup.mem_sup_left ha)
  have hb2 : b * b = 1 :=
    hS.mul_self_eq_one_of_mem_sup_commutator hU' b (Subgroup.mem_sup_left hb)
  have ha_inv : a⁻¹ = a := (inv_eq_iff_mul_eq_one).mpr ha2
  have hb_inv : b⁻¹ = b := (inv_eq_iff_mul_eq_one).mpr hb2
  have hprod : (a * b * a⁻¹) * (b * a * b⁻¹) = (a * b) ^ 3 := by
    rw [ha_inv, hb_inv, pow_three]
    group
  have hx2U : a * b * a⁻¹ ∈ conjSubgroup a U' := by
    rw [mem_conjSubgroup, show a⁻¹ * (a * b * a⁻¹) * a = b by group]
    exact hb
  have hx1U : b * a * b⁻¹ ∈ conjSubgroup b U := by
    rw [mem_conjSubgroup, show b⁻¹ * (b * a * b⁻¹) * b = a by group]
    exact ha
  have hcV : (a * b) ^ 3 ∈ V := hS.pow_three_mem_V hU hU' hcap ha hb hb1 hab
  have hx2sup : a * b * a⁻¹ ∈ conjSubgroup b U ⊔ V := by
    have hx2eq : a * b * a⁻¹ = (a * b) ^ 3 * (b * a * b⁻¹)⁻¹ := by
      rw [← hprod]
      group
    rw [hx2eq]
    have h := Subgroup.mul_mem_sup (S := V) (T := conjSubgroup b U) hcV
      ((conjSubgroup b U).inv_mem hx1U)
    rwa [sup_comm] at h
  have hx2ne : a * b * a⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have h1 : a⁻¹ * (a * b * a⁻¹) * a = b := by group
    rw [h] at h1
    simpa using h1.symm
  have hne : conjSubgroup a U' ⊓ (conjSubgroup b U ⊔ V) ≠ ⊥ := by
    intro hbot
    have hmem : a * b * a⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hx2U, hx2sup⟩
    exact hx2ne (Subgroup.mem_bot.mp hmem)
  have hU₂ω : conjSubgroup a U' ∈ omegaSet V := by
    obtain ⟨k, hU'k, -⟩ := hU'
    exact Tim79a.mem_omegaOf.mpr
      ⟨a * k, trivial, by rw [hU'k, conjSubgroup_conjSubgroup]⟩
  have hU₂V : conjSubgroup a U' ≠ V := ne_of_mem_sigmaSet hS.toRootHyp hU₂
  exact hS.stmt54 (conjSubgroup b U) hU₁ (conjSubgroup a U') hU₂ω hU₂V hne

private theorem Sec5Hyp.exists_conjSub_eq_of_mem_utri (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V)
    {F : Type} [Field F] [CharP F 2] {π : ↥(U ⊔ U') →* SL(2, F)}
    (hker : π.ker = (Pc M V).subgroupOf (U ⊔ U'))
    (hπU : (U.subgroupOf (U ⊔ U')).map π = utri F)
    (hπU' : (U'.subgroupOf (U ⊔ U')).map π = ltri F)
    {a : G} (ha : a ∈ U) (ha1 : π ⟨a, Subgroup.mem_sup_left ha⟩ ≠ 1) :
    ∃ b ∈ U', b ≠ 1 ∧ conjSubgroup b U = conjSubgroup a U' := by
  obtain ⟨b, hb, hpb1, hpow⟩ :=
    exists_pow_three_eq_one_of_mem_utri (A := U.subgroupOf (U ⊔ U'))
      (B := U'.subgroupOf (U ⊔ U')) hπU hπU' (Subgroup.mem_subgroupOf.mpr ha) ha1
  have hbG : (b : G) ∈ U' := Subgroup.mem_subgroupOf.mp hb
  have hb1 : (b : G) ≠ 1 := by
    intro h
    apply hpb1
    have hb_eq : b = 1 := Subtype.ext (by simpa using h)
    rw [hb_eq, map_one]
  have hab : (a * (b : G)) ^ 3 ∈ Pc M V := by
    have hmem : ((⟨a, Subgroup.mem_sup_left ha⟩ : ↥(U ⊔ U')) * b) ^ 3 ∈ π.ker :=
      MonoidHom.mem_ker.mpr hpow
    rw [hker] at hmem
    have hmem' : ((((⟨a, Subgroup.mem_sup_left ha⟩ : ↥(U ⊔ U')) * b) ^ 3 :
        ↥(U ⊔ U')) : G) ∈ Pc M V := Subgroup.mem_subgroupOf.mp hmem
    simpa using hmem'
  have heq := hS.conj_eq_of_pow_three_mem hU hU' hcap ha hbG hb1 hab
  exact ⟨(b : G), hbG, hb1, heq.symm⟩

private theorem Sec5Hyp.exists_conjSub_eq_of_mem_ltri (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V)
    {F : Type} [Field F] [CharP F 2] {π : ↥(U ⊔ U') →* SL(2, F)}
    (hker : π.ker = (Pc M V).subgroupOf (U ⊔ U'))
    (hπU : (U.subgroupOf (U ⊔ U')).map π = utri F)
    (hπU' : (U'.subgroupOf (U ⊔ U')).map π = ltri F)
    {b : G} (hb : b ∈ U') (hb1 : π ⟨b, Subgroup.mem_sup_right hb⟩ ≠ 1) :
    ∃ a ∈ U, a ≠ 1 ∧ conjSubgroup a U' = conjSubgroup b U := by
  obtain ⟨a, ha, hpa1, hpow⟩ :=
    exists_pow_three_eq_one_of_mem_ltri (A := U.subgroupOf (U ⊔ U'))
      (B := U'.subgroupOf (U ⊔ U')) hπU hπU' (Subgroup.mem_subgroupOf.mpr hb) hb1
  have haG : (a : G) ∈ U := Subgroup.mem_subgroupOf.mp ha
  have ha1 : (a : G) ≠ 1 := by
    intro h
    apply hpa1
    have ha_eq : a = 1 := Subtype.ext (by simpa using h)
    rw [ha_eq, map_one]
  have hbm : b ≠ 1 := by
    intro h
    apply hb1
    have hb_eq : (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(U ⊔ U')) = 1 :=
      Subtype.ext (by simpa using h)
    rw [hb_eq, map_one]
  have hab : ((a : G) * b) ^ 3 ∈ Pc M V := by
    have hmem : (a * (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(U ⊔ U'))) ^ 3 ∈ π.ker :=
      MonoidHom.mem_ker.mpr hpow
    rw [hker] at hmem
    have hmem' : (((a * (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(U ⊔ U'))) ^ 3 :
        ↥(U ⊔ U')) : G) ∈ Pc M V := Subgroup.mem_subgroupOf.mp hmem
    simpa using hmem'
  have heq := hS.conj_eq_of_pow_three_mem hU hU' hcap haG hb hbm hab
  exact ⟨(a : G), haG, ha1, heq⟩

private theorem Sec5Hyp.opposite_of_cap (hS : Sec5Hyp M V)
    {U U' : Subgroup G} (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hcap : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, U⁆ : Subgroup G) : Set G)) = V)
    {F : Type} [Field F] [CharP F 2] (π : ↥(U ⊔ U') →* SL(2, F))
    (hker : π.ker = (Pc M V).subgroupOf (U ⊔ U'))
    (hπU : (U.subgroupOf (U ⊔ U')).map π = utri F)
    (hπU' : (U'.subgroupOf (U ⊔ U')).map π = ltri F) (hut : utri F ≠ ltri F) :
    CFSG.Timmesfeld.ARS.Opposite U U' := by
  refine ⟨?_, ?_, ?_⟩
  · intro hUU'
    subst hUU'
    apply hut
    rw [hπU] at hπU'
    exact hπU'
  · intro a ha ha1
    have haX : a ∈ U ⊔ U' := Subgroup.mem_sup_left ha
    have hx1 : (⟨a, haX⟩ : ↥(U ⊔ U')) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hpa1 : π ⟨a, haX⟩ ≠ 1 :=
      map_ne_one_of_inf_eq_bot (K := U) (R := Pc M V) hker (hS.inf_Pc_eq_bot hU) ha hx1
    obtain ⟨b, hb, hb1, heq⟩ :=
      hS.exists_conjSub_eq_of_mem_utri hU hU' hcap hker hπU hπU' ha hpa1
    refine ⟨b, hb, hb1, ?_⟩
    show conjSubgroup b U = conjSubgroup a U'
    exact heq
  · intro b hb hb1
    have hbX : b ∈ U ⊔ U' := Subgroup.mem_sup_right hb
    have hx1 : (⟨b, hbX⟩ : ↥(U ⊔ U')) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
    have hpb1 : π ⟨b, hbX⟩ ≠ 1 :=
      map_ne_one_of_inf_eq_bot (K := U') (R := Pc M V) hker (hS.inf_Pc_eq_bot hU') hb hx1
    obtain ⟨a, ha, ha1, heq⟩ :=
      hS.exists_conjSub_eq_of_mem_ltri hU hU' hcap hker hπU hπU' hb hpb1
    refine ⟨a, ha, ha1, ?_⟩
    show conjSubgroup a U' = conjSubgroup b U
    exact heq

theorem Sec5Hyp.stmt56_of_stmt56a (hS : Sec5Hyp M V) (h56a : Sec5.Stmt56a M V) :
    Sec5.Stmt56 M V := by
  classical
  intro U hU U' hU' hcap
  obtain ⟨F, hF, hFin, hChar, π, hsurj, hker, hcardF, hπU, hπU'⟩ :=
    h56a U hU U' hU' hcap
  letI := hF
  letI := hFin
  letI := hChar
  have hut : utri F ≠ ltri F := by
    rw [Tim77.utri_eq_upperUnipotent, Sec2.ltri_eq_lowerUnipotent]
    exact RankOne.upperUnipotent_ne_lowerUnipotent F
  have hopp : CFSG.Timmesfeld.ARS.Opposite U U' :=
    hS.opposite_of_cap hU hU' hcap π hker hπU hπU' hut
  have hsqU : ∀ a ∈ U, a * a = 1 := fun a ha =>
    hS.mul_self_eq_one_of_mem_sup_commutator hU a (Subgroup.mem_sup_left ha)
  have hR1 : IsElemAbRankOne (U.subgroupOf (U ⊔ U')) (U'.subgroupOf (U ⊔ U')) :=
    hopp.isElemAbRankOne_of_mul_self hsqU
  have hAB : (U.subgroupOf (U ⊔ U')).map π ≠ (U'.subgroupOf (U ⊔ U')).map π := by
    rw [hπU, hπU']
    exact hut
  have hPc2 : IsPGroup 2 π.ker := by
    rw [hker]
    exact ((inSubgroup_pCore_two M).1.to_le
      (inf_le_left : Pc M V ≤ inSubgroup (pCore 2) M)).comap_subtype (K := U ⊔ U')
  have hbot : π.ker = ⊥ := hR1.ker_eq_bot_of_isPGroup hAB hPc2
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hbot
  let φ : ↥(U ⊔ U') ≃* SL(2, F) := MulEquiv.ofBijective π ⟨hinj, hsurj⟩
  have hφ : φ.toMonoidHom = π :=
    MonoidHom.ext fun x => MulEquiv.ofBijective_apply π ⟨hinj, hsurj⟩ x
  obtain ⟨g, hUg, -⟩ := hU
  have hcardU : Nat.card U = Nat.card V := by
    rw [hUg, card_conjSubgroup]
  refine ⟨F, hF, hFin, hChar, φ, ?_, ?_, ?_⟩
  · rw [hcardF, hcardU]
  · rw [hφ]
    exact hπU
  · rw [hφ]
    exact hπU'

end CFSG.RankThree.GF2n.Tim81

end
