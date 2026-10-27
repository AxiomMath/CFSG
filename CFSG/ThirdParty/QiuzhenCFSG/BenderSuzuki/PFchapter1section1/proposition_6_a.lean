module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

universe u v

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 6(a)
-/

private theorem hypothesisA1_H_decomp
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t h : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hh : h ∈ H) :
    ∃ q : G, q ∈ Q ∧ ∃ d : G, d ∈ D ∧ q * d = h := by
  classical
  let QH : Subgroup H := Q.subgroupOf H
  let DH : Subgroup H := D.subgroupOf H
  let hH : H := ⟨h, hh⟩
  have hQH_top : QH ⊔ DH = ⊤ := by
    calc
      QH ⊔ DH = (Q ⊔ D).subgroupOf H := by
        exact (Subgroup.subgroupOf_sup hA1.Q_le_H hA1.D_le_H).symm
      _ = H.subgroupOf H := by rw [hA1.Q_sup_D]
      _ = ⊤ := (Subgroup.subgroupOf_eq_top).2 le_rfl
  haveI : QH.Normal := hA1.Q_normal_in_H
  have hhH : hH ∈ QH ⊔ DH := by
    rw [hQH_top]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left (s := QH) (t := DH) (x := hH)).mp hhH with
    ⟨qH, hqH, dH, hdH, hmul⟩
  refine ⟨qH, ?_, dH, ?_, ?_⟩
  · change qH ∈ Q.subgroupOf H
    exact hqH
  · change dH ∈ D.subgroupOf H
    exact hdH
  · exact congrArg Subtype.val hmul

private theorem hypothesisA1_H_decomp_unique
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t q₁ d₁ q₂ d₂ : G}
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hq₁ : q₁ ∈ Q) (hd₁ : d₁ ∈ D) (hq₂ : q₂ ∈ Q) (hd₂ : d₂ ∈ D)
    (hmul : q₁ * d₁ = q₂ * d₂) :
    q₁ = q₂ ∧ d₁ = d₂ := by
  classical
  have hqd_eq : q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
    have haux : q₂⁻¹ * q₁ * d₁ = d₂ := by
      calc
        q₂⁻¹ * q₁ * d₁ = q₂⁻¹ * (q₁ * d₁) := by group
        _ = q₂⁻¹ * (q₂ * d₂) := by rw [hmul]
        _ = d₂ := by group
    calc
      q₂⁻¹ * q₁ = (q₂⁻¹ * q₁ * d₁) * d₁⁻¹ := by group
      _ = d₂ * d₁⁻¹ := by rw [haux]
  have hqd_mem : q₂⁻¹ * q₁ ∈ Q ⊓ D := by
    constructor
    · exact Q.mul_mem (Q.inv_mem hq₂) hq₁
    · rw [hqd_eq]
      exact D.mul_mem hd₂ (D.inv_mem hd₁)
  have hqd_one : q₂⁻¹ * q₁ = 1 := by
    have hbot : Q ⊓ D = ⊥ := hA1.Q_disjoint_D.eq_bot
    have : q₂⁻¹ * q₁ ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hqd_mem
    simpa using this
  have hq : q₁ = q₂ := by
    calc
      q₁ = q₂ * (q₂⁻¹ * q₁) := by group
      _ = q₂ := by simp [hqd_one]
  have hd : d₁ = d₂ := by
    have hmul' : q₂ * d₁ = q₂ * d₂ := by
      simpa [hq] using hmul
    exact mul_left_cancel hmul'
  exact ⟨hq, hd⟩

private theorem hypothesisA1_Q_conj_mem_of_mem_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t h q : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hh : h ∈ H) (hq : q ∈ Q) :
    h * q * h⁻¹ ∈ Q := by
  classical
  let hH : H := ⟨h, hh⟩
  let qH : H := ⟨q, hA1.Q_le_H hq⟩
  have hqH : qH ∈ Q.subgroupOf H := by
    simpa [qH, Subgroup.mem_subgroupOf] using hq
  have hmem := hA1.Q_normal_in_H.conj_mem qH hqH hH
  simpa [hH, qH, Subgroup.mem_subgroupOf, mul_assoc] using hmem

private theorem hypothesisA1_base_ne_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) :
    base ≠ t⁻¹ • base := by
  intro h
  have ht_inv_H : t⁻¹ ∈ H := by
    have ht_inv_stab : t⁻¹ ∈ MulAction.stabilizer G base := by
      exact h.symm
    simpa [hHbase] using ht_inv_stab
  have htH : t ∈ H := by
    simpa using H.inv_mem ht_inv_H
  exact hA1.t_not_mem_H htH

private theorem hypothesisA1_mem_rightConjugate_H_of_fixes_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t x : G}
    (_hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base)
    (hx : x • (t⁻¹ • base) = t⁻¹ • base) :
    x ∈ rightConjugate H t := by
  have hstab : x ∈ MulAction.stabilizer G (t⁻¹ • base) := hx
  have hconj :
      rightConjugate H t = MulAction.stabilizer G (t⁻¹ • base) := by
    rw [hHbase]
    exact rightConjugate_stabilizer base t
  simpa [hconj] using hstab

private theorem hypothesisA1_D_fixes_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) (hd : d ∈ D) :
    d • base = base := by
  have hdH : d ∈ H := hA1.D_le_H hd
  have hdstab : d ∈ MulAction.stabilizer G base := by
    simpa [hHbase] using hdH
  simpa using hdstab

private theorem hypothesisA1_D_fixes_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) (hd : d ∈ D) :
    d • (t⁻¹ • base) = t⁻¹ • base := by
  have hd' : d ∈ H ⊓ rightConjugate H t := by
    simpa [hA1.D_eq] using hd
  have hconj :
      rightConjugate H t = MulAction.stabilizer G (t⁻¹ • base) := by
    rw [hHbase]
    exact rightConjugate_stabilizer base t
  have hdstab : d ∈ MulAction.stabilizer G (t⁻¹ • base) := by
    simpa [hconj] using hd'.2
  simpa using hdstab

private theorem hypothesisA1_rightConjugateElem_mem_D_of_mem_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hd : d ∈ D) :
    rightConjugateElem d t ∈ D := by
  classical
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hd' : d ∈ H ⊓ rightConjugate H t := by
    simpa [hA1.D_eq] using hd
  rw [hA1.D_eq]
  constructor
  · rcases hd'.2 with ⟨h, hhH, hhd⟩
    change t⁻¹ * d * t ∈ H
    rw [← hhd]
    have hcollapse : t⁻¹ * (t⁻¹ * h * t) * t = h := by
      rw [htinv]
      calc
        t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by simp [htt]
    have hcollapse' :
        t⁻¹ * ((MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) h) * t = h := by
      change t⁻¹ * (t⁻¹ * h * (t⁻¹)⁻¹) * t = h
      simpa [inv_inv] using hcollapse
    rw [hcollapse']
    exact hhH
  · refine ⟨d, hd'.1, ?_⟩
    simp [rightConjugateElem]

private theorem hypothesisA1_t_conj_mem_D_of_mem_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hd : d ∈ D) :
    t * d * t⁻¹ ∈ D := by
  have hmem := hypothesisA1_rightConjugateElem_mem_D_of_mem_D (H := H) (Q := Q) hA1 hd
  simpa [rightConjugateElem, hA1.involution_t.inv_eq_self]
    using hmem

private theorem hypothesisA1_rightConjugate_Q_le_rightConjugate_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t q : G}
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hq : q ∈ rightConjugate Q t) :
    q ∈ rightConjugate H t := by
  rcases hq with ⟨q0, hq0Q, rfl⟩
  exact ⟨q0, hA1.Q_le_H hq0Q, rfl⟩

private theorem hypothesisA1_rightConjugate_Q_fixes_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t q : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base)
    (hq : q ∈ rightConjugate Q t) :
    q • (t⁻¹ • base) = t⁻¹ • base := by
  have hqHt : q ∈ rightConjugate H t :=
    hypothesisA1_rightConjugate_Q_le_rightConjugate_H hA1 hq
  have hconj :
      rightConjugate H t = MulAction.stabilizer G (t⁻¹ • base) := by
    rw [hHbase]
    exact rightConjugate_stabilizer base t
  have hstab : q ∈ MulAction.stabilizer G (t⁻¹ • base) := by
    simpa [hconj] using hqHt
  simpa using hstab

private theorem hypothesisA1_D_conj_mem_rightConjugate_Q
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d q : G}
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hd : d ∈ D) (hq : q ∈ rightConjugate Q t) :
    d * q * d⁻¹ ∈ rightConjugate Q t := by
  classical
  rcases hq with ⟨q0, hq0Q, hqeq⟩
  let d0 : G := t * d * t⁻¹
  have hd0D : d0 ∈ D := hypothesisA1_t_conj_mem_D_of_mem_D (H := H) (Q := Q) hA1 hd
  have hd0H : d0 ∈ H := hA1.D_le_H hd0D
  have hconjQ : d0 * q0 * d0⁻¹ ∈ Q :=
    hypothesisA1_Q_conj_mem_of_mem_H hA1 hd0H hq0Q
  refine ⟨d0 * q0 * d0⁻¹, hconjQ, ?_⟩
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  calc
    (MulAut.conj t⁻¹) (d0 * q0 * d0⁻¹) =
        t⁻¹ * (d0 * q0 * d0⁻¹) * (t⁻¹)⁻¹ := rfl
    _ = d * ((MulAut.conj t⁻¹) q0) * d⁻¹ := by
      have htt : t * t = 1 := by
        simpa [pow_two] using hA1.involution_t.sq_eq_one
      simp [d0, htinv, htt, mul_inv_rev, mul_assoc]
      rw [← mul_assoc, htt, one_mul]
    _ = d * q * d⁻¹ := by
      change d * ((MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) q0) * d⁻¹ =
        d * q * d⁻¹
      rw [hqeq]

private theorem hypothesisA1_Q_unique_on_complement
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) :
    ∀ y : Ω, y ≠ base →
      ∃! q : G, q ∈ Q ∧ q • (t⁻¹ • base) = y := by
  classical
  intro y hy_ne_base
  have hbase_ne_beta :
      base ≠ t⁻¹ • base :=
    hypothesisA1_base_ne_t_inv_base hA1 hHbase
  have hbase_ne_y : base ≠ y := by
    exact hy_ne_base.symm
  obtain ⟨h, hh_base, hh_beta⟩ :=
    (MulAction.is_two_pretransitive_iff.mp hA1.two_transitive)
      hbase_ne_beta hbase_ne_y
  have hhH : h ∈ H := by
    have hhstab : h ∈ MulAction.stabilizer G base := by
      simpa using hh_base
    simpa [hHbase] using hhstab
  rcases hypothesisA1_H_decomp hA1 hhH with ⟨q, hqQ, d, hdD, hqd⟩
  have hd_beta : d • (t⁻¹ • base) = t⁻¹ • base :=
    hypothesisA1_D_fixes_t_inv_base hA1 hHbase hdD
  have hq_beta : q • (t⁻¹ • base) = y := by
    calc
      q • (t⁻¹ • base) = (q * d) • (t⁻¹ • base) := by
        simp [mul_smul, hd_beta]
      _ = h • (t⁻¹ • base) := by rw [hqd]
      _ = y := hh_beta
  refine ⟨q, ⟨hqQ, hq_beta⟩, ?_⟩
  intro q' hq'
  have hdiffQ : q⁻¹ * q' ∈ Q := Q.mul_mem (Q.inv_mem hqQ) hq'.1
  have hdiffH : q⁻¹ * q' ∈ H := hA1.Q_le_H hdiffQ
  have hdiff_beta : (q⁻¹ * q') • (t⁻¹ • base) = t⁻¹ • base := by
    calc
      (q⁻¹ * q') • (t⁻¹ • base) =
          q⁻¹ • (q' • (t⁻¹ • base)) := by rw [mul_smul]
      _ = q⁻¹ • y := by rw [hq'.2]
      _ = q⁻¹ • (q • (t⁻¹ • base)) := by rw [hq_beta]
      _ = t⁻¹ • base := by simp [smul_smul]
  have hdiffRight : q⁻¹ * q' ∈ rightConjugate H t :=
    hypothesisA1_mem_rightConjugate_H_of_fixes_t_inv_base hA1 hHbase hdiff_beta
  have hdiffD : q⁻¹ * q' ∈ D := by
    rw [hA1.D_eq]
    exact ⟨hdiffH, hdiffRight⟩
  have hdiff_one : q⁻¹ * q' = 1 := by
    have hmem : q⁻¹ * q' ∈ Q ⊓ D := ⟨hdiffQ, hdiffD⟩
    have := hA1.Q_disjoint_D.le_bot hmem
    simpa using this
  calc
    q' = q * (q⁻¹ * q') := by group
    _ = q := by simp [hdiff_one]

private theorem hypothesisA1_Q_mem_centralizer_of_smul_fixed
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t q : G} {y : Ω}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base)
    (hqQ : q ∈ Q)
    (hy_fixed : y ∈ fixedPointsOfSubgroup G Ω X)
    (hq_beta : q • (t⁻¹ • base) = y) :
    q ∈ Subgroup.centralizer (X : Set G) := by
  classical
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxD : x ∈ D := hX_le_D hx
  have hxH : x ∈ H := hA1.D_le_H hxD
  have hconjQ : x * q * x⁻¹ ∈ Q :=
    hypothesisA1_Q_conj_mem_of_mem_H hA1 hxH hqQ
  have hx_beta : x • (t⁻¹ • base) = t⁻¹ • base :=
    hypothesisA1_D_fixes_t_inv_base hA1 hHbase hxD
  have hx_inv_beta : x⁻¹ • (t⁻¹ • base) = t⁻¹ • base :=
    hypothesisA1_D_fixes_t_inv_base hA1 hHbase (D.inv_mem hxD)
  have hconj_beta : (x * q * x⁻¹) • (t⁻¹ • base) = y := by
    calc
      (x * q * x⁻¹) • (t⁻¹ • base) =
          x • (q • (x⁻¹ • (t⁻¹ • base))) := by simp [mul_smul, mul_assoc]
      _ = x • (q • (t⁻¹ • base)) := by rw [hx_inv_beta]
      _ = x • y := by rw [hq_beta]
      _ = y := hy_fixed x hx
  have hy_ne_base : y ≠ base := by
    intro hybase
    have hq_base : q • base = base := by
      have hqH : q ∈ H := hA1.Q_le_H hqQ
      have hqstab : q ∈ MulAction.stabilizer G base := by
        simpa [hHbase] using hqH
      simpa using hqstab
    have hbeta_eq_base : t⁻¹ • base = base := by
      calc
        t⁻¹ • base = q⁻¹ • (q • (t⁻¹ • base)) := by simp [smul_smul]
        _ = q⁻¹ • y := by rw [hq_beta]
        _ = q⁻¹ • base := by rw [hybase]
        _ = base := by
          have hqinv_base : q⁻¹ • base = base := by
            have hqinvH : q⁻¹ ∈ H := H.inv_mem (hA1.Q_le_H hqQ)
            have hqinvstab : q⁻¹ ∈ MulAction.stabilizer G base := by
              simpa [hHbase] using hqinvH
            exact hqinvstab
          exact hqinv_base
    exact (hypothesisA1_base_ne_t_inv_base hA1 hHbase) hbeta_eq_base.symm
  have hregular := hypothesisA1_Q_unique_on_complement hA1 hHbase y hy_ne_base
  have hconj_eq_q :
      x * q * x⁻¹ = q :=
    hregular.unique ⟨hconjQ, hconj_beta⟩ ⟨hqQ, hq_beta⟩
  calc
    x * q = (x * q * x⁻¹) * x := by group
    _ = q * x := by rw [hconj_eq_q]

private theorem hypothesisA1_CQ_transitive_on_fixed_complement_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) :
    ∀ y z : Ω,
      y ∈ fixedPointsOfSubgroup G Ω X →
      z ∈ fixedPointsOfSubgroup G Ω X →
      y ≠ base → z ≠ base →
        ∃ q : G, q ∈ Subgroup.centralizer (X : Set G) ⊓ Q ∧ q • y = z := by
  classical
  intro y z hy_fixed hz_fixed hy_ne_base hz_ne_base
  obtain ⟨qy, hqy, hqy_unique⟩ :=
    hypothesisA1_Q_unique_on_complement hA1 hHbase y hy_ne_base
  obtain ⟨qz, hqz, _hqz_unique⟩ :=
    hypothesisA1_Q_unique_on_complement hA1 hHbase z hz_ne_base
  have hqyC : qy ∈ Subgroup.centralizer (X : Set G) :=
    hypothesisA1_Q_mem_centralizer_of_smul_fixed hA1 hX_le_D hHbase
      hqy.1 hy_fixed hqy.2
  have hqzC : qz ∈ Subgroup.centralizer (X : Set G) :=
    hypothesisA1_Q_mem_centralizer_of_smul_fixed hA1 hX_le_D hHbase
      hqz.1 hz_fixed hqz.2
  let q : G := qz * qy⁻¹
  have hqC : q ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer (X : Set G)).mul_mem hqzC
      ((Subgroup.centralizer (X : Set G)).inv_mem hqyC)
  have hqQ : q ∈ Q := Q.mul_mem hqz.1 (Q.inv_mem hqy.1)
  refine ⟨q, ⟨hqC, hqQ⟩, ?_⟩
  calc
    q • y = (qz * qy⁻¹) • y := rfl
    _ = qz • (qy⁻¹ • y) := by rw [mul_smul]
    _ = qz • (t⁻¹ • base) := by
      rw [← hqy.2]
      simp [smul_smul]
    _ = z := hqz.2

private theorem hypothesisA1_Qt_regular_on_complement
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) :
    ∀ y : Ω, y ≠ t⁻¹ • base →
      ∃! q : G, q ∈ rightConjugate Q t ∧ q • base = y := by
  classical
  intro y hy_ne_beta
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have ht_y_ne_base : t • y ≠ base := by
    intro hty
    apply hy_ne_beta
    calc
      y = t⁻¹ • (t • y) := by simp [smul_smul]
      _ = t⁻¹ • base := by rw [hty]
  obtain ⟨q0, hq0, hq0_unique⟩ :=
    hypothesisA1_Q_unique_on_complement hA1 hHbase (t • y) ht_y_ne_base
  let q : G := t⁻¹ * q0 * t
  have hqQt : q ∈ rightConjugate Q t := by
    refine ⟨q0, hq0.1, ?_⟩
    dsimp [q]
    simp
  have ht_base : t • base = t⁻¹ • base := by rw [htinv]
  have hq_base : q • base = y := by
    calc
      q • base = t⁻¹ • (q0 • (t • base)) := by
        simp [q, mul_smul, mul_assoc]
      _ = t⁻¹ • (q0 • (t⁻¹ • base)) := by rw [ht_base]
      _ = t⁻¹ • (t • y) := by rw [hq0.2]
      _ = y := by simp [smul_smul]
  refine ⟨q, ⟨hqQt, hq_base⟩, ?_⟩
  intro q' hq'
  rcases hq'.1 with ⟨q0', hq0'Q, hq0'eq⟩
  have hq0'_beta : q0' • (t⁻¹ • base) = t • y := by
    calc
      q0' • (t⁻¹ • base) = q0' • (t • base) := by rw [htinv]
      _ = t • (((MulAut.conj t⁻¹) q0') • base) := by
        simp [mul_smul, mul_assoc]
      _ = t • (q' • base) := by
        change t • (((MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) q0') • base) =
          t • (q' • base)
        rw [hq0'eq]
      _ = t • y := by rw [hq'.2]
  have hq0'_eq : q0' = q0 :=
    hq0_unique q0' ⟨hq0'Q, hq0'_beta⟩
  calc
    q' = (MulAut.conj t⁻¹) q0' := hq0'eq.symm
    _ = (MulAut.conj t⁻¹) q0 := by rw [hq0'_eq]
    _ = q := by
      change (MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) q0 = q
      dsimp [q]
      simp

private theorem hypothesisA1_Qt_mem_centralizer_of_smul_fixed
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t q : G} {y : Ω}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base)
    (hqQt : q ∈ rightConjugate Q t)
    (hy_fixed : y ∈ fixedPointsOfSubgroup G Ω X)
    (hq_base : q • base = y) :
    q ∈ Subgroup.centralizer (X : Set G) := by
  classical
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxD : x ∈ D := hX_le_D hx
  have hx_base : x • base = base :=
    hypothesisA1_D_fixes_base hA1 hHbase hxD
  have hx_inv_base : x⁻¹ • base = base :=
    hypothesisA1_D_fixes_base hA1 hHbase (D.inv_mem hxD)
  have hconjQt : x * q * x⁻¹ ∈ rightConjugate Q t :=
    hypothesisA1_D_conj_mem_rightConjugate_Q hA1 hxD hqQt
  have hconj_base : (x * q * x⁻¹) • base = y := by
    calc
      (x * q * x⁻¹) • base =
          x • (q • (x⁻¹ • base)) := by simp [mul_smul, mul_assoc]
      _ = x • (q • base) := by rw [hx_inv_base]
      _ = x • y := by rw [hq_base]
      _ = y := hy_fixed x hx
  have hy_ne_beta : y ≠ t⁻¹ • base := by
    intro hybeta
    have hq_beta : q • (t⁻¹ • base) = t⁻¹ • base :=
      hypothesisA1_rightConjugate_Q_fixes_t_inv_base hA1 hHbase hqQt
    have hbase_eq_beta : base = t⁻¹ • base := by
      calc
        base = q⁻¹ • (q • base) := by simp [smul_smul]
        _ = q⁻¹ • y := by rw [hq_base]
        _ = q⁻¹ • (t⁻¹ • base) := by rw [hybeta]
        _ = t⁻¹ • base := by
          have hqinv_beta : q⁻¹ • (t⁻¹ • base) = t⁻¹ • base := by
            calc
              q⁻¹ • (t⁻¹ • base) = q⁻¹ • (q • (t⁻¹ • base)) := by rw [hq_beta]
              _ = t⁻¹ • base := by simp [smul_smul]
          exact hqinv_beta
    exact (hypothesisA1_base_ne_t_inv_base hA1 hHbase) hbase_eq_beta
  have hregular := hypothesisA1_Qt_regular_on_complement hA1 hHbase y hy_ne_beta
  have hconj_eq_q :
      x * q * x⁻¹ = q :=
    hregular.unique ⟨hconjQt, hconj_base⟩ ⟨hqQt, hq_base⟩
  calc
    x * q = (x * q * x⁻¹) * x := by group
    _ = q * x := by rw [hconj_eq_q]

private theorem hypothesisA1_CQt_transitive_on_fixed_complement_beta
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base) :
    ∀ y z : Ω,
      y ∈ fixedPointsOfSubgroup G Ω X →
      z ∈ fixedPointsOfSubgroup G Ω X →
      y ≠ t⁻¹ • base → z ≠ t⁻¹ • base →
        ∃ q : G, q ∈ Subgroup.centralizer (X : Set G) ⊓ rightConjugate Q t ∧ q • y = z := by
  classical
  intro y z hy_fixed hz_fixed hy_ne_beta hz_ne_beta
  obtain ⟨qy, hqy, hqy_unique⟩ :=
    hypothesisA1_Qt_regular_on_complement hA1 hHbase y hy_ne_beta
  obtain ⟨qz, hqz, _hqz_unique⟩ :=
    hypothesisA1_Qt_regular_on_complement hA1 hHbase z hz_ne_beta
  have hqyC : qy ∈ Subgroup.centralizer (X : Set G) :=
    hypothesisA1_Qt_mem_centralizer_of_smul_fixed hA1 hX_le_D hHbase
      hqy.1 hy_fixed hqy.2
  have hqzC : qz ∈ Subgroup.centralizer (X : Set G) :=
    hypothesisA1_Qt_mem_centralizer_of_smul_fixed hA1 hX_le_D hHbase
      hqz.1 hz_fixed hqz.2
  let q : G := qz * qy⁻¹
  have hqC : q ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer (X : Set G)).mul_mem hqzC
      ((Subgroup.centralizer (X : Set G)).inv_mem hqyC)
  have hqQt : q ∈ rightConjugate Q t :=
    (rightConjugate Q t).mul_mem hqz.1 ((rightConjugate Q t).inv_mem hqy.1)
  refine ⟨q, ⟨hqC, hqQt⟩, ?_⟩
  calc
    q • y = (qz * qy⁻¹) • y := rfl
    _ = qz • (qy⁻¹ • y) := by rw [mul_smul]
    _ = qz • base := by
      rw [← hqy.2]
      simp [smul_smul]
    _ = z := hqz.2

private theorem hypothesisA1_centralizer_smul_fixed
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {X : Subgroup G} {g : G} {ω : Ω}
    (hgC : g ∈ Subgroup.centralizer (X : Set G))
    (hω : ω ∈ fixedPointsOfSubgroup G Ω X) :
    g • ω ∈ fixedPointsOfSubgroup G Ω X := by
  intro x hx
  have hcomm : x * g = g * x :=
    (Subgroup.mem_centralizer_iff.mp hgC) x hx
  calc
    x • (g • ω) = (x * g) • ω := by rw [mul_smul]
    _ = (g * x) • ω := by rw [hcomm]
    _ = g • (x • ω) := by rw [mul_smul]
    _ = g • ω := by rw [hω x hx]

private theorem hypothesisA1_exists_fixed_ne_base_beta
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) {base : Ω}
    (hHbase : H = MulAction.stabilizer G base)
    (hfixed : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}) :
    ∃ e : Ω,
      e ∈ fixedPointsOfSubgroup G Ω X ∧ e ≠ base ∧ e ≠ t⁻¹ • base := by
  classical
  let Fixed : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  have hbase_fixed : base ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    exact hypothesisA1_D_fixes_base hA1 hHbase (hX_le_D hx)
  have hbeta_fixed : t⁻¹ • base ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    exact hypothesisA1_D_fixes_t_inv_base hA1 hHbase (hX_le_D hx)
  by_contra hno
  have hcover :
      ∀ p : Fixed, (p : Ω) = base ∨ (p : Ω) = t⁻¹ • base := by
    intro p
    by_contra hp
    apply hno
    exact ⟨p, p.property, fun h => hp (Or.inl h), fun h => hp (Or.inr h)⟩
  let pbase : Fixed := ⟨base, hbase_fixed⟩
  let pbeta : Fixed := ⟨t⁻¹ • base, hbeta_fixed⟩
  let f : Fin 2 → Fixed := fun i => if i = 0 then pbase else pbeta
  letI : Fintype Fixed := Fintype.ofFinite Fixed
  have hsurj : Function.Surjective f := by
    intro p
    rcases hcover p with hp | hp
    · refine ⟨0, ?_⟩
      ext
      simp [f, pbase, hp]
    · refine ⟨1, ?_⟩
      ext
      simp [f, pbeta, hp]
  have hcard_le : Fintype.card Fixed ≤ 2 := by
    simpa using Fintype.card_le_of_surjective f hsurj
  have hcard_ge : 3 ≤ Fintype.card Fixed := by
    rw [← Nat.card_eq_fintype_card]
    change 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
    exact hfixed
  omega

private theorem hypothesisA1_centralizer_moves_base_to_fixed
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) {base z : Ω}
    (hHbase : H = MulAction.stabilizer G base)
    (hfixed_card : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X})
    (hz_fixed : z ∈ fixedPointsOfSubgroup G Ω X) :
    ∃ g : G, g ∈ Subgroup.centralizer (X : Set G) ∧ g • base = z := by
  classical
  by_cases hz_base : z = base
  · exact ⟨1, Subgroup.one_mem _, by simp [hz_base]⟩
  by_cases hz_beta : z = t⁻¹ • base
  · rcases hypothesisA1_exists_fixed_ne_base_beta hA1 hX_le_D hHbase hfixed_card with
      ⟨e, he_fixed, he_ne_base, he_ne_beta⟩
    have hbase_ne_beta : base ≠ t⁻¹ • base :=
      hypothesisA1_base_ne_t_inv_base hA1 hHbase
    rcases
      hypothesisA1_CQt_transitive_on_fixed_complement_beta hA1 hX_le_D hHbase
        base e
        (by
          intro x hx
          exact hypothesisA1_D_fixes_base hA1 hHbase (hX_le_D hx))
        he_fixed hbase_ne_beta he_ne_beta with
      ⟨g1, hg1, hg1map⟩
    rcases
      hypothesisA1_CQ_transitive_on_fixed_complement_base hA1 hX_le_D hHbase
        e (t⁻¹ • base) he_fixed
        (by
          intro x hx
          exact hypothesisA1_D_fixes_t_inv_base hA1 hHbase (hX_le_D hx))
        he_ne_base hbase_ne_beta.symm with
      ⟨g2, hg2, hg2map⟩
    refine ⟨g2 * g1, (Subgroup.centralizer (X : Set G)).mul_mem hg2.1 hg1.1, ?_⟩
    calc
      (g2 * g1) • base = g2 • (g1 • base) := by rw [mul_smul]
      _ = g2 • e := by rw [hg1map]
      _ = t⁻¹ • base := hg2map
      _ = z := hz_beta.symm
  · have hbase_ne_beta : base ≠ t⁻¹ • base :=
      hypothesisA1_base_ne_t_inv_base hA1 hHbase
    rcases
      hypothesisA1_CQt_transitive_on_fixed_complement_beta hA1 hX_le_D hHbase
        base z
        (by
          intro x hx
          exact hypothesisA1_D_fixes_base hA1 hHbase (hX_le_D hx))
        hz_fixed hbase_ne_beta hz_beta with
      ⟨g, hg, hgmap⟩
    exact ⟨g, hg.1, hgmap⟩

private theorem hypothesisA1_centralizer_double_transitive
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D)
    (hfixed : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}) :
    ∀ a b c d : Ω,
      a ∈ fixedPointsOfSubgroup G Ω X →
      b ∈ fixedPointsOfSubgroup G Ω X →
      c ∈ fixedPointsOfSubgroup G Ω X →
      d ∈ fixedPointsOfSubgroup G Ω X →
      a ≠ b → c ≠ d →
        ∃ g : G, g ∈ Subgroup.centralizer (X : Set G) ∧ g • a = c ∧ g • b = d := by
  classical
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  intro a b c d ha_fixed hb_fixed hc_fixed hd_fixed hab hcd
  rcases
    hypothesisA1_centralizer_moves_base_to_fixed hA1 hX_le_D hHbase hfixed ha_fixed with
    ⟨ga, hgaC, hga_base⟩
  rcases
    hypothesisA1_centralizer_moves_base_to_fixed hA1 hX_le_D hHbase hfixed hc_fixed with
    ⟨gc, hgcC, hgc_base⟩
  let b' : Ω := ga⁻¹ • b
  let d' : Ω := gc⁻¹ • d
  have hga_invC : ga⁻¹ ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer (X : Set G)).inv_mem hgaC
  have hgc_invC : gc⁻¹ ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer (X : Set G)).inv_mem hgcC
  have hb'_fixed : b' ∈ fixedPointsOfSubgroup G Ω X :=
    hypothesisA1_centralizer_smul_fixed hga_invC hb_fixed
  have hd'_fixed : d' ∈ fixedPointsOfSubgroup G Ω X :=
    hypothesisA1_centralizer_smul_fixed hgc_invC hd_fixed
  have hb'_ne_base : b' ≠ base := by
    intro hb'
    apply hab
    calc
      a = ga • base := hga_base.symm
      _ = ga • b' := by rw [hb']
      _ = b := by simp [b', smul_smul]
  have hd'_ne_base : d' ≠ base := by
    intro hd'
    apply hcd
    calc
      c = gc • base := hgc_base.symm
      _ = gc • d' := by rw [hd']
      _ = d := by simp [d', smul_smul]
  rcases
    hypothesisA1_CQ_transitive_on_fixed_complement_base hA1 hX_le_D hHbase
      b' d' hb'_fixed hd'_fixed hb'_ne_base hd'_ne_base with
    ⟨q, hq, hqmap⟩
  let g : G := gc * q * ga⁻¹
  have hgC : g ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer (X : Set G)).mul_mem
      ((Subgroup.centralizer (X : Set G)).mul_mem hgcC hq.1)
      hga_invC
  refine ⟨g, hgC, ?_, ?_⟩
  · calc
      g • a = (gc * q * ga⁻¹) • a := rfl
      _ = gc • (q • (ga⁻¹ • a)) := by simp [mul_smul, mul_assoc]
      _ = gc • (q • base) := by
        have hga_inv_a : ga⁻¹ • a = base := by
          calc
            ga⁻¹ • a = ga⁻¹ • (ga • base) := by rw [hga_base]
            _ = base := by simp [smul_smul]
        rw [hga_inv_a]
      _ = gc • base := by
        have hq_base : q • base = base := by
          have hqH : q ∈ H := hA1.Q_le_H hq.2
          have hqstab : q ∈ MulAction.stabilizer G base := by
            simpa [hHbase] using hqH
          simpa using hqstab
        rw [hq_base]
      _ = c := hgc_base
  · calc
      g • b = (gc * q * ga⁻¹) • b := rfl
      _ = gc • (q • (ga⁻¹ • b)) := by simp [mul_smul, mul_assoc]
      _ = gc • (q • b') := rfl
      _ = gc • d' := by rw [hqmap]
      _ = d := by simp [d', smul_smul]

private theorem hypothesisA1_centralizer_semidirect
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q X : Subgroup G} {t : G}
    (hA1 : HypothesisA1 G Ω H D Q t) (hX_le_D : X ≤ D) :
    (Subgroup.centralizer (X : Set G) ⊓ Q) ≤
        (Subgroup.centralizer (X : Set G) ⊓ H) ∧
      (Subgroup.centralizer (X : Set G) ⊓ D) ≤
        (Subgroup.centralizer (X : Set G) ⊓ H) ∧
        (∀ h n : G,
          h ∈ Subgroup.centralizer (X : Set G) ⊓ H →
            n ∈ Subgroup.centralizer (X : Set G) ⊓ Q →
              h * n * h⁻¹ ∈ Subgroup.centralizer (X : Set G) ⊓ Q) ∧
          Disjoint (Subgroup.centralizer (X : Set G) ⊓ Q)
            (Subgroup.centralizer (X : Set G) ⊓ D) ∧
            (Subgroup.centralizer (X : Set G) ⊓ Q) ⊔
                (Subgroup.centralizer (X : Set G) ⊓ D) =
              Subgroup.centralizer (X : Set G) ⊓ H := by
  classical
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  change (C ⊓ Q) ≤ (C ⊓ H) ∧ (C ⊓ D) ≤ (C ⊓ H) ∧
    (∀ h n : G, h ∈ C ⊓ H → n ∈ C ⊓ Q → h * n * h⁻¹ ∈ C ⊓ Q) ∧
      Disjoint (C ⊓ Q) (C ⊓ D) ∧ (C ⊓ Q) ⊔ (C ⊓ D) = C ⊓ H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨hg.1, hA1.Q_le_H hg.2⟩
  · intro g hg
    exact ⟨hg.1, hA1.D_le_H hg.2⟩
  · intro h n hh hn
    exact
      ⟨C.mul_mem (C.mul_mem hh.1 hn.1) (C.inv_mem hh.1),
        hypothesisA1_Q_conj_mem_of_mem_H hA1 hh.2 hn.2⟩
  · rw [Subgroup.disjoint_def]
    intro g hgQ hgD
    exact (Subgroup.disjoint_def.mp hA1.Q_disjoint_D) hgQ.2 hgD.2
  · apply le_antisymm
    · exact sup_le
        (by
          intro g hg
          exact ⟨hg.1, hA1.Q_le_H hg.2⟩)
        (by
          intro g hg
          exact ⟨hg.1, hA1.D_le_H hg.2⟩)
    · intro h hh
      rcases hypothesisA1_H_decomp hA1 hh.2 with ⟨q, hq, d, hd, hqd⟩
      have hqC : q ∈ C := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxD : x ∈ D := hX_le_D hx
        have hxH : x ∈ H := hA1.D_le_H hxD
        have hq'Q : x * q * x⁻¹ ∈ Q :=
          hypothesisA1_Q_conj_mem_of_mem_H hA1 hxH hq
        have hd'D : x * d * x⁻¹ ∈ D :=
          D.mul_mem (D.mul_mem hxD hd) (D.inv_mem hxD)
        have hconj_eq : (x * q * x⁻¹) * (x * d * x⁻¹) = q * d := by
          calc
            (x * q * x⁻¹) * (x * d * x⁻¹) = x * (q * d) * x⁻¹ := by group
            _ = x * h * x⁻¹ := by rw [hqd]
            _ = h := by
              have hxh : x * h = h * x :=
                (Subgroup.mem_centralizer_iff.mp hh.1) x hx
              calc
                x * h * x⁻¹ = (h * x) * x⁻¹ := by rw [hxh]
                _ = h := by group
            _ = q * d := hqd.symm
        have huniq :=
          hypothesisA1_H_decomp_unique hA1 hq'Q hd'D hq hd hconj_eq
        calc
          x * q = (x * q * x⁻¹) * x := by group
          _ = q * x := by rw [huniq.1]
      have hdC : d ∈ C := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxD : x ∈ D := hX_le_D hx
        have hxH : x ∈ H := hA1.D_le_H hxD
        have hq'Q : x * q * x⁻¹ ∈ Q :=
          hypothesisA1_Q_conj_mem_of_mem_H hA1 hxH hq
        have hd'D : x * d * x⁻¹ ∈ D :=
          D.mul_mem (D.mul_mem hxD hd) (D.inv_mem hxD)
        have hconj_eq : (x * q * x⁻¹) * (x * d * x⁻¹) = q * d := by
          calc
            (x * q * x⁻¹) * (x * d * x⁻¹) = x * (q * d) * x⁻¹ := by group
            _ = x * h * x⁻¹ := by rw [hqd]
            _ = h := by
              have hxh : x * h = h * x :=
                (Subgroup.mem_centralizer_iff.mp hh.1) x hx
              calc
                x * h * x⁻¹ = (h * x) * x⁻¹ := by rw [hxh]
                _ = h := by group
            _ = q * d := hqd.symm
        have huniq :=
          hypothesisA1_H_decomp_unique hA1 hq'Q hd'D hq hd hconj_eq
        calc
          x * d = (x * d * x⁻¹) * x := by group
          _ = d * x := by rw [huniq.2]
      rw [← hqd]
      exact Subgroup.mul_mem_sup (S := C ⊓ Q) (T := C ⊓ D) ⟨hqC, hq⟩ ⟨hdC, hd⟩

public theorem proposition_6_a
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q X : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hX_le_D : X ≤ D)
    (hfixed : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}) :
    (∀ a b c d : Ω,
      a ∈ fixedPointsOfSubgroup G Ω X →
      b ∈ fixedPointsOfSubgroup G Ω X →
      c ∈ fixedPointsOfSubgroup G Ω X →
      d ∈ fixedPointsOfSubgroup G Ω X →
      a ≠ b → c ≠ d →
        ∃ g : G, g ∈ Subgroup.centralizer (X : Set G) ∧ g • a = c ∧ g • b = d) ∧
      ((Subgroup.centralizer (X : Set G) ⊓ Q) ≤
          (Subgroup.centralizer (X : Set G) ⊓ H) ∧
        (Subgroup.centralizer (X : Set G) ⊓ D) ≤
          (Subgroup.centralizer (X : Set G) ⊓ H) ∧
          (∀ h n : G,
            h ∈ Subgroup.centralizer (X : Set G) ⊓ H →
              n ∈ Subgroup.centralizer (X : Set G) ⊓ Q →
                h * n * h⁻¹ ∈ Subgroup.centralizer (X : Set G) ⊓ Q) ∧
            Disjoint (Subgroup.centralizer (X : Set G) ⊓ Q)
              (Subgroup.centralizer (X : Set G) ⊓ D) ∧
              (Subgroup.centralizer (X : Set G) ⊓ Q) ⊔
                  (Subgroup.centralizer (X : Set G) ⊓ D) =
                Subgroup.centralizer (X : Set G) ⊓ H) := by
  exact
    ⟨hypothesisA1_centralizer_double_transitive hA1 hX_le_D hfixed,
      hypothesisA1_centralizer_semidirect hA1 hX_le_D⟩

public theorem t_mem_centralizer_of_le_peterfalviV
    {G : Type*} [Group G] (D V X : Subgroup G) (t : G)
    (hX_le_V : X ≤ V) (hV_eq : V = peterfalviV D t) :
    t ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxV : x ∈ peterfalviV D t := by
    simpa [hV_eq] using hX_le_V hx
  exact ((Subgroup.mem_centralizer_iff.mp hxV.2) t (by simp)).symm

end PFchapter1section1
end CFSG.BenderSuzuki

