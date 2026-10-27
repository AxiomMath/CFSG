module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 1, (H1) -/

public theorem rightConjugateElem_mem_rightConjugate
    {L : Type*} [Group L] {M : Subgroup L} {a t : L}
    (ha : a ∈ M) : rightConjugateElem a t ∈ rightConjugate M t := by
  rw [rightConjugate, rightConjugateElem, Subgroup.conjBy, Subgroup.mem_map]
  exact ⟨a, ha, by simp⟩

public theorem rightConjugateElem_mem_of_mem_rightConjugate
    {L : Type*} [Group L] {M : Subgroup L} {a t : L}
    (htinv : t⁻¹ = t) (ha : a ∈ rightConjugate M t) :
    rightConjugateElem a t ∈ M := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at ha
  rcases ha with ⟨m, hm, rfl⟩
  have hmapped :
      (MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) m =
        rightConjugateElem m t := by
    simp [rightConjugateElem, htinv, mul_assoc]
  rw [hmapped]
  simpa [rightConjugateElem_rightConjugateElem (a := m) htinv] using hm

public theorem rightConjugateElem_mem_D
    {L : Type*} [Group L] {M D : Subgroup L} {a t : L}
    (htinv : t⁻¹ = t) (hD : D = M ⊓ rightConjugate M t) (ha : a ∈ D) :
    rightConjugateElem a t ∈ D := by
  rw [hD] at ha ⊢
  exact
    ⟨rightConjugateElem_mem_of_mem_rightConjugate (M := M) htinv ha.2,
      rightConjugateElem_mem_rightConjugate (M := M) ha.1⟩

public theorem qd_t_q_right_unique
    {L : Type*} [Group L] {M Q D : Subgroup L} {t q₁ d₁ r₁ q₂ d₂ r₂ : L}
    (htinv : t⁻¹ = t) (hD : D = M ⊓ rightConjugate M t)
    (hQM : Q ≤ M) (hDM : D ≤ M) (hdisj : Disjoint Q D)
    (hq₁ : q₁ ∈ Q) (hd₁ : d₁ ∈ D) (hr₁ : r₁ ∈ Q)
    (hq₂ : q₂ ∈ Q) (hd₂ : d₂ ∈ D) (hr₂ : r₂ ∈ Q)
    (heq : q₁ * d₁ * t * r₁ = q₂ * d₂ * t * r₂) :
    r₁ = r₂ := by
  have hleftM : (q₂ * d₂)⁻¹ * (q₁ * d₁) ∈ M := by
    exact M.mul_mem
      (M.inv_mem (M.mul_mem (hQM hq₂) (hDM hd₂)))
      (M.mul_mem (hQM hq₁) (hDM hd₁))
  have hdiffQ : r₂ * r₁⁻¹ ∈ Q := Q.mul_mem hr₂ (Q.inv_mem hr₁)
  have hcalc :
      (q₂ * d₂)⁻¹ * (q₁ * d₁) = t * (r₂ * r₁⁻¹) * t⁻¹ := by
    calc
      (q₂ * d₂)⁻¹ * (q₁ * d₁) =
          (q₂ * d₂)⁻¹ * (q₁ * d₁ * t * r₁) * r₁⁻¹ * t⁻¹ := by
            simp [mul_assoc]
      _ = (q₂ * d₂)⁻¹ * (q₂ * d₂ * t * r₂) * r₁⁻¹ * t⁻¹ := by
            rw [heq]
      _ = t * (r₂ * r₁⁻¹) * t⁻¹ := by
            simp [mul_assoc]
  have hconjD : rightConjugateElem (r₂ * r₁⁻¹) t ∈ D := by
    rw [hD]
    refine ⟨?_, ?_⟩
    · have hright_eq :
          rightConjugateElem (r₂ * r₁⁻¹) t =
            (q₂ * d₂)⁻¹ * (q₁ * d₁) := by
        simpa [rightConjugateElem, htinv, mul_assoc] using hcalc.symm
      simpa [hright_eq] using hleftM
    · exact rightConjugateElem_mem_rightConjugate (M := M) (hQM hdiffQ)
  have hdiffD : r₂ * r₁⁻¹ ∈ D := by
    have hback := rightConjugateElem_mem_D (M := M) (D := D) htinv hD hconjD
    simpa [rightConjugateElem_rightConjugateElem (a := r₂ * r₁⁻¹) htinv] using hback
  have hdiff_one : r₂ * r₁⁻¹ = 1 :=
    Subgroup.disjoint_def.mp hdisj hdiffQ hdiffD
  exact (mul_inv_eq_one.mp hdiff_one).symm

public theorem qd_t_q_unique
    {L : Type*} [Group L] {M Q D : Subgroup L} {t q₁ d₁ r₁ q₂ d₂ r₂ : L}
    (htinv : t⁻¹ = t) (hD : D = M ⊓ rightConjugate M t)
    (hQM : Q ≤ M) (hDM : D ≤ M) (hdisj : Disjoint Q D)
    (hq₁ : q₁ ∈ Q) (hd₁ : d₁ ∈ D) (hr₁ : r₁ ∈ Q)
    (hq₂ : q₂ ∈ Q) (hd₂ : d₂ ∈ D) (hr₂ : r₂ ∈ Q)
    (heq : q₁ * d₁ * t * r₁ = q₂ * d₂ * t * r₂) :
    q₁ = q₂ ∧ d₁ = d₂ ∧ r₁ = r₂ := by
  have hr : r₁ = r₂ :=
    qd_t_q_right_unique (M := M) (Q := Q) (D := D) (t := t)
      (q₁ := q₁) (d₁ := d₁) (r₁ := r₁)
      (q₂ := q₂) (d₂ := d₂) (r₂ := r₂)
      htinv hD hQM hDM hdisj hq₁ hd₁ hr₁ hq₂ hd₂ hr₂ heq
  have hqd : q₁ * d₁ = q₂ * d₂ := by
    have h := congrArg (fun z => z * r₁⁻¹ * t⁻¹) heq
    simpa [hr, mul_assoc] using h
  have hdiff :
      q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
    calc
      q₂⁻¹ * q₁ = q₂⁻¹ * q₁ * (d₁ * d₁⁻¹) := by simp
      _ = q₂⁻¹ * (q₁ * d₁) * d₁⁻¹ := by simp [mul_assoc]
      _ = q₂⁻¹ * (q₂ * d₂) * d₁⁻¹ := by rw [hqd]
      _ = d₂ * d₁⁻¹ := by simp
  have hdiffQ : q₂⁻¹ * q₁ ∈ Q := Q.mul_mem (Q.inv_mem hq₂) hq₁
  have hdiffD : q₂⁻¹ * q₁ ∈ D := by
    rw [hdiff]
    exact D.mul_mem hd₂ (D.inv_mem hd₁)
  have hdiff_one : q₂⁻¹ * q₁ = 1 :=
    Subgroup.disjoint_def.mp hdisj hdiffQ hdiffD
  have hq : q₁ = q₂ := (inv_mul_eq_one.mp hdiff_one).symm
  have hd : d₁ = d₂ := by
    have hd' : q₂ * d₁ = q₂ * d₂ := by
      simpa [hq] using hqd
    exact mul_left_cancel hd'
  exact ⟨hq, hd, hr⟩

public theorem canonical_compare_inv
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    g x⁻¹ = (f x)⁻¹ ∧
      h x⁻¹ = rightConjugateElem (h x)⁻¹ t ∧
        f x⁻¹ = (g x)⁻¹ := by
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_not_mem_M
  have _ := hQ_normal_in_M
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have ht2 : t * t = 1 := by
    calc
      t * t = t⁻¹ * t := by rw [htinv]
      _ = 1 := inv_mul_cancel t
  have hxinvQ : x⁻¹ ∈ Q := Q.inv_mem hxQ
  have hxinv1 : x⁻¹ ≠ 1 := by
    intro h
    exact hx1 (inv_eq_one.mp h)
  have hcan_x := hcanonical_eq x hxQ hx1
  have hcan_xinv := hcanonical_eq x⁻¹ hxinvQ hxinv1
  have hfmem := hf_mem x hxQ hx1
  have hgmem := hg_mem x hxQ hx1
  have hhmem := hh_mem x hxQ hx1
  have hfmem_inv := hf_mem x⁻¹ hxinvQ hxinv1
  have hgmem_inv := hg_mem x⁻¹ hxinvQ hxinv1
  have hhmem_inv := hh_mem x⁻¹ hxinvQ hxinv1
  have hsecond :
      t * x⁻¹ * t =
        (f x)⁻¹ * rightConjugateElem (h x)⁻¹ t * t * (g x)⁻¹ := by
    calc
      t * x⁻¹ * t = (t * x * t)⁻¹ := by
        simp [htinv, mul_assoc]
      _ = (g x * h x * t * f x)⁻¹ := by
            rw [hcan_x]
      _ = (f x)⁻¹ * rightConjugateElem (h x)⁻¹ t * t * (g x)⁻¹ := by
        simp [rightConjugateElem, htinv, ht2, mul_assoc]
  have hcompare :
      g x⁻¹ * h x⁻¹ * t * f x⁻¹ =
        (f x)⁻¹ * rightConjugateElem (h x)⁻¹ t * t * (g x)⁻¹ :=
    hcan_xinv.symm.trans hsecond
  exact qd_t_q_unique (M := M) (Q := Q) (D := D) (t := t)
    (q₁ := g x⁻¹) (d₁ := h x⁻¹) (r₁ := f x⁻¹)
    (q₂ := (f x)⁻¹) (d₂ := rightConjugateElem (h x)⁻¹ t) (r₂ := (g x)⁻¹)
    htinv hD_eq (rankOneSplit_Q_le_M hQ_sup_D) (rankOneSplit_D_le_M hD_eq) hQ_disjoint_D
    hgmem_inv.1 hhmem_inv hfmem_inv.1
    (Q.inv_mem hfmem.1)
    (rightConjugateElem_mem_D (M := M) (D := D) htinv hD_eq (D.inv_mem hhmem))
    (Q.inv_mem hgmem.1) hcompare

public theorem claim_H1
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ x : L, x ∈ Q → x ≠ 1 → f x⁻¹ = (g x)⁻¹ := by
  intro x hxQ hx1
  exact (canonical_compare_inv M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hxQ hx1).2.2

end PFchapter4section1
end CFSG.BenderSuzuki

