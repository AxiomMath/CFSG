module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H2

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 1, (H6)(a) -/

public theorem h6_rightConjugateElem_mem_Q_of_mem_M
    {L : Type*} [Group L] {M Q : Subgroup L} {q a : L}
    (hQM : Q ≤ M) (hQnorm : (Q.subgroupOf M).Normal)
    (hq : q ∈ Q) (ha : a ∈ M) :
    rightConjugateElem q a ∈ Q := by
  have hqsub : (⟨q, hQM hq⟩ : M) ∈ Q.subgroupOf M := hq
  have hmem :=
    hQnorm.conj_mem (⟨q, hQM hq⟩ : M) hqsub ⟨a⁻¹, M.inv_mem ha⟩
  have htarget :
      (⟨rightConjugateElem q a,
        M.mul_mem (M.mul_mem (M.inv_mem ha) (hQM hq)) ha⟩ : M) ∈ Q.subgroupOf M := by
    convert hmem using 1
    ext
    simp [rightConjugateElem, mul_assoc]
  simpa [Subgroup.mem_subgroupOf] using htarget

public theorem h6_qd_D_unique
    {L : Type*} [Group L] {Q D : Subgroup L} {q₁ d₁ q₂ d₂ : L}
    (hdisj : Disjoint Q D)
    (hq₁ : q₁ ∈ Q) (hd₁ : d₁ ∈ D)
    (hq₂ : q₂ ∈ Q) (hd₂ : d₂ ∈ D)
    (heq : q₁ * d₁ = q₂ * d₂) :
    d₁ = d₂ := by
  have hdiff_eq : q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
    calc
      q₂⁻¹ * q₁ = q₂⁻¹ * (q₁ * d₁) * d₁⁻¹ := by
        simp [mul_assoc]
      _ = q₂⁻¹ * (q₂ * d₂) * d₁⁻¹ := by
        rw [heq]
      _ = d₂ * d₁⁻¹ := by
        simp
  have hdiffQ : q₂⁻¹ * q₁ ∈ Q := Q.mul_mem (Q.inv_mem hq₂) hq₁
  have hdiffD : q₂⁻¹ * q₁ ∈ D := by
    rw [hdiff_eq]
    exact D.mul_mem hd₂ (D.inv_mem hd₁)
  have hdiff_one : q₂⁻¹ * q₁ = 1 :=
    Subgroup.disjoint_def.mp hdisj hdiffQ hdiffD
  have hd : d₂ * d₁⁻¹ = 1 := by
    simpa [hdiff_eq] using hdiff_one
  exact (mul_inv_eq_one.mp hd).symm

public theorem h6_qd_t_q_D_unique
    {L : Type*} [Group L] {M Q D : Subgroup L} {t q₁ d₁ r₁ q₂ d₂ r₂ : L}
    (htinv : t⁻¹ = t) (hD : D = M ⊓ rightConjugate M t)
    (hQM : Q ≤ M) (hDM : D ≤ M) (hdisj : Disjoint Q D)
    (hq₁ : q₁ ∈ Q) (hd₁ : d₁ ∈ D) (hr₁ : r₁ ∈ Q)
    (hq₂ : q₂ ∈ Q) (hd₂ : d₂ ∈ D) (hr₂ : r₂ ∈ Q)
    (heq : q₁ * d₁ * t * r₁ = q₂ * d₂ * t * r₂) :
    d₁ = d₂ := by
  have hr : r₁ = r₂ :=
    qd_t_q_right_unique (M := M) (Q := Q) (D := D) (t := t)
      htinv hD hQM hDM hdisj hq₁ hd₁ hr₁ hq₂ hd₂ hr₂ heq
  have hsame_r : q₁ * d₁ * t * r₁ = q₂ * d₂ * t * r₁ := by
    simpa [hr] using heq
  have hqd : q₁ * d₁ = q₂ * d₂ := by
    have h := congrArg (fun u : L => u * (t * r₁)⁻¹) hsame_r
    simpa [mul_assoc] using h
  exact h6_qd_D_unique hdisj hq₁ hd₁ hq₂ hd₂ hqd

public theorem claim_H6_a
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
    ∀ x y : L, x ∈ Q → y ∈ Q → x ≠ 1 → y ≠ 1 → x * y ≠ 1 →
      f x * g y ≠ 1 := by
  intro x y hxQ hyQ hx1 hy1 hxy1 hprod
  have hyinvQ : y⁻¹ ∈ Q := Q.inv_mem hyQ
  have hyinv1 : y⁻¹ ≠ 1 := inv_ne_one.mpr hy1
  have hfyinv : f y⁻¹ = (g y)⁻¹ :=
    claim_H1 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq y hyQ hy1
  have hfx_eq : f x = f y⁻¹ := by
    calc
      f x = (g y)⁻¹ := by
        exact eq_inv_of_mul_eq_one_left hprod
      _ = f y⁻¹ := hfyinv.symm
  have hx_eq_yinv : x = y⁻¹ := by
    calc
      x = f (f x) := (claim_H2 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x hxQ hx1).symm
      _ = f (f y⁻¹) := by rw [hfx_eq]
      _ = y⁻¹ := claim_H2 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq y⁻¹ hyinvQ hyinv1
  apply hxy1
  rw [hx_eq_yinv, inv_mul_cancel]

end PFchapter4section1
end CFSG.BenderSuzuki
