module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H4_c

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 1, (H5) -/

private theorem h5_j_comp_f_sq
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
    ∀ x : L, x ∈ Q → x ≠ 1 →
      (f ((f x)⁻¹))⁻¹ = rightConjugateElem (f x⁻¹) (h x) := by
  intro x hxQ hx1
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have ht2 : t * t = 1 := by
    calc
      t * t = t⁻¹ * t := by rw [htinv]
      _ = 1 := inv_mul_cancel t
  have hfxmem := hf_mem x hxQ hx1
  have hcan_x := hcanonical_eq x hxQ hx1
  have hcan_fx := hcanonical_eq (f x) hfxmem.1 hfxmem.2
  have hsecond :
      t * f x * t = (h x)⁻¹ * (g x)⁻¹ * t * x := by
    calc
      t * f x * t =
          (h x)⁻¹ * (g x)⁻¹ * (g x * h x * t * f x) * t := by
            group
      _ = (h x)⁻¹ * (g x)⁻¹ * (t * x * t) * t := by
            rw [← hcan_x]
      _ = (h x)⁻¹ * (g x)⁻¹ * t * x := by
            simp [ht2, mul_assoc]
  have hcompare :
      g (f x) * h (f x) * t * f (f x) =
        (h x)⁻¹ * (g x)⁻¹ * t * x :=
    hcan_fx.symm.trans hsecond
  have hffx : f (f x) = x :=
    claim_H2 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x hxQ hx1
  have hhfx : h (f x) = (h x)⁻¹ :=
    claim_H4_c M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x hxQ hx1
  have hgfx :
      g (f x) = rightConjugateElem (g x)⁻¹ (h x) := by
    have hcompare' :
        g (f x) * (h x)⁻¹ * t * x =
          (h x)⁻¹ * (g x)⁻¹ * t * x := by
      simpa [hffx, hhfx, mul_assoc] using hcompare
    have hcancel := congrArg (fun u : L => u * (t * x)⁻¹ * h x) hcompare'
    simpa [rightConjugateElem, mul_assoc] using hcancel
  have hfgfx :
      f ((f x)⁻¹) = (g (f x))⁻¹ :=
    claim_H1 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq (f x) hfxmem.1 hfxmem.2
  have hfgx :
      f x⁻¹ = (g x)⁻¹ :=
    claim_H1 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x hxQ hx1
  calc
    (f ((f x)⁻¹))⁻¹ = g (f x) := by
      rw [hfgfx]
      simp
    _ = rightConjugateElem (g x)⁻¹ (h x) := hgfx
    _ = rightConjugateElem (f x⁻¹) (h x) := by rw [hfgx]

private theorem h5_fj_sq_rightConjugate
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
    ∀ x a : L, x ∈ Q → x ≠ 1 → a ∈ D →
      f ((f (rightConjugateElem x a)⁻¹)⁻¹) =
        rightConjugateElem (f ((f x⁻¹)⁻¹)) a := by
  intro x a hxQ hx1 haD
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have hxinvQ : x⁻¹ ∈ Q := Q.inv_mem hxQ
  have hxinv1 : x⁻¹ ≠ 1 := by
    intro h
    exact hx1 (inv_eq_one.mp h)
  have hfxinv := hf_mem x⁻¹ hxinvQ hxinv1
  have hbaseQ : (f x⁻¹)⁻¹ ∈ Q := Q.inv_mem hfxinv.1
  have hbase1 : (f x⁻¹)⁻¹ ≠ 1 := by
    intro h
    exact hfxinv.2 (inv_eq_one.mp h)
  have hatD : rightConjugateElem a t ∈ D :=
    rightConjugateElem_mem_D (M := M) (D := D) htinv hD_eq haD
  have hfirst :
      f (rightConjugateElem x⁻¹ a) =
        rightConjugateElem (f x⁻¹) (rightConjugateElem a t) :=
    claim_H3 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x⁻¹ a hxinvQ hxinv1 haD
  have hsecond :
      f (rightConjugateElem (f x⁻¹)⁻¹ (rightConjugateElem a t)) =
        rightConjugateElem (f ((f x⁻¹)⁻¹))
          (rightConjugateElem (rightConjugateElem a t) t) :=
    claim_H3 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq (f x⁻¹)⁻¹
      (rightConjugateElem a t) hbaseQ hbase1 hatD
  calc
    f ((f (rightConjugateElem x a)⁻¹)⁻¹) =
        f ((f (rightConjugateElem x⁻¹ a))⁻¹) := by
          simp [rightConjugateElem, mul_assoc]
    _ = f ((rightConjugateElem (f x⁻¹) (rightConjugateElem a t))⁻¹) := by
          rw [hfirst]
    _ = f (rightConjugateElem (f x⁻¹)⁻¹ (rightConjugateElem a t)) := by
          simp [rightConjugateElem, mul_assoc]
    _ = rightConjugateElem (f ((f x⁻¹)⁻¹))
          (rightConjugateElem (rightConjugateElem a t) t) := hsecond
    _ = rightConjugateElem (f ((f x⁻¹)⁻¹)) a := by
          rw [rightConjugateElem_rightConjugateElem (a := a) htinv]

public theorem claim_H5
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
    ∀ x : L, x ∈ Q → x ≠ 1 →
      f ((f ((f x⁻¹)⁻¹))⁻¹) = rightConjugateElem x (h x)⁻¹ := by
  intro x hxQ hx1
  have hxinvQ : x⁻¹ ∈ Q := Q.inv_mem hxQ
  have hxinv1 : x⁻¹ ≠ 1 := by
    intro h
    exact hx1 (inv_eq_one.mp h)
  have hfxinv := hf_mem x⁻¹ hxinvQ hxinv1
  have hfxmem := hf_mem x hxQ hx1
  have hfx_invQ : (f x)⁻¹ ∈ Q := Q.inv_mem hfxmem.1
  have hfx_inv1 : (f x)⁻¹ ≠ 1 := by
    intro h
    exact hfxmem.2 (inv_eq_one.mp h)
  have hconjFormula :
      (f ((f x)⁻¹))⁻¹ = rightConjugateElem (f x⁻¹) (h x) :=
    h5_j_comp_f_sq M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x hxQ hx1
  have hleft :
      f ((f (((f ((f x)⁻¹))⁻¹)⁻¹))⁻¹) = x := by
    have h1 :
        f (f ((f x)⁻¹)) = (f x)⁻¹ :=
      claim_H2 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq (f x)⁻¹ hfx_invQ hfx_inv1
    have h2 :
        f (f x) = x :=
      claim_H2 M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x hxQ hx1
    simp [h1, h2]
  have htransport :
      f ((f (rightConjugateElem (f x⁻¹) (h x))⁻¹)⁻¹) =
        rightConjugateElem (f ((f ((f x⁻¹)⁻¹))⁻¹)) (h x) :=
    h5_fj_sq_rightConjugate M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (f x⁻¹) (h x) hfxinv.1 hfxinv.2 (hh_mem x hxQ hx1)
  have hx_eq_conj :
      x = rightConjugateElem (f ((f ((f x⁻¹)⁻¹))⁻¹)) (h x) := by
    calc
      x = f ((f (((f ((f x)⁻¹))⁻¹)⁻¹))⁻¹) := hleft.symm
      _ = f ((f (rightConjugateElem (f x⁻¹) (h x))⁻¹)⁻¹) := by
            rw [hconjFormula]
      _ = rightConjugateElem (f ((f ((f x⁻¹)⁻¹))⁻¹)) (h x) := htransport
  calc
    f ((f ((f x⁻¹)⁻¹))⁻¹) =
        rightConjugateElem
          (rightConjugateElem (f ((f ((f x⁻¹)⁻¹))⁻¹)) (h x)) (h x)⁻¹ := by
          simp [rightConjugateElem, mul_assoc]
    _ = rightConjugateElem x (h x)⁻¹ := by rw [← hx_eq_conj]

end PFchapter4section1
end CFSG.BenderSuzuki


