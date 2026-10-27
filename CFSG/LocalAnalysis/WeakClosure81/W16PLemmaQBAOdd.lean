module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQA
public import CFSG.CGT.PushingUpLit.SolKR2.WeakInner

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

theorem exists_coboundary_of_odd_relIndex (q : CfgLemmaQ M V₀ V h C) {τ : G} (hτ : τ ∈ V)
    (hτY : τ ∈ centralizer ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G))
    (hτX : ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * τ * x⁻¹ * τ⁻¹ ∈ nVSub V₀ h ⊔ bSub V₀ h)
    (hodd : Odd ((V₀ ⊔ (nVSub V₀ h ⊔ bSub V₀ h)).relIndex (V₀ ⊔ conjSubgroup V₀ h))) :
    ∃ y ∈ nVSub V₀ h ⊔ bSub V₀ h,
      ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * τ * x⁻¹ * τ⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  let X : Subgroup G := V₀ ⊔ conjSubgroup V₀ h
  let N : Subgroup G := nVSub V₀ h ⊔ bSub V₀ h
  let S₂ : Subgroup G := V₀ ⊔ N
  have S : CFSG.RankThree.GF2n.Tim77.Prop24Setup V₀ (conjSubgroup V₀ h)
      (nVSub V₀ h) (bSub V₀ h) N := q.prop24Setup
  have hXn : ∀ z ∈ X, ∀ n ∈ N, z * n * z⁻¹ ∈ N := fun z hz n hn =>
    (Subgroup.normal_subgroupOf_iff S.M_le_X).mp S.normal_subgroupOf n z hn hz
  have hNc : ∀ m ∈ N, ∀ n ∈ N, m * n = n * m := fun m hm n hn =>
    congrArg Subtype.val (S.isElemAbelian_M.1.is_comm.comm ⟨m, hm⟩ ⟨n, hn⟩)
  have hN2 : ∀ n ∈ N, n * n = 1 := fun n hn => by
    simpa [pow_two] using S.isElemAbelian_M.2 n hn
  have hδ : ∀ z ∈ X, τ * z * τ⁻¹ * z⁻¹ ∈ N := fun z hz => by
    have h := N.inv_mem (hτX z hz)
    rwa [show (z * τ * z⁻¹ * τ⁻¹)⁻¹ = τ * z * τ⁻¹ * z⁻¹ by group] at h
  have hS : ∀ s ∈ S₂, τ * s * τ⁻¹ = s := by
    have hcentV₀ : V₀ ≤ Subgroup.centralizer ({τ} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact B2F.isElemAbelian_comm q.hyp.h6.elemAbelian (q.hyp.h6.le ha) hτ
    have hcentN : N ≤ Subgroup.centralizer ({τ} : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hτY b hb
    have hcent : S₂ ≤ Subgroup.centralizer ({τ} : Set G) := sup_le hcentV₀ hcentN
    intro s hs
    have hcomm : s * τ = τ * s := Subgroup.mem_centralizer_singleton_iff.mp (hcent hs)
    calc τ * s * τ⁻¹ = s * τ * τ⁻¹ := by rw [← hcomm]
      _ = s := by group
  have hodd' : Odd (S₂.subgroupOf X).index := by
    simpa only [S₂, X, Subgroup.relIndex] using hodd
  obtain ⟨m, hmN, hm⟩ := CFSG.CGT.PushingUpLit.SolKR2.exists_inner_of_trivial_action
    (X := X) (N := N) (S₂ := S₂) (y := τ) S.M_le_X hXn hNc hN2 hodd' hδ hS
  refine ⟨m, hmN, fun x hx => ?_⟩
  have hx' : x⁻¹ ∈ X := X.inv_mem hx
  have hx1 := hm x⁻¹ hx'
  calc x * τ * x⁻¹ * τ⁻¹ = x * (τ * x⁻¹ * τ⁻¹) := by group
    _ = x * (m * x⁻¹ * m⁻¹) := by rw [hx1]
    _ = x * m * x⁻¹ * m⁻¹ := by group

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end
