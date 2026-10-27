module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_fixed {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G} {y : G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    (hCb : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) (hΦ : IsTorusCoord n Φ)
    (hlow : ∀ h ∈ spSignedGroup ((n + 1) / 2) 3, ∃ σ ∈ ggAutomizer K Bs, InducesSigned K ψ Φ σ h) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y := by
  intro b hfix
  have hcomm : ∀ s ∈ (halfTorus n).map ψ,
      ∀ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), Commute s c := by
    intro s hs c hc
    obtain ⟨t, _ht, rfl⟩ := Subgroup.mem_map.mp hs
    have hsK : ψ t ∈ K := by
      rw [← hψ.range]
      exact ⟨t, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hc.2 (ψ t) hsK
  have hb_mem : (b : G) ∈
      (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← hprod]
    exact b.2
  obtain ⟨s, hs, c, hc, hsc⟩ := (CFSG.mem_sup_of_commute hcomm).mp hb_mem
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  obtain ⟨a, ha⟩ := Φ.surjective ⟨t, ht⟩
  have hta : (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = t := congrArg Subtype.val ha
  have hbc : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c = (b : G) := by
    rw [hta]
    exact hsc
  have ha1 : a = 1 := by
    funext j
    have hmem : coordInv ((n + 1) / 2) 3 j ∈ spSignedGroup ((n + 1) / 2) 3 :=
      coordInv_mem_spSignedGroup j
    obtain ⟨σ, hσ, hσind⟩ := hlow (coordInv ((n + 1) / 2) 3 j) hmem
    have hσfix : σ b = b := hfix σ hσ
    have hb : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs := by
      rw [hbc]
      exact b.2
    have happ := hσind a c hb hc.2
    have hsub : (⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ : ↥Bs) = b :=
      Subtype.ext hbc
    rw [hsub, hσfix] at happ
    have heq : ψ (Φ (coordInv ((n + 1) / 2) 3 j a) :
          SpecialLinearGroup (Fin (n + 1)) F2) * c =
        ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c := by
      rw [← happ, hbc]
    have hja : coordInv ((n + 1) / 2) 3 j a = a := by
      apply Φ.injective
      apply Subtype.ext
      exact hψ.inj (mul_right_cancel heq)
    have hcoord : (a j)⁻¹ = a j := by
      have h := congrFun hja j
      rwa [coordInv_apply, Function.update_apply, if_pos rfl] at h
    exact (by decide : ∀ x : Multiplicative (ZMod 3), x⁻¹ = x → x = 1) (a j) hcoord
  have hψa : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = 1 := by
    rw [ha1]
    simp
  have hcb : (b : G) = c := by
    rw [← hbc, hψa, one_mul]
  rw [hcb, ← hCb]
  exact hc

end CFSG.StandardType

end
