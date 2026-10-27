module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
public import CFSG.GroupTheory.TitsSystem.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Bruhat
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.BNPair
open CFSG.GroupTheory.TitsSystem (IsBNPair)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ASVolI.ChIJK (burnsideI2BN_exists_isBNPair burnsideI2BN_toPre)

theorem uc22sp207_noStrongParabolic_of_isBNPair {X : Type} [Group X] [Finite X]
    {B N : Subgroup X} [(cartan B N).Normal] {S : Set (WeylGroup B N)} (h : IsBNPair B N S)
    {U : Subgroup X} (hU2 : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hUB : U ≤ B)
    (hBU : B ≤ normalizer (U : Set X)) (hBUH : B ≤ U ⊔ (B ⊓ N)) {n₀ : X} (hn₀ : n₀ ∈ N)
    (hsup : B ⊔ B.map (MulAut.conj n₀).toMonoidHom = ⊤)
    (hcen : ∀ x ∈ N, n₀ * x * n₀⁻¹ * x⁻¹ ∈ B) : NoStrongParabolic X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, rfl⟩ : ∃ n : N, (n : X) = n₀ := ⟨⟨n₀, hn₀⟩, rfl⟩
  intro p hp hp2 Y ⟨S₂, hS₂Y⟩ hY
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hU2.toSylow hUi) S₂
  have hS₂ : (S₂ : Subgroup X) = U.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hBY : B ≤ Y.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro b hb
    have hgb : (MulAut.conj g).toMonoidHom b ∈ normalizer ((S₂ : Subgroup X) : Set X) := by
      rw [hS₂, ← map_equiv_normalizer_eq U (MulAut.conj g)]
      exact ⟨b, hBU hb, rfl⟩
    exact ⟨_, hS₂Y hgb, by simp [MulAut.conj_apply, mul_assoc]⟩
  obtain ⟨J, hJ, hPJ⟩ := h.exists_parabolic hBY
  have hYJ : IsStronglyPEmbedded p (Y.map (MulAut.conj g⁻¹).toMonoidHom) := hY.conj g⁻¹
  rw [hPJ] at hBY hYJ
  have hnJ : (n : X) ∉ parabolic B N J := by
    intro hn
    have hle : B ⊔ B.map (MulAut.conj (n : X)).toMonoidHom ≤ parabolic B N J := by
      refine sup_le hBY ?_
      rintro _ ⟨b, hb, rfl⟩
      exact mul_mem (mul_mem hn (hBY hb)) (inv_mem hn)
    rw [hsup] at hle
    exact hYJ.1 (eq_top_iff.2 hle)
  have hc : ∀ v ∈ Subgroup.closure J,
      (n : WeylGroup B N)⁻¹ * v * (n : WeylGroup B N) ∈ Subgroup.closure J := by
    intro v hv
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective v
    have h1 : ((n * m * n⁻¹ * m⁻¹ : N) : WeylGroup B N) = 1 :=
      mk_eq_one_iff.2 (by simpa using hcen m m.2)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_assoc, ← mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1), inv_mul_cancel_left]
    exact hv
  exact uc22sp207_not_isStronglyPEmbedded_of_subset_mul hU2 (hUB.trans hBY) hnJ
    (fun x hx => uc22sp207_exists_inv_mul_mem_conj h hBU hBUH hJ hc hx) hp hp2 hYJ

theorem uc22sp207_noStrongParabolic {X : Type} [Group X] [Finite X] (h : HasCentralLongest X) :
    NoStrongParabolic X := by
  obtain ⟨B, N, hBN, n₀, hn₀, hsup, hcen⟩ := h
  have : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨S, hS⟩ := burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN)
  obtain ⟨U, hUB, hUn, hU2, hUi, -, hUH, -⟩ := hBN.split
  exact uc22sp207_noStrongParabolic_of_isBNPair hS hU2 hUi hUB
    ((normal_subgroupOf_iff_le_normalizer hUB).1 hUn) hUH.ge hn₀ hsup hcen

end CFSG.LocalAnalysis.UniquenessCase.UC22
