module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FinAEigen
import CFSG.LocalAnalysis.UniquenessCase.UC22FinAHall
import CFSG.LocalAnalysis.UniquenessCase.UC22FinAPoint
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Subgroup
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {Γ : Type} [Group Γ] [Finite Γ]

theorem fina_core (hq : 8 ≤ Nat.card K) (φ : Γ →* projectiveSL 3 K)
    (hφ : φ.range = projStabilizer (flagSpace 3 K 1))
    {Y B : Subgroup Γ} [Y.Normal] (hN2 : IsPGroup 2 ↥(φ.ker ⊓ Y)) (hperf : ⁅Y, Y⁆ = Y)
    (hns : ¬ Group.IsSolvable ↥(Y.map φ))
    (hBab : IsMulCommutative B) (hBodd : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hBker : ∀ b ∈ B, φ b = 1 → b = 1)
    {t : projectiveSL 3 K} (ht : ∀ b ∈ B, t * φ b * t⁻¹ = (φ b)⁻¹)
    (htP : t ∉ projStabilizer (flagSpace 3 K 1)) :
    ∃ A : Subgroup Γ, B ≤ A ∧ A ≤ Y ⊔ B ∧ IsMulCommutative A ∧ A ⊓ Y ⊔ B = A ∧
      A ⊓ Y ⊓ B = ⊥ ∧ Nonempty (↥(A ⊓ Y) ≃* ↥B) := by
  classical
  set N : Subgroup Γ := φ.ker ⊓ Y with hNdef
  have hNY : N ≤ Y := inf_le_right
  have hker : ∀ y ∈ Y, φ y = 1 → y ∈ N := fun y hy h => ⟨MonoidHom.mem_ker.2 h, hy⟩
  have hinjB : Function.Injective (φ.domRestrict B) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    exact Subtype.ext (hBker b b.2 hb)
  let eB : ↥B ≃* ↥(φ.domRestrict B).range := MonoidHom.ofInjective hinjB
  have hE : (φ.domRestrict B).range = B.map φ := MonoidHom.restrict_range B φ
  have hcardE : Nat.card (B.map φ) = Nat.card B := by
    rw [← hE]
    exact (Nat.card_congr eB.toEquiv).symm
  have hEab : IsMulCommutative (B.map φ) := ⟨⟨by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val (hBab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))⟩⟩
  have hEP : B.map φ ≤ projStabilizer (flagSpace 3 K 1) := hφ ▸ Subgroup.map_le_range φ B
  obtain ⟨hEcyc, hEfix, C, hCle, hCcent, hCcyc, hCcard⟩ :=
    eigen_of_inverted (B.map φ) hEP hEab (hcardE ▸ hBodd) (hcardE ▸ hB3) t
      (by rintro _ ⟨b, hb, rfl⟩; exact ht b hb) htP
  have hYP : Y.map φ ≤ projStabilizer (flagSpace 3 K 1) := hφ ▸ Subgroup.map_le_range φ Y
  have hperfX : ⁅Y.map φ, Y.map φ⁆ = Y.map φ := by rw [← Subgroup.map_commutator, hperf]
  have hnormX : projStabilizer (flagSpace 3 K 1) ≤
      Subgroup.normalizer (↑(Y.map φ) : Set (projectiveSL 3 K)) := by
    have h1 := Subgroup.le_normalizer_map (H := Y) φ
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance, ← MonoidHom.range_eq_map, hφ] at h1
    exact h1
  have hnot2 : ¬ IsPGroup 2 (Y.map φ) := fun h => hns (by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥(Y.map φ) := h.isNilpotent
    infer_instance)
  have hYX := eq_commutator_of_normal_perfect hq (Y.map φ) hYP hperfX hnormX hnot2
  have hBY : B ⊓ Y = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h1 : φ x ∈ B.map φ := Subgroup.mem_map_of_mem φ hx.1
    have h2 : φ x ∈ Y.map φ := Subgroup.mem_map_of_mem φ hx.2
    rw [hYX] at h2
    have h3 := (Subgroup.mem_inf.2 ⟨h1, h2⟩)
    rw [hEfix, Subgroup.mem_bot] at h3
    exact hBker x hx.1 h3
  have := hCcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hordg : orderOf (g : projectiveSL 3 K) = Nat.card B := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hCcard, hcardE]
  obtain ⟨y₁, hy₁, hφy₁⟩ : (g : projectiveSL 3 K) ∈ Y.map φ := hYX ▸ hCle g.2
  have hcomm : ∀ b ∈ B, y₁ * b * y₁⁻¹ * b⁻¹ ∈ N := by
    intro b hb
    apply hker
    · have hconj : b * y₁⁻¹ * b⁻¹ ∈ Y :=
        Subgroup.Normal.conj_mem inferInstance _ (Y.inv_mem hy₁) b
      simpa [mul_assoc] using Y.mul_mem hy₁ hconj
    · have hc := hCcent g g.2 (φ b) (Subgroup.mem_map_of_mem φ hb)
      simp only [map_mul, map_inv, hφy₁]
      rw [hc]
      simp
  have hu : orderOf (QuotientGroup.mk' N y₁) = Nat.card B := by
    rw [orderOf_mk_eq_orderOf_image φ hN2 hker hy₁ (by rw [hφy₁, hordg]; exact hBodd), hφy₁,
      hordg]
  have : IsCyclic ↥(φ.domRestrict B).range := by rw [hE]; exact hEcyc
  have : IsCyclic ↥B := isCyclic_of_injective eB.toMonoidHom eB.injective
  exact exists_abelian_complement hN2 hNY hBab hBodd hy₁ hcomm hBY hu

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
