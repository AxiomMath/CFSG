module

public import CFSG.Quasithin.Vol2.KGFactInspModelL
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.Quasithin.H13.KGInspOdd

open Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.GH74.GLS.IVK.Proofs2
  CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.SubgroupLists
open CFSG.LieType.Steinberg (fixedSubfield)
open scoped MatrixGroups

variable {p n : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime] [CharP K p]

theorem invCentModel_psu (h : UnitaryFieldData p n K) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ n) ^ 2) :
    InvCentModel (StatedProj (StatedSU 3 (p ^ n) K))
      ↥(fixedSubfield K p n) := by
  intro w hw
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSU 3 (p ^ n) K))
    (statedProjMk_surjective _) (fun z hz => Lemma41aU3.ker_pow_three h z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  set φ := Lemma41aU3.phi h c with hφdef
  have hrange : φ.range = centralizer ({a} : Set _) := by
    rw [hφdef, Lemma41aU3.phi_range h hp2 c, hc]
  have hSU : StatedSU 2 (p ^ n) K ≤ GU2Stated (p ^ n) K := fun _ hA =>
    (Lemma41aU3.mem_GU2Stated_iff h).mpr ((mem_unitarySU_iff h).mp hA).2
  set T := (StatedSU 2 (p ^ n) K).subgroupOf (GU2Stated (p ^ n) K) with hTdef
  let eT : SL(2, ↥(fixedSubfield K p n)) ≃* ↥T :=
    (nonempty_sl2_mulEquiv_statedSU_two (r := p) (f := n) hK).some.trans
      (subgroupOfEquivOfLe hSU).symm
  have hZ3 : ∀ x : SL(2, ↥(fixedSubfield K p n)),
      x ∈ center SL(2, ↥(fixedSubfield K p n)) → x ^ 3 = 1 → x = 1 := by
    intro x hx h3
    obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
    rw [Fintype.card_fin] at hr2
    have hx3 : (x : Matrix (Fin 2) (Fin 2) ↥(fixedSubfield K p n)) ^ 3 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, h3, Matrix.SpecialLinearGroup.coe_one]
    rw [← hr, ← map_pow] at hx3
    have hr3 : r ^ 3 = 1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) _ => M 0 0) hx3
      simpa [Matrix.scalar_apply] using this
    have hr1 : r = 1 := by
      have h1 : r ^ 3 = r ^ 2 * r := by ring
      rw [hr3, hr2, one_mul] at h1
      exact h1.symm
    apply Subtype.ext
    rw [← hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hinj : ∀ t ∈ T, statedProjMk (StatedSU 3 (p ^ n) K) (φ t) = 1 → t = 1 := by
    intro t ht htk
    have htk' : φ t ∈ (statedProjMk (StatedSU 3 (p ^ n) K)).ker := htk
    have htc := mem_center_iff.mp (ker_statedProjMk_le_center _ htk')
    have ht3 : t ^ 3 = 1 :=
      Lemma41aU3.phi_injective h c (by rw [map_pow, Lemma41aU3.ker_pow_three h _ htk', map_one])
    have htcen : (⟨t, ht⟩ : ↥T) ∈ center ↥T := by
      rw [mem_center_iff]
      intro s
      apply Subtype.ext
      apply Lemma41aU3.phi_injective h c
      simp only [Subgroup.coe_mul, map_mul]
      exact htc (φ s)
    have hcen : eT.symm ⟨t, ht⟩ ∈ center SL(2, ↥(fixedSubfield K p n)) := by
      rw [mem_center_iff]
      intro B
      obtain ⟨s, rfl⟩ := eT.symm.surjective B
      rw [← map_mul, ← map_mul, mem_center_iff.mp htcen s]
    have h3' : eT.symm ⟨t, ht⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨t, ht⟩ : ↥T) ^ 3 = 1 := Subtype.ext ht3
      rw [this, map_one]
    have h2 : (⟨t, ht⟩ : ↥T) = 1 :=
      eT.symm.injective ((hZ3 _ hcen h3').trans (map_one _).symm)
    exact congrArg Subtype.val h2
  refine model_of_param (statedProjMk (StatedSU 3 (p ^ n) K)) (statedProjMk_surjective _)
    (ker_statedProjMk_le_center _) (fun z hz => Lemma41aU3.ker_pow_three h z hz) ha φ hrange T
    ⟨?_⟩ hinj (fun A B => ?_) ?_ eT
  · rintro ⟨A, hA⟩ hAS ⟨g, hg⟩
    rw [mem_subgroupOf] at hAS ⊢
    have hA' := (mem_unitarySU_iff h).mp hAS
    have hmem : g * A * g⁻¹ ∈ GU2Stated (p ^ n) K := mul_mem (mul_mem hg hA) (inv_mem hg)
    refine (mem_unitarySU_iff h).mpr ⟨?_, (Lemma41aU3.mem_GU2Stated_iff h).mp hmem⟩
    show ((g * A * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, hA'.1]
  · rw [hTdef, mem_subgroupOf]
    refine (mem_unitarySU_iff h).mpr
      ⟨?_, (Lemma41aU3.mem_GU2Stated_iff h).mp (A * B * A⁻¹ * B⁻¹).2⟩
    show (((A : GL (Fin 2) K) * B * (A : GL (Fin 2) K)⁻¹ * (B : GL (Fin 2) K)⁻¹ :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_units_conj,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  · rintro H₀ - ⟨b, hb, c, hc, hbc⟩ A hA B
    have hb' : (A : GL (Fin 2) K) * b = b * A := congrArg Subtype.val (hA b hb)
    have hc' : (A : GL (Fin 2) K) * c = c * A := congrArg Subtype.val (hA c hc)
    have hbc' : (b : GL (Fin 2) K) * c ≠ c * b := fun e => hbc (Subtype.ext e)
    exact Subtype.ext (commute_of_commute_gl hb' hc' hbc' B)

end CFSG.Quasithin.H13.KGInspOdd
