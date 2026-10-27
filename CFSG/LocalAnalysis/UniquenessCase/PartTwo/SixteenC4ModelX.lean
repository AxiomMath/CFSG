module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4ModelOut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

include F in
theorem s16_C4ModelX_lin {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEL : E ≤ lBar V₀ V hV L)
    (hE1 : E ≠ ⊥) {Ut : Subgroup (Vtil V₀ V hV)} (hUt : Nat.card Ut * 2 = 2 ^ 8)
    (hUb : ∀ b ∈ E, b ≠ 1 → ∀ w : Vtil V₀ V hV, w ∈ Ut ↔ b w * w⁻¹ ∈ fixV E) : False := by
  obtain ⟨⟨b, hbE⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hCs : ∀ (c : F.K) (z : Fin 4 → F.K), z ∈ F.addSub (fixV E) →
      c • z ∈ F.addSub (fixV E) := by
    intro c z hz
    refine (F.mem_addSub_fixV E _).2 (fun φ hφ => ?_)
    rw [F.isLin_of_mem_lBar (hEL hφ) c z, (F.mem_addSub_fixV E z).1 hz φ hφ]
  let S : Submodule F.K (Fin 4 → F.K) :=
    { carrier := {x | F.rho b x - x ∈ F.addSub (fixV E)}
      add_mem' := fun {x y} hx hy => by
        have : F.rho b (x + y) - (x + y) = (F.rho b x - x) + (F.rho b y - y) := by
          rw [map_add]; abel
        change F.rho b (x + y) - (x + y) ∈ F.addSub (fixV E)
        rw [this]
        exact add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have : F.rho b (c • x) - c • x = c • (F.rho b x - x) := by
          rw [F.isLin_of_mem_lBar (hEL hbE) c x, smul_sub]
        change F.rho b (c • x) - c • x ∈ F.addSub (fixV E)
        rw [this]
        exact hCs c _ hx }
  have hS : ∀ x : Fin 4 → F.K, x ∈ S ↔ F.ofVec x ∈ Ut := by
    intro x
    rw [hUb b hbE hb1', ← F.vec_mem_addSub, F.vec_mul, F.vec_inv, ← F.rho_vec, F.vec_ofVec]
    simp [S, sub_eq_add_neg]
  have hcard : Nat.card Ut = Nat.card S := by
    rw [← F.card_addSub Ut]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => (F.mem_addSub Ut x).trans (hS x).symm))
  rw [hcard, Module.natCard_eq_pow_finrank (K := F.K), F.card_K] at hUt
  set k := Module.finrank F.K S with hk
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · interval_cases k <;> omega
  · have : 4 ^ 4 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) h4
    omega

include F in
theorem s16c4_modelX {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) (hE1 : E ≠ ⊥) {Ut : Subgroup (Vtil V₀ V hV)}
    (hUt : Nat.card Ut * 2 = Nat.card (Vtil V₀ V hV))
    (hUb : ∀ b ∈ E, b ≠ 1 → ∀ w : Vtil V₀ V hV, w ∈ Ut ↔ b w * w⁻¹ ∈ fixV E)
    (hcard : Nat.card E * 2 * Nat.card (fixV E) = Nat.card (Vtil V₀ V hV)) : False := by
  have hV8 : Nat.card (Vtil V₀ V hV) = 2 ^ 8 := F.card_Vtil
  rw [hV8] at hUt hcard
  by_cases hEL : E ≤ lBar V₀ V hV L
  · exact F.s16_C4ModelX_lin hEL hE1 hUt hUb
  · obtain ⟨τ, hτE, hτ⟩ := F.exists_isSemi_of_not_le hEN hE2 hEL
    have hτ2 : τ * τ = 1 := by rw [← pow_two]; exact hE2.2 τ hτE
    have hτ1 : τ ≠ 1 := by
      intro h
      subst h
      exact F.not_isSemi_of_isLin (fun c x => by simp [F.rho_one]) hτ
    have hle : fixV E ≤ fixV (Subgroup.zpowers τ) := fun w hw x hx =>
      hw x ((Subgroup.zpowers_le.2 hτE) hx)
    have hpre := F.card_preimage_of_isSemi hτ hτ2 hle (hUb τ hτE hτ1)
    have hC : Nat.card (fixV E) = 8 := by omega
    have hE16 : Nat.card E = 16 := by rw [hC] at hcard; omega
    have h2 := F.card_le_two_mul_card_inf hEN hE2 hτE hτ
    have h4 := F.s16c4_out_C_le_four hEN hE2 hτE hτ (by omega)
    omega

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
