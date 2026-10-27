module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4OutBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem rho_one : F.rho (1 : MulAut (Vtil V₀ V hV)) = AddEquiv.refl _ := by
  ext x : 1
  simp [rho]

theorem s16_C4ModelOut_hcom_vec {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcom : ∀ x ∈ E, x ≠ 1 → ∀ w : Vtil V₀ V hV, x w = w → ∀ y ∈ E, y w * w⁻¹ ∈ fixV E)
    {x : MulAut (Vtil V₀ V hV)} (hx : x ∈ E) (hx1 : x ≠ 1) {r : Fin 4 → F.K}
    (hr : F.rho x r = r) {y : MulAut (Vtil V₀ V hV)} (hy : y ∈ E) :
    F.rho y r - r ∈ F.addSub (fixV E) := by
  have hw : x (F.ofVec r) = F.ofVec r := by
    apply F.vec_injective
    rw [← F.rho_vec, F.vec_ofVec, hr]
  have h := hcom x hx hx1 (F.ofVec r) hw y hy
  have h' : F.vec (y (F.ofVec r) * (F.ofVec r)⁻¹) ∈ F.addSub (fixV E) :=
    (F.vec_mem_addSub _ _).2 h
  rw [F.vec_mul, F.vec_inv, ← F.rho_vec, F.vec_ofVec] at h'
  simpa [sub_eq_add_neg] using h'

theorem s16_C4ModelOut_fix_inter {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcom : ∀ x ∈ E, x ≠ 1 → ∀ w : Vtil V₀ V hV, x w = w → ∀ y ∈ E, y w * w⁻¹ ∈ fixV E)
    {τ : MulAut (Vtil V₀ V hV)} (hτE : τ ∈ E) (hτ : F.IsSemi τ)
    {y : MulAut (Vtil V₀ V hV)} (hyE : y ∈ E) (hyL : y ∈ lBar V₀ V hV L) (hy1 : y ≠ 1)
    {r : Fin 4 → F.K} (hrτ : F.rho τ r = r) (hry : F.rho y r = r) :
    r ∈ F.addSub (fixV E) := by
  obtain ⟨ω, hω, -⟩ := F.exists_omega
  have hlin := F.isLin_of_mem_lBar hyL
  have hωy : F.rho y (ω • r) = ω • r := by rw [hlin, hry]
  have h := F.s16_C4ModelOut_hcom_vec hcom hyE hy1 hωy hτE
  rw [hτ, hrτ] at h
  have h2 : ω ^ 2 • r - ω • r = -r := by
    rw [← sub_smul]
    have : ω ^ 2 - ω = -1 := by linear_combination hω - ω * F.two_eq_zero
    rw [this]
    simp
  rw [h2] at h
  simpa using h

theorem s16_C4ModelOut_exists_r0 {E : Subgroup (MulAut (Vtil V₀ V hV))}
    {τ : MulAut (Vtil V₀ V hV)} (hτ : F.IsSemi τ) (hτ2 : τ * τ = 1)
    {y : MulAut (Vtil V₀ V hV)} (hyE : y ∈ E) (hyL : y ∈ lBar V₀ V hV L) (hy1 : y ≠ 1) :
    ∃ r : Fin 4 → F.K, F.rho τ r = r ∧ r ∉ F.addSub (fixV E) := by
  by_contra hcon
  have hall : ∀ r : Fin 4 → F.K, F.rho τ r = r → r ∈ F.addSub (fixV E) := by
    intro r hr
    by_contra hn
    exact hcon ⟨r, hr, hn⟩
  obtain ⟨ω, hω, -⟩ := F.exists_omega
  have hlin := F.isLin_of_mem_lBar hyL
  have hfix : ∀ r : Fin 4 → F.K, F.rho τ r = r → F.rho y r = r := fun r hr =>
    (F.mem_addSub_fixV E r).1 (hall r hr) y hyE
  apply hy1
  ext w
  apply F.vec_injective
  rw [← F.rho_vec]
  obtain ⟨r₁, r₂, h1, h2, hx⟩ := F.descent_decomp hτ hτ2 hω (F.vec w)
  rw [hx, map_add, hlin, hfix r₁ h1, hfix r₂ h2]
  simp [← hx]

theorem s16_C4ModelOut_card_le {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcom : ∀ x ∈ E, x ≠ 1 → ∀ w : Vtil V₀ V hV, x w = w → ∀ y ∈ E, y w * w⁻¹ ∈ fixV E)
    {τ : MulAut (Vtil V₀ V hV)} (hτE : τ ∈ E) (hτ : F.IsSemi τ) (hτ2 : τ * τ = 1)
    (hy : ∃ y ∈ (E ⊓ lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))), y ≠ 1) :
    Nat.card (E ⊓ lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) ≤ Nat.card (fixV E) := by
  obtain ⟨y₀, hy₀, hy₀1⟩ := hy
  obtain ⟨r₀, hr₀τ, hr₀C⟩ := F.s16_C4ModelOut_exists_r0 (E := E) hτ hτ2 hy₀.1 hy₀.2 hy₀1
  have hτ1 : τ ≠ 1 := by
    intro h
    subst h
    exact F.not_isSemi_of_isLin (fun c x => by simp [F.rho_one]) hτ
  rw [← F.card_addSub (fixV E)]
  refine Nat.card_le_card_of_injective
    (fun y => (⟨F.rho y.1 r₀ - r₀, F.s16_C4ModelOut_hcom_vec hcom hτE hτ1 hr₀τ y.2.1⟩ :
      F.addSub (fixV E))) ?_
  intro a b hab
  have hab' : F.rho a.1 r₀ = F.rho b.1 r₀ := by
    have := congrArg Subtype.val hab
    simpa using this
  have hz : F.rho (b.1⁻¹ * a.1) r₀ = r₀ := by
    rw [F.rho_mul, hab', ← F.rho_mul]
    simp [F.rho_one]
  by_contra hne
  have hz1 : b.1⁻¹ * a.1 ≠ 1 := by
    intro h
    exact hne (Subtype.ext (inv_mul_eq_one.1 h).symm)
  exact hr₀C (F.s16_C4ModelOut_fix_inter hcom hτE hτ
    (E.mul_mem (E.inv_mem b.2.1) a.2.1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ b.2.2) a.2.2) hz1 hr₀τ hz)

include F in
theorem s16c4_modelOut {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) (hcard : 2 ^ 4 ≤ Nat.card E) (hout : ¬ E ≤ lBar V₀ V hV L)
    (hcom : ∀ x ∈ E, x ≠ 1 → ∀ w : Vtil V₀ V hV, x w = w → ∀ y ∈ E, y w * w⁻¹ ∈ fixV E) :
    False := by
  obtain ⟨τ, hτE, hτ⟩ := F.exists_isSemi_of_not_le hEN hE2 hout
  have hτ2 : τ * τ = 1 := by rw [← pow_two]; exact hE2.2 τ hτE
  have h2 := F.card_le_two_mul_card_inf hEN hE2 hτE hτ
  have h4 := F.s16c4_out_C_le_four hEN hE2 hτE hτ (by omega)
  have hy : ∃ y ∈ (E ⊓ lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))), y ≠ 1 := by
    by_contra hcon
    have hbot : (E ⊓ lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      by_contra hne
      exact hcon ⟨y, hy, hne⟩
    rw [hbot, Subgroup.card_bot] at h2
    omega
  have h3 := F.s16_C4ModelOut_card_le hcom hτE hτ hτ2 hy
  omega

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
