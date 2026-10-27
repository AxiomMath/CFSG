module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4OutDesc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4ModelTv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R50c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem s16c4_out_card_sq_le {E : Subgroup (MulAut (Vtil V₀ V hV))}
    {τ : MulAut (Vtil V₀ V hV)} (hτE : τ ∈ E) (hτ : F.IsSemi τ) :
    Nat.card (fixV E) * Nat.card (fixV E) ≤
      Nat.card (fixSp (F.suSub (E ⊓ lBar V₀ V hV L))) := by
  obtain ⟨ω, hω, -⟩ := F.exists_omega
  have hC : Nat.card ↥(F.addSub (fixV E)) = Nat.card (fixV E) := F.card_addSub (fixV E)
  have hsmul : ∀ (a : ↥(SUid F.σ 4)) (y : Fin 4 → F.K), F.rho (F.π a) y = a • y :=
    fun a y => by rw [← F.vec_ofVec y, F.rho_vec, F.vec_action]
  have hmem : ∀ (c₁ : Fin 4 → F.K), c₁ ∈ F.addSub (fixV E) →
      ∀ (c₂ : Fin 4 → F.K), c₂ ∈ F.addSub (fixV E) →
      c₁ + ω • c₂ ∈ fixSp (F.suSub (E ⊓ lBar V₀ V hV L)) := by
    intro c₁ hc₁ c₂ hc₂
    rw [mem_fixSp]
    intro a ha
    have haE : (F.π a : MulAut (Vtil V₀ V hV)) ∈ E :=
      ((F.mem_suSub (E ⊓ lBar V₀ V hV L) a).1 ha).1
    have hc₁' : a • c₁ = c₁ := by
      have h := (F.mem_addSub_fixV E c₁).1 hc₁ (F.π a) haE
      rwa [hsmul a c₁] at h
    have hc₂' : a • c₂ = c₂ := by
      have h := (F.mem_addSub_fixV E c₂).1 hc₂ (F.π a) haE
      rwa [hsmul a c₂] at h
    calc a • (c₁ + ω • c₂) = a • c₁ + a • (ω • c₂) := smul_add a c₁ (ω • c₂)
      _ = c₁ + ω • (a • c₂) := by rw [hc₁', smul_comm]
      _ = c₁ + ω • c₂ := by rw [hc₂']
  let f : ↥(F.addSub (fixV E)) × ↥(F.addSub (fixV E)) →
      ↥(fixSp (F.suSub (E ⊓ lBar V₀ V hV L))) :=
    fun p => ⟨p.1.1 + ω • p.2.1, hmem p.1.1 p.1.2 p.2.1 p.2.2⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ ⟨⟨c₁', hc₁'⟩, ⟨c₂', hc₂'⟩⟩ h
    dsimp only [f] at h
    have h' : c₁ + ω • c₂ = c₁' + ω • c₂' := congrArg Subtype.val h
    have hd₁ : c₁ - c₁' ∈ F.addSub (fixV E) := (F.addSub (fixV E)).sub_mem hc₁ hc₁'
    have hd₂ : c₂' - c₂ ∈ F.addSub (fixV E) := (F.addSub (fixV E)).sub_mem hc₂' hc₂
    have hd : c₁ - c₁' = ω • (c₂' - c₂) := by
      apply add_right_cancel (b := c₁' + ω • c₂)
      calc (c₁ - c₁') + (c₁' + ω • c₂) = c₁ + ω • c₂ := by abel
        _ = c₁' + ω • c₂' := h'
        _ = ω • (c₂' - c₂) + (c₁' + ω • c₂) := by rw [smul_sub]; abel
    have hr : F.rho τ (c₂' - c₂) = c₂' - c₂ :=
      (F.mem_addSub_fixV E (c₂' - c₂)).1 hd₂ τ hτE
    have hr₁ : F.rho τ (c₁ - c₁') = c₁ - c₁' :=
      (F.mem_addSub_fixV E (c₁ - c₁')).1 hd₁ τ hτE
    have hωr : F.rho τ (ω • (c₂' - c₂)) = ω • (c₂' - c₂) := by
      rw [← hd]; exact hr₁
    have hd₂0 : c₂' - c₂ = 0 := F.descent_inter hτ hω hr hωr
    have hd₁0 : c₁ - c₁' = 0 := by rw [hd, hd₂0, smul_zero]
    have hc₁eq : c₁ = c₁' := sub_eq_zero.mp hd₁0
    have hc₂eq : c₂' = c₂ := sub_eq_zero.mp hd₂0
    exact Prod.ext (Subtype.ext hc₁eq) (Subtype.ext hc₂eq).symm
  calc Nat.card (fixV E) * Nat.card (fixV E)
      = Nat.card ↥(F.addSub (fixV E)) * Nat.card ↥(F.addSub (fixV E)) := by rw [hC]
    _ = Nat.card (↥(F.addSub (fixV E)) × ↥(F.addSub (fixV E))) :=
        (Nat.card_prod (↥(F.addSub (fixV E))) (↥(F.addSub (fixV E)))).symm
    _ ≤ Nat.card ↥(fixSp (F.suSub (E ⊓ lBar V₀ V hV L))) :=
        Nat.card_le_card_of_injective f hf_inj

theorem s16c4_out_C_le_four {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) {τ : MulAut (Vtil V₀ V hV)} (hτE : τ ∈ E) (hτ : F.IsSemi τ)
    (h3 : 3 ≤ Nat.card (E ⊓ lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV)))) :
    Nat.card (fixV E) ≤ 4 := by
  let E₀ : Subgroup (MulAut (Vtil V₀ V hV)) := E ⊓ lBar V₀ V hV L
  have hE0 : IsElemAbelian2 E₀ :=
    ⟨fun a ha b hb => hE2.1 a ha.1 b hb.1, fun a ha => hE2.2 a ha.1⟩
  have hle0 : E₀ ≤ lBar V₀ V hV L := inf_le_right
  obtain ⟨hsq, hcomm⟩ := F.suSub_sq_comm hle0 hE0
  have hcard0 : Nat.card (F.suSub E₀) = Nat.card E₀ := F.card_suSub hle0
  have h3' : 3 ≤ Nat.card (F.suSub E₀) := by rw [hcard0]; exact h3
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  have hfixle : Module.finrank F.K ↥(fixSp (F.suSub E₀)) ≤ 2 := by
    rcases card_cases (F := F.K) (σ := F.σ) F.isUnitary hsq hcomm (n := 1) le_rfl hF with
      ⟨h0, hlt⟩ | ⟨h1, hlt⟩ | ⟨h2, _⟩ | ⟨h3c, _⟩
    · omega
    · omega
    · have hadd := finrank_commSp_add_finrank_fixSp (F := F.K) (σ := F.σ) F.isUnitary hsq
      omega
    · have hadd := finrank_commSp_add_finrank_fixSp (F := F.K) (σ := F.σ) F.isUnitary hsq
      omega
  have hcardfix : Nat.card ↥(fixSp (F.suSub E₀)) =
      Nat.card F.K ^ Module.finrank F.K ↥(fixSp (F.suSub E₀)) :=
    Module.natCard_eq_pow_finrank
  have h16 : Nat.card ↥(fixSp (F.suSub E₀)) ≤ 16 := by
    rw [hcardfix, F.card_K]
    calc 4 ^ Module.finrank F.K ↥(fixSp (F.suSub E₀)) ≤ 4 ^ 2 :=
          Nat.pow_le_pow_right (n := 4) (by norm_num) hfixle
      _ = 16 := by norm_num
  have hmul : Nat.card (fixV E) * Nat.card (fixV E) ≤ 4 * 4 :=
    (F.s16c4_out_card_sq_le hτE hτ).trans (by simpa using h16)
  exact Nat.mul_self_le_mul_self_iff.mp hmul

include F in
theorem s16c4_card_le_sixteen {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEN : E ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
    (hE2 : IsElemAbelian2 E) : Nat.card E ≤ 2 ^ 4 := by
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  by_cases hle : E ≤ lBar V₀ V hV L
  · obtain ⟨hsq, hcomm⟩ := F.suSub_sq_comm hle hE2
    have h := card_le_two_pow_four (F := F.K) (σ := F.σ) F.isUnitary hsq hcomm
      (n := 1) le_rfl hF
    rw [F.card_suSub hle] at h
    simpa using h
  · obtain ⟨τ, hτE, hτ⟩ := F.exists_isSemi_of_not_le hEN hE2 hle
    let E₀ : Subgroup (MulAut (Vtil V₀ V hV)) := E ⊓ lBar V₀ V hV L
    have hE0 : IsElemAbelian2 E₀ :=
      ⟨fun a ha b hb => hE2.1 a ha.1 b hb.1, fun a ha => hE2.2 a ha.1⟩
    have hle0 : E₀ ≤ lBar V₀ V hV L := inf_le_right
    have hleE : Nat.card E ≤ 2 * Nat.card E₀ := F.card_le_two_mul_card_inf hEN hE2 hτE hτ
    obtain ⟨hsq, hcomm⟩ := F.suSub_sq_comm hle0 hE0
    have hcard0_le : Nat.card E₀ ≤ 2 ^ 4 := by
      have h := card_le_two_pow_four (F := F.K) (σ := F.σ) F.isUnitary hsq hcomm
        (n := 1) le_rfl hF
      rw [F.card_suSub hle0] at h
      simpa using h
    have hE0pg : IsPGroup 2 ↥E₀ := E3.isPGroup_of_isElemAbelian2 hE0
    have hE0card : Nat.card E₀ = 2 ^ rk E₀ := card_eq_two_pow_of_isPGroup hE0pg
    by_cases hk : rk E₀ ≤ 3
    · have hE03 : Nat.card E₀ ≤ 2 ^ 3 := by
        rw [hE0card]
        exact Nat.pow_le_pow_right (n := 2) (by norm_num) hk
      calc Nat.card E ≤ 2 * Nat.card E₀ := hleE
        _ ≤ 2 * 2 ^ 3 := Nat.mul_le_mul_left 2 hE03
        _ = 2 ^ 4 := by norm_num
    · have hk4 : 4 ≤ rk E₀ := by omega
      have hge : 2 ^ 4 ≤ Nat.card E₀ := by
        rw [hE0card]
        exact Nat.pow_le_pow_right (n := 2) (by norm_num) hk4
      have hcard4 : Nat.card E₀ = 2 ^ 4 := le_antisymm hcard0_le hge
      have hcard : Nat.card ↥(F.suSub E₀) = 2 ^ (4 * 1) := by
        rw [F.card_suSub hle0, hcard4]
      have hθ : F.σ.toRingHom = RingHom.id F.K :=
        s16_C4ModelTv_theta_eq_id (F := F.K) (σ := F.σ) F.isUnitary F.two_eq_zero hsq hcomm
          (n := 1) le_rfl hF hcard (F.rho τ).toAddMonoidHom F.σ.toRingHom
          (fun c x => by
            show F.rho τ (c • x) = F.σ c • F.rho τ x
            rw [hτ c x, F.sigma_apply])
          (F.rho τ).injective
          (fun a ha x => by
            have haE : (F.π a : MulAut (Vtil V₀ V hV)) ∈ E := ((F.mem_suSub E₀ a).1 ha).1
            have hcommτ : τ * (F.π a) = (F.π a) * τ := hE2.1 τ hτE (F.π a) haE
            have hsmul : ∀ y : Fin 4 → F.K, F.rho (F.π a) y = a • y :=
              fun y => by rw [← F.vec_ofVec y, F.rho_vec, F.vec_action]
            show F.rho τ (a • x) = a • F.rho τ x
            calc F.rho τ (a • x) = F.rho τ (F.rho (F.π a) x) := by rw [hsmul x]
              _ = F.rho (τ * (F.π a)) x := (F.rho_mul τ (F.π a) x).symm
              _ = F.rho ((F.π a) * τ) x := by rw [hcommτ]
              _ = F.rho (F.π a) (F.rho τ x) := F.rho_mul (F.π a) τ x
              _ = a • F.rho τ x := hsmul (F.rho τ x))
      obtain ⟨ω, hω, -⟩ := F.exists_omega
      have hσω : F.σ ω = ω := by
        have := congrArg (fun f : F.K →+* F.K => f ω) hθ
        simpa using this
      have hω2 : ω ^ 2 = ω := (F.sigma_apply ω).symm.trans hσω
      have hsum : ω + ω + 1 = 0 := by
        have h := hω
        rw [hω2] at h
        exact h
      have hzero : ω + ω = 0 := by rw [← two_mul, F.two_eq_zero, zero_mul]
      have h1 : (1 : F.K) = 0 := by
        have h := hsum
        rw [hzero, zero_add] at h
        exact h
      exact (one_ne_zero h1).elim

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
