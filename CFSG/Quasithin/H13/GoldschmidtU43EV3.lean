module

public import CFSG.Quasithin.H13.GoldschmidtU43EV2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem card_zpowers_σ₁ : Nat.card (Subgroup.zpowers (S.σ₁ : G)) = 3 := by
  rw [Nat.card_zpowers]
  have h3 : (S.σ₁ : G) ^ 3 = 1 := S.pow_three_Tg S.σ₁G_mem_Tg
  have h1 : (S.σ₁ : G) ≠ 1 := fun h => S.σ₁_ne_one (Subtype.ext h)
  exact orderOf_eq_prime h3 h1

theorem card_V3_ge (r : S.Rho) (hAU : (S.A : G) ∈ Uz z) {V₃ : Subgroup G}
    (hmax : ∀ T : Subgroup G, T ≤ S.Vg → IsPGroup 3 T → T ≤ V₃) (hV₃ : V₃ ≤ S.Vg) :
    243 ≤ Nat.card V₃ := by
  have hA : S.Ag r ≤ V₃ := hmax _ (S.Ag_le_Vg r hAU) (S.isPGroup_Ag r)
  have hB : S.Bg r ≤ V₃ := hmax _ (S.Bg_le_Vg r hAU) (S.isPGroup_Bg r)
  set A'' : Subgroup ↥V₃ := (S.Ag r).subgroupOf V₃ with hA''
  set B'' : Subgroup ↥V₃ := (S.Bg r).subgroupOf V₃ with hB''
  have hnorm : B''.Normal := by
    refine ⟨fun b hb g => ?_⟩
    have hbB : (b : G) ∈ S.Bg r := hb
    have hcomm := ((S.Vg_comm_mem hAU).2 ((g : G)⁻¹) (inv_mem (hV₃ g.2)) ((b : G)⁻¹)
      (inv_mem (hV₃ b.2)))
    have e : ((g : G)⁻¹)⁻¹ * ((b : G)⁻¹)⁻¹ * (g : G)⁻¹ * (b : G)⁻¹ =
        ((g : G) * b * (g : G)⁻¹) * (b : G)⁻¹ := by group
    rw [e] at hcomm
    have hσB : ((g : G) * b * (g : G)⁻¹) * (b : G)⁻¹ ∈ S.Bg r := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm
      rw [← hk]
      exact zpow_mem (S.σ₁_mem_Bg r) k
    have : (g : G) * b * (g : G)⁻¹ ∈ S.Bg r := by
      have := (S.Bg r).mul_mem hσB hbB
      simpa [mul_assoc] using this
    exact this
  have hrel : B''.relIndex (A'' ⊔ B'') = B''.relIndex A'' := Subgroup.relIndex_sup_right A'' B''
  have h1 : B''.relIndex (A'' ⊔ B'') * Nat.card ↥(B'' ⊓ (A'' ⊔ B'')) = Nat.card ↥(A'' ⊔ B'') :=
    Subgroup.relIndex_mul_card _ _
  have h2 : B''.relIndex A'' * Nat.card ↥(B'' ⊓ A'') = Nat.card A'' :=
    Subgroup.relIndex_mul_card _ _
  have e3 : B'' ⊓ (A'' ⊔ B'') = B'' := inf_eq_left.mpr le_sup_right
  rw [e3] at h1
  have hcardA : Nat.card A'' = Nat.card (S.Ag r) := by
    rw [hA'', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]
  have hcardB : Nat.card B'' = Nat.card (S.Bg r) := by
    rw [hB'', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv]
  have hA27 : 27 ≤ Nat.card A'' := by rw [hcardA]; exact S.card_Ag_ge r
  have hB27 : 27 ≤ Nat.card B'' := by rw [hcardB, S.card_Bg r]; exact S.card_Ag_ge r
  have hinf : Nat.card ↥(B'' ⊓ A'') ≤ 3 := by
    rw [← S.card_zpowers_σ₁]
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥V₃) : G), ?_⟩) ?_
    · exact S.Ag_inf_Bg r hAU x.2.2 x.2.1
    · intro a b hab
      have h : ((a : ↥V₃) : G) = ((b : ↥V₃) : G) := by
        have := congrArg (fun t : ↥(Subgroup.zpowers (S.σ₁ : G)) => (t : G)) hab
        simpa using this
      exact Subtype.ext (Subtype.ext h)
  have h4 : 9 ≤ B''.relIndex A'' := by
    have : B''.relIndex A'' * 3 ≥ 27 := by
      calc B''.relIndex A'' * 3 ≥ B''.relIndex A'' * Nat.card ↥(B'' ⊓ A'') :=
            Nat.mul_le_mul_left _ hinf
        _ = Nat.card A'' := h2
        _ ≥ 27 := hA27
    omega
  have h5 : 243 ≤ Nat.card ↥(A'' ⊔ B'') := by
    rw [← h1, hrel]
    calc 243 = 9 * 27 := by norm_num
      _ ≤ B''.relIndex A'' * Nat.card B'' := Nat.mul_le_mul h4 hB27
  exact h5.trans (Subgroup.card_le_card_group _)

theorem exists_big_three_group (hAU : (S.A : G) ∈ Uz z) :
    ∃ Q : Subgroup G, IsPGroup 3 Q ∧ 729 ≤ Nat.card Q ∧ S.Mg ≤ Q := by
  obtain ⟨r⟩ := S.nonempty_Rho
  obtain ⟨V₃, hle, hP, hmax, hconj⟩ := S.exists_V3 hAU
  have hcard := S.card_V3_ge r hAU hmax hle
  have hσ₂C : (S.σ₂ : G) ∈ S.Cg1 := by
    rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val S.σ₁σ₂_comm.symm
  have hnorm : Subgroup.zpowers (S.σ₂ : G) ≤ Subgroup.normalizer (V₃ : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hconj _ hσ₂C x hx
    · intro hx
      have := hconj _ (inv_mem hσ₂C) _ hx
      simpa [mul_assoc] using this
  have h3 : (S.σ₂ : G) ^ 3 = 1 := S.pow_three_Tg S.σ₂G_mem_Tg
  have h1 : (S.σ₂ : G) ≠ 1 := fun h => S.σ₂_ne_one (Subtype.ext h)
  have hp2 : IsPGroup 3 (Subgroup.zpowers (S.σ₂ : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime h3 h1]; norm_num)
  have hQ : IsPGroup 3 (Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ : Subgroup G) :=
    hp2.to_sup_of_normal_right' hP hnorm
  have hσQ : (S.σ₂ : G) ∈ Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hVQ : V₃ ≤ Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ := le_sup_right
  have hσV : (S.σ₂ : G) ∉ V₃ := fun h => S.σ₂_not_mem_Vg hAU (hle h)
  refine ⟨Subgroup.zpowers (S.σ₂ : G) ⊔ V₃, hQ, ?_, ?_⟩
  · set Q := Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ with hQdef
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hQ
    have hlt : Nat.card V₃ < Nat.card Q := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.eq_of_le_of_card_ge hVQ hcon
      exact hσV (this ▸ hσQ)
    have hk5 : 5 ≤ k := by
      by_contra hk5
      push Not at hk5
      have : 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hk] at hcard
      omega
    have hm6 : 6 ≤ m := by
      have : 3 ^ k < 3 ^ m := by rw [← hk, ← hm]; exact hlt
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp this
      omega
    rw [hm]
    calc 729 = 3 ^ 6 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm6
  · have hρ : r.ρ ∈ V₃ := hmax _ (S.Ag_le_Vg r hAU) (S.isPGroup_Ag r)
      (Subgroup.subset_closure (by simp))
    have hρ₂ : S.rho2 r.ρ ∈ V₃ := hmax _ (S.Ag_le_Vg r hAU) (S.isPGroup_Ag r)
      (Subgroup.subset_closure (by simp))
    have hσ₁ : (S.σ₁ : G) ∈ V₃ := hmax _ (S.Ag_le_Vg r hAU) (S.isPGroup_Ag r) (S.σ₁_mem_Ag r)
    have hσ₂ : (S.σ₂ : G) ∈ Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ := hσQ
    have hσ₁Q : (S.σ₁ : G) ∈ Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ := hVQ hσ₁
    refine (S.Mg_le_closure r).trans ?_
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · rw [sigG_eq]
      exact mul_mem hσ₁Q hσ₂
    · rw [sigp_eq]
      exact mul_mem hσ₁Q (inv_mem hσ₂)
    · exact hVQ hρ
    · exact hVQ hρ₂

end JWSetup

end CFSG.Quasithin.H13.U43
