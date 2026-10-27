module

public import CFSG.Quasithin.Vol2.Ch11SecO1bE
public import CFSG.Quasithin.Vol2.Ch11SecO1bP
public import CFSG.Quasithin.Vol2.Ch11SecO1bQ
public import CFSG.Quasithin.Vol2.Ch11SecDFacts2
public import CFSG.Quasithin.Vol2.Ch11SecAKA9
public import CFSG.Quasithin.Vol2.Ch11SecO1bC
public import CFSG.Quasithin.Vol2.Ch11SecO1bD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin

variable {G : Type} [Group G] {V : Subgroup G} {K M : Type} [Field K] [AddCommGroup M]
  [Module K M]

theorem mem_conjSubgroup_point_iff {f : ↥V → M} {V₁ : Subgroup G} {u₀ : M}
    (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀) {y : G}
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) {A B : M → M}
    (hA : ∀ w, f (SecA.conjV V y hyV w) = A (f w)) (hBA : ∀ x, B (A x) = x)
    (hAB : ∀ x, A (B x) = x) (hAs : ∀ (c : K) x, A (c • x) = c • A x) (v : ↥V) :
    (v : G) ∈ conjSubgroup V₁ y ↔ ∃ c : K, f v = c • B u₀ := by
  have hBs : ∀ c : K, B (c • u₀) = c • B u₀ := fun c => by
    rw [← hBA (c • B u₀), hAs, hAB]
  rw [mem_conjSubgroup_iff, show y * (v : G) * y⁻¹ = ((SecA.conjV V y hyV v : ↥V) : G) by
    rw [SecA.conjV_apply_coe], hV₁]
  simp only [hA]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hBA (f v), hc, hBs]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, hAs, hAB]⟩

omit [Field K] [AddCommGroup M] [Module K M] in
theorem conjSubgroup_le {V₁ : Subgroup G} (hV₁V : V₁ ≤ V) {y : G}
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) : conjSubgroup V₁ y ≤ V := fun x hx => by
  have h := hV₁V (mem_conjSubgroup_iff.mp hx)
  have e : x = y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyV) _).mp h

theorem not_smul_of_conjSubgroup_ne {f : ↥V → M} {V₁ : Subgroup G} (hV₁V : V₁ ≤ V) {y₁ y₂ : G}
    (hy₁V : y₁ ∈ Subgroup.normalizer (V : Set G)) (hy₂V : y₂ ∈ Subgroup.normalizer (V : Set G))
    {p₁ p₂ : M} (h₁ : ∀ v : ↥V, (v : G) ∈ conjSubgroup V₁ y₁ ↔ ∃ c : K, f v = c • p₁)
    (h₂ : ∀ v : ↥V, (v : G) ∈ conjSubgroup V₁ y₂ ↔ ∃ c : K, f v = c • p₂) (hp₂ : p₂ ≠ 0)
    (hne : conjSubgroup V₁ y₁ ≠ conjSubgroup V₁ y₂) : ∀ c : K, p₂ ≠ c • p₁ := by
  intro c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hp₂ hc
  apply hne
  ext x
  constructor
  · intro hx
    have hxV := conjSubgroup_le hV₁V hy₁V hx
    obtain ⟨a, ha⟩ := (h₁ ⟨x, hxV⟩).mp hx
    exact (h₂ ⟨x, hxV⟩).mpr ⟨a * c⁻¹, by
      rw [ha, hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]⟩
  · intro hx
    have hxV := conjSubgroup_le hV₁V hy₂V hx
    obtain ⟨a, ha⟩ := (h₂ ⟨x, hxV⟩).mp hx
    exact (h₁ ⟨x, hxV⟩).mpr ⟨a * c, by rw [ha, hc, smul_smul]⟩

end CFSG.Quasithin.Vol2.Ch11.SecO1b

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecO1b
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

theorem twoPointsFact_holds : TwoPointsFact := by
  intro G _ _ T L I n V₁ hS hk hV₁ y₁ hy₁ y₂ hy₂ hne
  have := SecO1.isMulCommutative hS
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hy₁V := hS.le_normalizer hy₁
  have hy₂V := hS.le_normalizer hy₂
  rcases hk with hk | hk
  · obtain ⟨K, _, _, _, hK, π, f, hf, g, hg⟩ := exists_coord_sl3_syl hS hk
    let ρ : SpecialLinearGroup (Fin 3) K →* MulAut ↥(fsuV T I) :=
      (autOn L (fsuV T I)).subtype.comp (rho3 π)
    have hρ : ∀ x ∈ autOn L (fsuV T I), ∃ γ, ρ γ = x := fun x hx => by
      obtain ⟨γ, hγ⟩ := (rho3_bijective hf).2 ⟨x, hx⟩
      exact ⟨γ, congrArg Subtype.val hγ⟩
    have hact : ∀ γ w, f (ρ γ w) = γ • f w := fun γ w => hf.act3 γ w
    obtain ⟨δ₁, hδ₁⟩ := hρ _ (SecA.conjV_mem_autOn hy₁ hy₁V)
    obtain ⟨δ₂, hδ₂⟩ := hρ _ (SecA.conjV_mem_autOn hy₂ hy₂V)
    have hu₀ : g • (JonesParshall.e0 : Fin 3 → K) ≠ 0 := fun h => by
      have h1 : (JonesParshall.e0 : Fin 3 → K) = 0 := by
        rw [← inv_smul_smul g JonesParshall.e0, h, smul_zero]
      simpa [JonesParshall.e0] using congrFun h1 0
    have hpt : ∀ (y : G) (hyV : y ∈ Subgroup.normalizer (fsuV T I : Set G))
        (δ : SpecialLinearGroup (Fin 3) K), ρ δ = SecA.conjV (fsuV T I) y hyV →
        ∀ v : ↥(fsuV T I), (v : G) ∈ conjSubgroup V₁ y ↔
          ∃ c : K, f v = c • (δ⁻¹ • g • (JonesParshall.e0 : Fin 3 → K)) := fun y hyV δ hδ =>
      mem_conjSubgroup_point_iff (mem_V1_sl3_iff hS hK hf hg hV₁) hyV (A := (δ • ·))
        (B := (δ⁻¹ • ·)) (fun w => by rw [← hδ]; exact hact δ w) (fun x => inv_smul_smul δ x)
        (fun x => smul_inv_smul δ x) (fun c x => sl3_smul_comm δ c x)
    have hp : ∀ δ : SpecialLinearGroup (Fin 3) K, δ⁻¹ • g • (JonesParshall.e0 : Fin 3 → K) ≠ 0 :=
      fun δ h => hu₀ (by rw [← smul_inv_smul δ (g • JonesParshall.e0), h, smul_zero])
    have h12 := not_smul_of_conjSubgroup_ne hV₁V hy₁V hy₂V (hpt y₁ hy₁V δ₁ hδ₁)
      (hpt y₂ hy₂V δ₂ hδ₂) (hp δ₂) hne
    refine sup_conj_eq_of_sup_eq_top hS hV₁V ρ hρ
      (S₀ := MulAction.stabilizer _ (g • (JonesParshall.e0 : Fin 3 → K))) ?_ hy₁ hy₂ hδ₁ hδ₂ ?_
    · intro γ hγ
      rw [autOn_L1_sl3 hS hK hf hg hV₁]
      refine ⟨g⁻¹ * γ * g, ?_, ?_⟩
      · change (g⁻¹ * γ * g) • (JonesParshall.e0 : Fin 3 → K) = JonesParshall.e0
        rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hγ, inv_smul_smul]
      · change ((rho3 π (g * (g⁻¹ * γ * g) * g⁻¹) : ↥(autOn L (fsuV T I))) :
          MulAut ↥(fsuV T I)) = ρ γ
        rw [show g * (g⁻¹ * γ * g) * g⁻¹ = γ by group]
        rfl
    · rw [conjSubgroup_stabilizer, conjSubgroup_stabilizer]
      exact sup_stab3_eq_top (hp δ₁) (hp δ₂) h12
  · obtain ⟨K, _, _, _, hK, π, f, -, hf, g, hg⟩ := exists_coord_sp4_syl hS hk
    let ρ : ↥(StatedSp 2 K) →* MulAut ↥(fsuV T I) := (autOn L (fsuV T I)).subtype.comp π
    have hρ : ∀ x ∈ autOn L (fsuV T I), ∃ γ, ρ γ = x := fun x hx => by
      obtain ⟨γ, hγ⟩ := hf.onto ⟨x, hx⟩
      exact ⟨γ, congrArg Subtype.val hγ⟩
    have hact : ∀ γ w, f (ρ γ w) = mat 2 K γ *ᵥ f w := fun γ w => by
      have h := hf.act γ w
      rw [linModelNat_lin] at h
      exact h
    obtain ⟨δ₁, hδ₁⟩ := hρ _ (SecA.conjV_mem_autOn hy₁ hy₁V)
    obtain ⟨δ₂, hδ₂⟩ := hρ _ (SecA.conjV_mem_autOn hy₂ hy₂V)
    have hu₀ : mat 2 K g *ᵥ vec4 1 0 0 0 ≠ 0 := fun h => by
      have h1 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) = 0 := by
        rw [← mat_inv_mulVec g (vec4 1 0 0 0), h, Matrix.mulVec_zero]
      exact (one_ne_zero : (1 : K) ≠ 0) (congrFun h1 (.inl 0))
    have hpt : ∀ (y : G) (hyV : y ∈ Subgroup.normalizer (fsuV T I : Set G))
        (δ : ↥(StatedSp 2 K)), ρ δ = SecA.conjV (fsuV T I) y hyV →
        ∀ v : ↥(fsuV T I), (v : G) ∈ conjSubgroup V₁ y ↔
          ∃ c : K, f v = c • (mat 2 K δ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) := fun y hyV δ hδ =>
      mem_conjSubgroup_point_iff (mem_V1_sp4_iff hS hK hf hg hV₁) hyV
        (A := (mat 2 K δ *ᵥ ·)) (B := (mat 2 K δ⁻¹ *ᵥ ·)) (fun w => by rw [← hδ]; exact hact δ w)
        (fun x => mat_inv_mulVec δ x) (fun x => mat_mulVec_inv δ x)
        (fun c x => Matrix.mulVec_smul _ c x)
    have hp : ∀ δ : ↥(StatedSp 2 K), mat 2 K δ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) ≠ 0 :=
      fun δ h => hu₀ (by rw [← mat_mulVec_inv δ (mat 2 K g *ᵥ vec4 1 0 0 0), h,
        Matrix.mulVec_zero])
    have h12 := not_smul_of_conjSubgroup_ne hV₁V hy₁V hy₂V (hpt y₁ hy₁V δ₁ hδ₁)
      (hpt y₂ hy₂V δ₂ hδ₂) (hp δ₂) hne
    have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four
      (four_le_card hS.one_lt hK)
    refine sup_conj_eq_of_sup_eq_top hS hV₁V ρ hρ (S₀ := stabSp (mat 2 K g *ᵥ vec4 1 0 0 0)) ?_
      hy₁ hy₂ hδ₁ hδ₂ ?_
    · intro γ hγ
      rw [autOn_L1_sp4 hS hK hf hg hV₁]
      refine ⟨g⁻¹ * γ * g, KA.mem_N0_of_fix hK4 ?_, ?_⟩
      · rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          mem_stabSp.mp hγ, mat_inv_mulVec]
      · change ((π (g * (g⁻¹ * γ * g) * g⁻¹) : ↥(autOn L (fsuV T I))) :
          MulAut ↥(fsuV T I)) = ρ γ
        rw [show g * (g⁻¹ * γ * g) * g⁻¹ = γ by group]
        rfl
    · rw [conjSubgroup_stabSp, conjSubgroup_stabSp]
      exact sup_stabSp_eq_top (hp δ₁) (hp δ₂) h12

end CFSG.Quasithin.Vol2.Ch11.SecD
