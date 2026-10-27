module

public import CFSG.Quasithin.H13.L32NLem1444j

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

theorem mat_cube_cases : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * A * A ≠ 1 ∨
    B * B * B ≠ 1 ∨ B = 1 ∨ A = 1 ∨ A = B ∨ A = B * B := by
  decide +kernel

section LinAlg

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {P : Submodule (ZMod 2) W}

theorem eq_pow_of_cube (b : Module.Basis (Fin 2) (ZMod 2) P) {k c : W →ₗ[ZMod 2] W}
    (hk : ∀ w ∈ P, k w ∈ P) (hc : ∀ w ∈ P, c w ∈ P) (hk3 : ∀ w ∈ P, k (k (k w)) = w)
    (hc3 : ∀ w ∈ P, c (c (c w)) = w) (hc1 : ∃ w ∈ P, c w ≠ w) :
    (∀ w ∈ P, k w = w) ∨ (∀ w ∈ P, k w = c w) ∨ (∀ w ∈ P, k w = c (c w)) := by
  set e := LinearMap.toMatrixAlgEquiv b
  set K : Module.End (ZMod 2) P := k.restrict hk
  set C : Module.End (ZMod 2) P := c.restrict hc
  have hK : K * K * K = 1 := LinearMap.ext fun ⟨w, hw⟩ => Subtype.ext (hk3 w hw)
  have hC : C * C * C = 1 := LinearMap.ext fun ⟨w, hw⟩ => Subtype.ext (hc3 w hw)
  have hC1 : C ≠ 1 := fun h => by
    obtain ⟨w, hw, hcw⟩ := hc1
    exact hcw (congrArg Subtype.val (LinearMap.congr_fun h ⟨w, hw⟩))
  have hA : e K * e K * e K = 1 := by rw [← map_mul, ← map_mul, hK, map_one]
  have hB : e C * e C * e C = 1 := by rw [← map_mul, ← map_mul, hC, map_one]
  have hB1 : e C ≠ 1 := fun h => hC1 (e.injective (h.trans (map_one e).symm))
  rcases mat_cube_cases (e K) (e C) with h | h | h | h | h | h
  · exact absurd hA h
  · exact absurd hB h
  · exact absurd h hB1
  · have h' : K = 1 := e.injective (h.trans (map_one e).symm)
    exact Or.inl fun w hw => congrArg Subtype.val (LinearMap.congr_fun h' ⟨w, hw⟩)
  · have h' : K = C := e.injective h
    exact Or.inr (Or.inl fun w hw => congrArg Subtype.val (LinearMap.congr_fun h' ⟨w, hw⟩))
  · have h' : K = C * C := e.injective (h.trans (map_mul e C C).symm)
    exact Or.inr (Or.inr fun w hw => congrArg Subtype.val (LinearMap.congr_fun h' ⟨w, hw⟩))

end LinAlg

variable {G : Type} [Group G] [Finite G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

omit S in
theorem rho_comm_of_comm_mem (S : Setup4 G T L V V₂ g D Q₁ Q₂) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G))
    (hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G))
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (l32nH T V)) (w : D.V) :
    D.ρ ⟨x, hxN⟩ (D.ρ ⟨y, hyN⟩ w) = D.ρ ⟨y, hyN⟩ (D.ρ ⟨x, hxN⟩ w) := by
  have hcN : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).mul_mem hxN hyN) ((Subgroup.normalizer _).inv_mem hxN))
      ((Subgroup.normalizer _).inv_mem hyN)
  have h1 := S.rho_eq_one_of_mem_Q hxy hcN
  have h2 : D.ρ ⟨x * y * x⁻¹ * y⁻¹, hcN⟩ =
      D.ρ ⟨x, hxN⟩ * D.ρ ⟨y, hyN⟩ * (D.ρ ⟨x, hxN⟩)⁻¹ * (D.ρ ⟨y, hyN⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [h2] at h1
  have h3 : D.ρ ⟨x, hxN⟩ * D.ρ ⟨y, hyN⟩ = D.ρ ⟨y, hyN⟩ * D.ρ ⟨x, hxN⟩ := by
    calc D.ρ ⟨x, hxN⟩ * D.ρ ⟨y, hyN⟩ = (D.ρ ⟨x, hxN⟩ * D.ρ ⟨y, hyN⟩ * (D.ρ ⟨x, hxN⟩)⁻¹ *
          (D.ρ ⟨y, hyN⟩)⁻¹) * (D.ρ ⟨y, hyN⟩ * D.ρ ⟨x, hxN⟩) := by group
      _ = D.ρ ⟨y, hyN⟩ * D.ρ ⟨x, hxN⟩ := by rw [h1, one_mul]
  exact congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) h3

theorem inv_mul_mem_Q_of_eq_on {σ e k : G} (hσH : σ ∈ l32nH T V) (hσ2 : σ * σ = 1)
    (h21 : ∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁) (heH : e ∈ l32nH T V) (hkH : k ∈ l32nH T V)
    (hσe : σ * e * σ⁻¹ * e⁻¹ ∈ pCoreOf 2 (l32nH T V))
    (hσk : σ * k * σ⁻¹ * k⁻¹ ∈ pCoreOf 2 (l32nH T V))
    (hon : ∀ (heN : e ∈ Subgroup.normalizer (fsuU T V : Set G))
      (hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G)), ∀ w ∈ D.hat Q₁,
      D.ρ ⟨k, hkN⟩ w = D.ρ ⟨e, heN⟩ w) :
    e⁻¹ * k ∈ pCoreOf 2 (l32nH T V) := by
  have hHN : l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V
  have hσN := hHN hσH
  have heN := hHN heH
  have hkN := hHN hkH
  set ρσ := D.ρ ⟨σ, hσN⟩ with hρσ
  set ρe := D.ρ ⟨e, heN⟩ with hρe
  set ρk := D.ρ ⟨k, hkN⟩ with hρk
  have hρσ2 : ∀ w, ρσ (ρσ w) = w := by
    intro w
    have h1 : ρσ * ρσ = 1 := by
      rw [hρσ, ← map_mul]
      rw [show (⟨σ, hσN⟩ * ⟨σ, hσN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 from
        Subtype.ext hσ2, map_one]
    exact congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) h1
  have hσ₂ : ∀ w ∈ D.hat Q₂, ρσ w ∈ D.hat Q₁ := fun w hw => by
    obtain ⟨q, hq, hqU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
    rw [hρσ, D.ρ_π _ q hqU]
    exact L128A.HatU.π_mem_hat D (h21 q hq) (L128A.HatU.conj_mem hσN hqU)
  have hce := rho_comm_of_comm_mem S hσN heN hσe
  have hck := rho_comm_of_comm_mem S hσN hkN hσk
  have hon₁ := hon heN hkN
  have hon₂ : ∀ w ∈ D.hat Q₂, ρk w = ρe w := by
    intro w hw
    calc ρk w = ρk (ρσ (ρσ w)) := by rw [hρσ2]
      _ = ρσ (ρk (ρσ w)) := (hck _).symm
      _ = ρσ (ρe (ρσ w)) := by rw [hon₁ _ (hσ₂ w hw)]
      _ = ρe (ρσ (ρσ w)) := hce _
      _ = ρe w := by rw [hρσ2]
  have hall : ∀ w, ρk w = ρe w := by
    intro w
    have hw : w ∈ D.hat Q₁ ⊔ D.hat Q₂ := S.hat_Q_sup ▸ Submodule.mem_top
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, map_add, hon₁ w₁ hw₁, hon₂ w₂ hw₂]
  have hekN : e⁻¹ * k ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem heN) hkN
  have hρ : D.ρ ⟨e⁻¹ * k, hekN⟩ = 1 := by
    have h1 : D.ρ ⟨e⁻¹ * k, hekN⟩ = ρe⁻¹ * ρk := by
      rw [hρe, hρk, ← map_inv, ← map_mul]
      rfl
    rw [h1]
    refine LinearEquiv.ext fun w => ?_
    show ρe⁻¹ (ρk w) = w
    rw [hall w]
    exact ρe.symm_apply_apply w
  rw [← S.cHat]
  exact (L14332.rho_eq_one_iff_mem (D := D)
    ((l32nH T V).mul_mem ((l32nH T V).inv_mem heH) hkH) hekN).mp hρ

theorem exists_pow_inv_mul_mem_Q {σ c k : G} (hσH : σ ∈ l32nH T V) (hσ2 : σ * σ = 1)
    (h21 : ∀ q ∈ Q₂, σ * q * σ⁻¹ ∈ Q₁)
    (hcK : c ∈ oTwoUpper (l32nH T V))
    (hcfpf : ∀ (hcN : c ∈ Subgroup.normalizer (fsuU T V : Set G)) (w : D.V),
      D.ρ ⟨c, hcN⟩ w = w → w = 0)
    (hσc : σ * c * σ⁻¹ * c⁻¹ ∈ pCoreOf 2 (l32nH T V)) (hkK : k ∈ oTwoUpper (l32nH T V))
    (hσk : σ * k * σ⁻¹ * k⁻¹ ∈ pCoreOf 2 (l32nH T V)) :
    ∃ j : ℕ, (c ^ j)⁻¹ * k ∈ pCoreOf 2 (l32nH T V) := by
  have hHN : l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V
  have hKH : oTwoUpper (l32nH T V) ≤ l32nH T V := oTwoUpper_le _
  have hσN := hHN hσH
  have hcN := hHN (hKH hcK)
  have hkN := hHN (hKH hkK)
  set ρσ := D.ρ ⟨σ, hσN⟩ with hρσ
  set ρc := D.ρ ⟨c, hcN⟩ with hρc
  set ρk := D.ρ ⟨k, hkN⟩ with hρk
  have hρσ2 : ∀ w, ρσ (ρσ w) = w := by
    intro w
    have h1 : ρσ * ρσ = 1 := by
      rw [hρσ, ← map_mul]
      rw [show (⟨σ, hσN⟩ * ⟨σ, hσN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 from
        Subtype.ext hσ2, map_one]
    exact congrArg (fun γ : D.V ≃ₗ[ZMod 2] D.V => γ w) h1
  have hσ₂ : ∀ w ∈ D.hat Q₂, ρσ w ∈ D.hat Q₁ := fun w hw => by
    obtain ⟨q, hq, hqU, rfl⟩ := (L128A.HatU.mem_hat D).mp hw
    rw [hρσ, D.ρ_π _ q hqU]
    exact L128A.HatU.π_mem_hat D (h21 q hq) (L128A.HatU.conj_mem hσN hqU)
  have hk₁ : ∀ w ∈ D.hat Q₁, ρk w ∈ D.hat Q₁ := fun w hw => Setup3.rho_mem_hat hkN
    (fun a ha => (Subgroup.mem_normalizer_iff.mp (S.K_norm hkK).1 a).mp ha) hw
  have hc₁ : ∀ w ∈ D.hat Q₁, ρc w ∈ D.hat Q₁ := fun w hw => Setup3.rho_mem_hat hcN
    (fun a ha => (Subgroup.mem_normalizer_iff.mp (S.K_norm hcK).1 a).mp ha) hw
  have hc1 : ∃ w ∈ D.hat Q₁, ρc w ≠ w := by
    have h4 := S.card_hat_Q₁
    have : Nontrivial ↥(D.hat Q₁) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [h4]; norm_num)
    obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : ↥(D.hat Q₁))
    refine ⟨w, hw, fun h => hw0 ?_⟩
    exact Subtype.ext (hcfpf hcN w h)
  have hcH := hKH hcK
  have hkH := hKH hkK
  rcases eq_pow_of_cube S.basis₁ (k := ρk.toLinearMap) (c := ρc.toLinearMap) hk₁ hc₁
      (fun w _ => S.rho_cube_of_mem_K hkK hkN w) (fun w _ => S.rho_cube_of_mem_K hcK hcN w)
      hc1 with h | h | h
  · refine ⟨0, ?_⟩
    rw [pow_zero]
    refine inv_mul_mem_Q_of_eq_on S hσH hσ2 h21 (l32nH T V).one_mem hkH
      (by simp) hσk (fun he hk w hw => ?_)
    rw [show (⟨1, he⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 from rfl, map_one]
    exact h w hw
  · refine ⟨1, ?_⟩
    rw [pow_one]
    exact inv_mul_mem_Q_of_eq_on S hσH hσ2 h21 hcH hkH hσc hσk fun _ _ w hw => h w hw
  · refine ⟨2, ?_⟩
    refine inv_mul_mem_Q_of_eq_on S hσH hσ2 h21 ((l32nH T V).pow_mem hcH 2) hkH
      (Setup3.comm_pow_mem_Q hcH hσc 2) hσk (fun he hk w hw => ?_)
    have h2 : D.ρ ⟨c ^ 2, he⟩ = ρc * ρc := by
      rw [hρc, ← map_mul]
      exact congrArg D.ρ (Subtype.ext (pow_two c))
    rw [h2]
    exact h w hw

end Setup

end L1444CTL

end CFSG.Quasithin.H13
