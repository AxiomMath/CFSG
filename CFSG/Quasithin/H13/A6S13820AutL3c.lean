module

public import CFSG.Quasithin.H13.A6S13820AutL3b
public import CFSG.Quasithin.H13.A6S13820AutT

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace Aut20

variable {F : Type} [Field F]

theorem autBorelU20 [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {C : Subgroup (projectiveSL 3 F)} {α : MulAut (projectiveSL 3 F)}
    (h : BorelAut13820 (projUnitriangular 3 F) C α) : (∃ g, α = MulAut.conj g) ∨ n = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hCn, hidx, ⟨k, hk⟩, hαS, hcomm⟩ := h
  have hαU : ∀ x ∈ projUnitriangular 3 F, α x ∈ projUnitriangular 3 F := fun x hx => by
    rw [← hαS]
    exact ⟨x, hx, rfl⟩
  have htor : ∀ (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1),
      (proj 3 F (diagSL20 (fun i => w i ^ 3) (pow_prod20 hw)))⁻¹ *
        α (proj 3 F (diagSL20 (fun i => w i ^ 3) (pow_prod20 hw))) ∈ projUnitriangular 3 F := by
    intro w hw
    have hmem : proj 3 F (diagSL20 w hw) ∈
        Subgroup.normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) := by
      rw [normalizer_projUnitriangular (K := F) (n := 3) 2]
      exact ⟨_, diagSL20_mem_upperTriangular w hw, rfl⟩
    rw [← proj_diagSL20_pow w hw]
    exact hcomm _ (pow_three_mem20 hCn hidx hmem)
  have hwa : ∀ a : Fˣ, ![(a : F), (a : F)⁻¹, 1] 0 * ![(a : F), (a : F)⁻¹, 1] 1 *
      ![(a : F), (a : F)⁻¹, 1] 2 = 1 := fun a => by
    show (a : F) * (a : F)⁻¹ * 1 = 1
    rw [mul_one, mul_inv_cancel₀ (Units.ne_zero a)]
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 α
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hα
    have hA : ∀ x ∈ projUnitriangular 3 F,
        LinearFlag.conjAut 3 F A x ∈ projUnitriangular 3 F := by
      intro x hx
      have e : LinearFlag.conjAut 3 F A x = α ((LinearFlag.fieldAut 3 F σ)⁻¹ x) := by
        rw [hα, MulAut.mul_apply, MulAut.apply_inv_self]
      rw [e]
      exact hαU _ (inv_apply_mem20 _ (fun y hy => fieldAut_mem20 σ hy) hx)
    obtain ⟨T, hT, v, hAv⟩ := exists_conjAut_eq20 A hA
    have hσ : ∀ a : Fˣ, σ ((a : F) ^ 3) = (a : F) ^ 3 := by
      intro a
      have h1 := htor _ (hwa a)
      rw [hα, MulAut.mul_apply, fieldAut_diagSL20, hAv] at h1
      have h3 := key_torus20 hT v _ _ _ _ h1
      have h4 : ((a : F) ^ 3)⁻¹ * σ ((a : F) ^ 3) = ((1 : F) ^ 3)⁻¹ * σ ((1 : F) ^ 3) :=
        h3.1.trans h3.2
      rw [one_pow, inv_one, map_one, mul_one] at h4
      exact ((inv_mul_eq_one₀ (pow_ne_zero 3 (Units.ne_zero a))).mp h4).symm
    rcases sigma_eq_one_of_fix_cubes20 hn hF σ hσ with rfl | h2
    · left
      rw [map_one, mul_one] at hα
      rw [hα] at hk ⊢
      exact exists_conj_of_conjAut_pow20 A hk
    · exact Or.inr h2
  ·
    right
    rw [pow_one] at hα
    obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := 3) (K := F)
    have hWσ : LinearFlag.fieldAut 3 F σ * LinearFlag.conjAut 3 F wGL20 =
        LinearFlag.conjAut 3 F wGL20 * LinearFlag.fieldAut 3 F σ := by
      have h1 := hfc σ wGL20
      rw [map_wGL20, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hWW : LinearFlag.conjAut 3 F wGL20 * LinearFlag.conjAut 3 F wGL20 = 1 := by
      rw [← map_mul, wGL20_mul_self, map_one]
    have hαB : α = LinearFlag.conjAut 3 F (A * wGL20) * LinearFlag.fieldAut 3 F σ *
        gammaAut20 := by
      rw [hα, map_mul, gammaAut20]
      calc LinearFlag.conjAut 3 F A * LinearFlag.fieldAut 3 F σ * LinearFlag.dualAut 3 F
          = LinearFlag.conjAut 3 F A * ((LinearFlag.conjAut 3 F wGL20 *
              LinearFlag.conjAut 3 F wGL20) * LinearFlag.fieldAut 3 F σ) *
              LinearFlag.dualAut 3 F := by rw [hWW, one_mul]
        _ = LinearFlag.conjAut 3 F A * LinearFlag.conjAut 3 F wGL20 *
              (LinearFlag.fieldAut 3 F σ * LinearFlag.conjAut 3 F wGL20) *
              LinearFlag.dualAut 3 F := by rw [hWσ]; simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    have hBU : ∀ x ∈ projUnitriangular 3 F,
        LinearFlag.conjAut 3 F (A * wGL20) x ∈ projUnitriangular 3 F := by
      intro x hx
      have e : LinearFlag.conjAut 3 F (A * wGL20) x =
          α (gammaAut20⁻¹ ((LinearFlag.fieldAut 3 F σ)⁻¹ x)) := by
        rw [hαB, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self,
          MulAut.apply_inv_self]
      rw [e]
      exact hαU _ (inv_apply_mem20 _ (fun y hy => gammaAut20_mem hy)
        (inv_apply_mem20 _ (fun y hy => fieldAut_mem20 σ hy) hx))
    obtain ⟨T, hT, v, hBv⟩ := exists_conjAut_eq20 (A * wGL20) hBU
    refine n_eq_two_of_pow_nine20 hn hF fun a => ?_
    have h1 := htor _ (hwa a)
    rw [hαB, MulAut.mul_apply, MulAut.mul_apply, gammaAut20_diagSL20, fieldAut_diagSL20,
      hBv] at h1
    have h3 := key_torus20 hT v _ _ _ _ h1
    have h4 : ((a : F) ^ 3)⁻¹ * σ (((1 : F) ^ 3)⁻¹) =
        (((a : F)⁻¹) ^ 3)⁻¹ * σ ((((a : F)⁻¹) ^ 3)⁻¹) := h3.1
    have h5 : (((a : F)⁻¹) ^ 3)⁻¹ * σ ((((a : F)⁻¹) ^ 3)⁻¹) =
        ((1 : F) ^ 3)⁻¹ * σ (((a : F) ^ 3)⁻¹) := h3.2
    simp only [inv_pow, inv_inv, one_pow, inv_one, map_one, mul_one, one_mul, map_inv₀] at h4 h5
    have hs : σ ((a : F) ^ 3) = (a : F) ^ 3 := inv_injective (h5.symm.trans h4.symm)
    rw [hs] at h4
    have hx0 : (a : F) ^ 3 ≠ 0 := pow_ne_zero 3 (Units.ne_zero a)
    have h6 : ((a : F) ^ 3)⁻¹ * (a : F) ^ 3 = (a : F) ^ 3 * (a : F) ^ 3 * (a : F) ^ 3 := by
      rw [h4]
    rw [inv_mul_cancel₀ hx0] at h6
    have h9 : (a : F) ^ 9 = 1 := by
      calc (a : F) ^ 9 = (a : F) ^ 3 * (a : F) ^ 3 * (a : F) ^ 3 := by ring
        _ = 1 := h6.symm
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h9, Units.val_one])

theorem autBorelP3_20 [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {S C : Subgroup (projectiveSL 3 F)} {α : MulAut (projectiveSL 3 F)}
    (h : BorelAut13820 S C α) : (∃ g, α = MulAut.conj g) ∨ n = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have hidx : ¬ 2 ∣ S.index := by
    have h2 := h.1.2.2
    rwa [show (S.subgroupOf ⊤).index = S.relIndex ⊤ from rfl, Subgroup.relIndex_top_right] at h2
  obtain ⟨g, hg⟩ := CFSG.SeitzReduction.LinearPilot.exists_conj_projUnitriangular (K := F)
    (p := 2) (n := 3) (by norm_num) (h.1.2.1.toSylow hidx)
  have hSe : S.map (MulAut.conj g⁻¹).toMonoidHom = projUnitriangular 3 F := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h1 := (hg s).1 hs
      simpa [MulAut.conj_apply] using h1
    · intro hx
      refine ⟨g * x * g⁻¹, (hg _).2 (by simpa [mul_assoc] using hx), ?_⟩
      simp [mul_assoc]
  have h' := borelAut_mulEquiv20 (MulAut.conj g⁻¹) h
  rw [hSe] at h'
  rcases autBorelU20 hn hF h' with hi | h2
  · exact Or.inl ((inner_congr_iff20 (MulAut.conj g⁻¹) α).1 hi)
  · exact Or.inr h2

end Aut20

theorem autBorel13820L3_holds : AutBorel13820L3 := by
  intro Q _ _ n hq hZ hn hL S C α h
  have hquot := Aut20.borelAut_quot20 hZ h
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hL
  let ψ : (Q ⧸ Subgroup.center Q) ≃* projectiveSL 3 F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  rcases Aut20.autBorelP3_20 hn hcard (Aut20.borelAut_mulEquiv20 ψ hquot) with hi | h2
  · left
    have : Group.IsPerfect Q := hq.1
    obtain ⟨g, hg⟩ := (Aut20.inner_congr_iff20 ψ _).1 hi
    exact Aut20.inner_of_quot20 hg
  · exact Or.inr h2

end CFSG.Quasithin.H13.A6
