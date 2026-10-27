module

public import CFSG.Quasithin.MS93.S37Bad2

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Sp

variable {F : Type} [Field F]

theorem lam_comm_tau [CharP F 2] (a b c d : F) :
    lam a * tau (sym2_transpose b c d) * (lam a)⁻¹ * tau (sym2_transpose b c d) =
      tau (sym2_transpose (a ^ 2 * d) (a * d) 0) := by
  rw [lam_mul_tau_mul_inv, tau_mul_tau]
  refine tau_congr _ _ ?_
  rw [unitri_mul_sym2_mul_transpose]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sym2]
    linear_combination b * h2
  · simp [sym2]
    linear_combination c * h2
  · simp [sym2]
    linear_combination c * h2
  · simp [sym2]
    linear_combination d * h2

theorem mem_X₂_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (h1 : mat g (.inl 0) (.inr 1) = 0)
    (h2 : mat g (.inl 1) (.inr 1) = 0) : g ∈ X₂ F := by
  refine mem_X₂_of_sylS (Q₁_le_sylS hg) ?_ h1 h2
  rw [mat_apply_eq, hg _ (mem_ln₀.2 ⟨by simp, by simp⟩)]
  simp

end Sp

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem conj_mem_Dt_of_T1 (θ : MulAut ↥(T1 M T L)) {t x : G} (ht : t ∈ T1 M T L)
    (hx : x ∈ Dt M L θ) : t * x * t⁻¹ ∈ Dt M L θ := by
  obtain ⟨y, hyS, hyD, rfl⟩ := mem_tImage.1 hx
  set s := θ.symm ⟨t, ht⟩
  have hs : (s : G) * y * (s : G)⁻¹ ∈ Dq M L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer
      (C.h.le (T1_le_T s.2))) y).1 hyD
  refine mem_tImage.2 ⟨_, (T1 M T L).mul_mem ((T1 M T L).mul_mem s.2 hyS)
    ((T1 M T L).inv_mem s.2), hs, ?_⟩
  have e : (⟨(s : G) * y * (s : G)⁻¹, (T1 M T L).mul_mem ((T1 M T L).mul_mem s.2 hyS)
      ((T1 M T L).inv_mem s.2)⟩ : ↥(T1 M T L)) = s * ⟨y, hyS⟩ * s⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem conj_mem_rhoIm_Dt (θ : MulAut ↥(T1 M T L)) {g e : Sp4 F} (hg : g ∈ C.T0bar)
    (he : e ∈ C.rhoIm (Dt M L θ)) : g * e * g⁻¹ ∈ C.rhoIm (Dt M L θ) := by
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨d, hdK, hd, rfl⟩ := (C.mem_rhoIm).1 he
  have hc := C.conj_mem_Dt_of_T1 θ t.2 hd
  refine (C.mem_rhoIm).2 ⟨_, T1_le_sup (tImage_le θ _ hc), hc, ?_⟩
  rw [C.rho1_apply, C.rho_conj_eq (T1_le_sup t.2) hdK]

theorem relIndex_Qt_inv (θ : MulAut ↥(T1 M T L)) :
    (pCoreOf 2 M).relIndex (Qt M θ⁻¹) = (pCoreOf 2 M).relIndex (Qt M θ) := by
  have h1 := relIndex_tImage θ (C.pCore_le_T1) (tImage_le θ⁻¹ (pCoreOf 2 M))
  rw [tImage_tImage_inv' θ C.pCore_le_T1] at h1
  have c1 := Subgroup.relIndex_mul_card (Qt M θ) (pCoreOf 2 M)
  have c2 := Subgroup.relIndex_mul_card (pCoreOf 2 M) (Qt M θ)
  rw [card_tImage θ C.pCore_le_T1, inf_comm] at c2
  have hpos : 0 < Nat.card ↥(Qt M θ ⊓ pCoreOf 2 M) := Nat.card_pos
  rw [← h1]
  exact Nat.eq_of_mul_eq_mul_right hpos (c1.trans c2.symm)

theorem false_of_bad_S (hT : C.T0bar = sylS F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F)
    (hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hN := C.rhoIm_Qt_eq_T0bar θ hE hK
  obtain ⟨v, hv, hfix⟩ := C.exists_fix_Dt θ hE hK (C.sup_Qt_eq θ hN)
  set E := C.rhoIm (Dt M L θ) with hEdef
  have hcardE : Nat.card F ^ 2 ≤ Nat.card ↥E := by
    have h1 := C.card_rhoIm_Dt θ
    have h2 := C.relIndex_Qt_eq_mul θ⁻¹ hE'
    rw [C.relIndex_Qt_inv θ, ← C.card_rhoIm (Qt_le_sup θ), hN, hT, card_sylS, ← h1] at h2
    have hr := C.relIndex_le_card
    have hq : 0 < Nat.card F := Nat.card_pos
    have h3 : Nat.card F ^ 4 ≤ Nat.card F * Nat.card F * Nat.card ↥E := by
      rw [h2]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr)
    have h4 : Nat.card F ^ 2 * Nat.card F ^ 2 ≤ Nat.card F ^ 2 * Nat.card ↥E := by
      calc Nat.card F ^ 2 * Nat.card F ^ 2 = Nat.card F ^ 4 := by ring
        _ ≤ Nat.card F * Nat.card F * Nat.card ↥E := h3
        _ = Nat.card F ^ 2 * Nat.card ↥E := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  have hES : E ≤ sylS F := fun e he => by
    obtain ⟨d, hdK, hd, rfl⟩ := (C.mem_rhoIm).1 he
    rw [← hT]
    exact ⟨⟨d, tImage_le θ _ hd⟩, rfl⟩
  have hEX : ∀ e ∈ E, e ∈ X₂ F → e = 1 := by
    intro e he heX
    obtain ⟨d, hdK, hd, rfl⟩ := (C.mem_rhoIm).1 he
    exact C.rho_Dt_eq_one θ hE hE' hd hdK heX
  have hEn : ∀ g ∈ sylS F, ∀ e ∈ E, g * e * g⁻¹ ∈ E := fun g hg e he =>
    C.conj_mem_rhoIm_Dt θ (hT ▸ hg) he
  have hvW : ∀ e ∈ E, mat e *ᵥ v = v := by
    intro e he
    obtain ⟨d, hdK, hd, rfl⟩ := (C.mem_rhoIm).1 he
    exact hfix d hd
  have hWS : ∀ g ∈ sylS F, ∀ w : V4 F, (∀ e ∈ E, mat e *ᵥ w = w) →
      ∀ e ∈ E, mat e *ᵥ (mat g *ᵥ w) = mat g *ᵥ w := by
    intro g hg w hw e he
    have h1 := hw _ (hEn g⁻¹ ((sylS F).inv_mem hg) e he)
    rw [inv_inv, mat_mul_mulVec, mat_mul_mulVec] at h1
    have h2 := congrArg (fun x => mat g *ᵥ x) h1
    simp only [mat_mulVec_inv] at h2
    exact h2
  have hW1 : ∀ e ∈ E, mat e *ᵥ e₁ F = e₁ F := fun e he => sylS_mulVec_e₁ (hES he)
  have hWsub : ∀ w w' : V4 F, (∀ e ∈ E, mat e *ᵥ w = w) → (∀ e ∈ E, mat e *ᵥ w' = w') →
      ∀ c : F, ∀ e ∈ E, mat e *ᵥ (w - c • w') = w - c • w' := by
    intro w w' hw hw' c e he
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hw e he, hw' e he]
  have hW2 : ∀ e ∈ E, mat e *ᵥ e₂ F = e₂ F := by
    by_cases h3 : v (.inr 0) ≠ 0
    ·
      have hg : tau (sym2_transpose (0 : F) 1 0) ∈ sylS F := tau_mem_unipotent _
      have hw := hWS _ hg v hvW
      have hw' := hWsub _ _ hw hvW 1
      have hw'' := hWsub _ _ hw' hW1 (v (.inr 1))
      intro e he
      have h := hw'' e he
      have hval : mat (tau (sym2_transpose (0 : F) 1 0)) *ᵥ v - (1 : F) • v - v (.inr 1) • e₁ F =
          v (.inr 0) • e₂ F := by
        obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 (0 : F) 1 0 v
        refine ext4 ?_ ?_ ?_ ?_
        · simp [e0, e₁, e₂]
        · simp [e1, e₁, e₂]
        · simp [e2, e₁, e₂]
        · simp [e3, e₁, e₂]
      have h' : mat e *ᵥ (v (.inr 0) • e₂ F) = v (.inr 0) • e₂ F := by
        rw [← hval]
        exact h
      rw [Matrix.mulVec_smul] at h'
      exact smul_right_injective _ h3 h'
    · push Not at h3
      by_cases h4 : v (.inr 1) ≠ 0
      · have hg : tau (sym2_transpose (0 : F) 0 1) ∈ sylS F := tau_mem_unipotent _
        have hw' := hWsub _ _ (hWS _ hg v hvW) hvW 1
        intro e he
        have h := hw' e he
        have hval : mat (tau (sym2_transpose (0 : F) 0 1)) *ᵥ v - (1 : F) • v =
            v (.inr 1) • e₂ F := by
          obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 (0 : F) 0 1 v
          refine ext4 ?_ ?_ ?_ ?_
          · simp [e0, e₂, h3]
          · simp [e1, e₂, h3]
          · simp [e2, e₂, h3]
          · simp [e3, e₂]
        have h' : mat e *ᵥ (v (.inr 1) • e₂ F) = v (.inr 1) • e₂ F := by
          rw [← hval]
          exact h
        rw [Matrix.mulVec_smul] at h'
        exact smul_right_injective _ h4 h'
      · push Not at h4
        have h5 : v (.inl 1) ≠ 0 := fun h5 => hv (mem_pt₀.2 ⟨h5, h3, h4⟩)
        have hw' := hWsub _ _ hvW hW1 (v (.inl 0))
        intro e he
        have h := hw' e he
        have hval : v - v (.inl 0) • e₁ F = v (.inl 1) • e₂ F := by
          refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, h3, h4]
        have h' : mat e *ᵥ (v (.inl 1) • e₂ F) = v (.inl 1) • e₂ F := by
          rw [← hval]
          exact h
        rw [Matrix.mulVec_smul] at h'
        exact smul_right_injective _ h5 h'
  have hEQ : E ≤ Q₁ F := by
    intro e he w hw
    obtain ⟨h1, h2⟩ := mem_ln₀.1 hw
    have hw' : w = w (.inl 0) • e₁ F + w (.inl 1) • e₂ F := by
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, h1, h2]
    rw [hw', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hW1 e he, hW2 e he]
  let f : ↥E → F × F := fun e => (mat (e : Sp4 F) (.inl 0) (.inr 1),
    mat (e : Sp4 F) (.inl 1) (.inr 1))
  have hf : Function.Injective f := by
    intro e e' hee
    have h1 := congrArg Prod.fst hee
    have h2 := congrArg Prod.snd hee
    simp only [f] at h1 h2
    have he := hEQ e.2
    have he' := hEQ e'.2
    have hmem : (e : Sp4 F)⁻¹ * e' ∈ E := E.mul_mem (E.inv_mem e.2) e'.2
    have hX : (e : Sp4 F)⁻¹ * e' ∈ X₂ F := by
      refine mem_X₂_of_mem_Q₁ ((Q₁ F).mul_mem ((Q₁ F).inv_mem he) he') ?_ ?_
      · rw [entry_mul_of_mem_Q₁ ((Q₁ F).inv_mem he) he', entry_inv_of_mem_Q₁ he, h1]
        ring
      · rw [entry_mul_of_mem_Q₁ ((Q₁ F).inv_mem he) he', entry_inv_of_mem_Q₁ he, h2]
        ring
    have := hEX _ hmem hX
    exact Subtype.ext (inv_mul_eq_one.1 this)
  have hbij := hf.bijective_of_nat_card_le (by rw [Nat.card_prod, ← sq]; exact hcardE)
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one (show 2 < Nat.card F by
    have := C.q_ge_four; omega)
  have hcomm : ∀ (a d : F), (∃ e : ↥E, f e = (0, d)) →
      ∃ b c : F, tau (sym2_transpose (a ^ 2 * d) (a * d) 0) ∈ E ∧ b = b ∧ c = c := by
    rintro a d ⟨e, he⟩
    have heQ := hEQ e.2
    rw [Q₁_eq_radical] at heQ
    obtain ⟨Cm, hCm, hCe⟩ := heQ
    have hsym := eq_sym2 hCm
    have hd : Cm 1 1 = d := by
      have := congrArg Prod.snd he
      simp only [f, hCe] at this
      rw [mat_apply_eq, mat_tau hCm, (mulVec_blockMat_unitri 0 Cm _).2.1] at this
      · simpa using this
    refine ⟨0, 0, ?_, rfl, rfl⟩
    have h1 : lam a * (e : Sp4 F) * (lam a)⁻¹ * (e : Sp4 F) ∈ E :=
      E.mul_mem (hEn _ (lam_mem_sylS a) _ e.2) e.2
    have h2 : (e : Sp4 F) = tau (sym2_transpose (Cm 0 0) (Cm 0 1) (Cm 1 1)) := by
      rw [hCe]
      exact tau_congr _ _ hsym
    rw [h2, lam_comm_tau, hd] at h1
    exact h1
  obtain ⟨e₁', he₁'⟩ := hbij.2 (0, 1)
  obtain ⟨e₂', he₂'⟩ := hbij.2 (0, μ⁻¹)
  obtain ⟨-, -, hg₁, -, -⟩ := hcomm 1 1 ⟨e₁', he₁'⟩
  obtain ⟨-, -, hg₂, -, -⟩ := hcomm μ μ⁻¹ ⟨e₂', he₂'⟩
  have hprod := E.mul_mem hg₁ hg₂
  rw [tau_mul_tau] at hprod
  have htr : tau (C := sym2 (1 ^ 2 * 1) (1 * 1) 0 + sym2 (μ ^ 2 * μ⁻¹) (μ * μ⁻¹) 0)
      (by rw [Matrix.transpose_add, sym2_transpose, sym2_transpose]) =
      transv (e₁ F) (1 + μ) := by
    rw [transv_e₁]
    refine tau_congr _ _ ?_
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    ext i j
    fin_cases i <;> fin_cases j
    · simp [sym2]
      field_simp
    · simp [sym2, mul_inv_cancel₀ hμ0]
      linear_combination h2
    · simp [sym2, mul_inv_cancel₀ hμ0]
      linear_combination h2
    · simp [sym2]
  rw [htr] at hprod
  have h1 := hEX _ hprod (transv_mem_X₂ _)
  have h3 : transv (e₁ F) (1 + μ) = transv (e₁ F) 0 := by rw [h1, transv_zero]
  have h4 := congrFun (congrArg (fun g => mat g *ᵥ f₁ F) h3) (.inl 0)
  simp only [transv_mulVec, form_e₁] at h4
  simp [f₁, e₁] at h4
  apply hμ1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h4 - h2

end Cfg

end CFSG.Quasithin.MS93.S37
