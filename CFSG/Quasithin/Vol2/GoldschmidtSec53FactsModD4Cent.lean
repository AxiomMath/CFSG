module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Perf

public section

namespace CFSG.Quasithin.H13.Sec53F.TriD4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

include hσ3 in
theorem center_Q0_form {z : GL} (hzQ : z ∈ Q0 σ)
    (hzC : z ∈ Subgroup.centralizer (Q0 σ : Set GL)) :
    ∃ f : trialityFixedField K τ₀, z = ox₆ σ f := by
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_radical_a0_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q0 σ,
      ⁅ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hb : b = 0 := by
    have h1 := hcent _ (ox₅_mem_Q0 σ hσ3 (1 : trialityFixedField K τ₀))
    have e1 : ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₂ σ b * (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₅ σ 1) :=
      (((comm35 σ hσ3 c 1).mul_left (comm45 σ hσ3 d 1)).mul_left
        (commute_of_add (ox₅ σ) (ox₅_add σ hσ3) e 1)).mul_left (comm56 σ hσ3 1 f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), rel25 σ hσ3] at h1
    have := ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
    exact (mul_one b).symm.trans this
  subst hb
  have hc : c = 0 := by
    apply trace_nondeg σ hσ3
    intro t
    have h1 := hcent _ (ox₄_mem_Q0 σ hσ3 t)
    have e1 : ox₂ σ 0 * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        ox₂ σ 0 * ox₃ σ c * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0) (ox₄ σ t) := comm24 σ hσ3 0 t
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    have hAy : Commute (ox₂ σ 0) ⁅ox₃ σ c, ox₄ σ t⁆ := by
      rw [rel34 σ hσ3]
      exact comm26 σ hσ3 0 _
    rw [e1, comm_sandwich hA hB hAy, rel34 σ hσ3] at h1
    exact ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₃_mem_Q0 σ hσ3 s)
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0) * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0) (ox₃ σ s) :=
      (comm23 σ hσ3 0 s).mul_left (commute_of_add (ox₃ σ) (ox₃_add σ hσ3) 0 s)
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₃ σ s) :=
      (comm35 σ hσ3 s e).symm.mul_left (comm36 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₃ σ s⁆ = (ox₆ σ (trialityTrace K τ₀ hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel34 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0) ⁅ox₄ σ d, ox₃ σ s⁆ := by
      rw [hinv]
      exact ((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (trialityTrace K τ₀ hσ3 (s * d)) = 1 := inv_eq_one.1 h1
    exact ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
  subst hd
  have he : e = 0 := by
    have h1 := hcent _ (ox₂_mem_Q0 σ hσ3 (1 : trialityFixedField K τ₀))
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) * ox₅ σ e * ox₆ σ f := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) (ox₂ σ 1) :=
      (((commute_of_add (ox₂ σ) (ox₂_add σ hσ3) 0 1).mul_left (comm23 σ hσ3 1 0).symm).mul_left
        (comm24 σ hσ3 1 0).symm)
    have hB : Commute (ox₆ σ f) (ox₂ σ 1) := (comm26 σ hσ3 1 f).symm
    have hinv : ⁅ox₅ σ e, ox₂ σ 1⁆ = (ox₆ σ (1 * e))⁻¹ := by
      rw [← commutatorElement_inv, rel25 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) ⁅ox₅ σ e, ox₂ σ 1⁆ := by
      rw [hinv]
      exact (((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).mul_left
        (comm46 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (1 * e) = 1 := inv_eq_one.1 h1
    have := ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
    exact (one_mul e).symm.trans this
  subst he
  refine ⟨f, ?_⟩
  rw [ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, ox₅_zero σ hσ3]
  simp

include hσ3 in
theorem center_Q1_form {z : GL} (hzQ : z ∈ Q1 σ)
    (hzC : z ∈ Subgroup.centralizer (Q1 σ : Set GL)) :
    ∃ e f : trialityFixedField K τ₀, z = ox₅ σ e * ox₆ σ f := by
  obtain ⟨a, c, d, e, f, rfl⟩ := (mem_radical_a1_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q1 σ,
      ⁅ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hac : ∀ t : K, trialityTrace K τ₀ hσ3 (a * t) = 0 ∧ trialityTrace K τ₀ hσ3 (c * t) = 0 := by
    intro t
    have h1 := hcent _ (ox₄_mem_Q1 σ hσ3 t)
    have e1 : ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * (ox₁ σ a * ox₃ σ c) * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _)] at h1
    have e2 : ⁅ox₁ σ a * ox₃ σ c, ox₄ σ t⁆ =
        ox₁ σ a * ⁅ox₃ σ c, ox₄ σ t⁆ * (ox₁ σ a)⁻¹ * ⁅ox₁ σ a, ox₄ σ t⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e2, rel34 σ hσ3, rel14 σ hσ3, (comm16 σ hσ3 a _).eq, mul_inv_cancel_right] at h1
    have h2 : ox₅ σ (trialityTrace K τ₀ hσ3 (a * t)) * ox₆ σ (trialityTrace K τ₀ hσ3 (c * t)) =
        1 := by
      rw [(comm56 σ hσ3 _ _).eq]
      exact h1
    obtain ⟨h5, h6⟩ := five_six_eq_one σ hσ3 h2
    exact ⟨h5, h6⟩
  have ha : a = 0 := trace_nondeg σ hσ3 a (fun t => (hac t).1)
  have hc : c = 0 := trace_nondeg σ hσ3 c (fun t => (hac t).2)
  subst ha
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₁_mem_Q1 σ hσ3 s)
    have e1 : ox₁ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by
      rw [ox₁_zero σ hσ3, ox₃_zero σ hσ3]
      group
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₁ σ s) :=
      (comm15 σ hσ3 s e).symm.mul_left (comm16 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₁ σ s⁆ = (ox₅ σ (trialityTrace K τ₀ hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel14 σ hσ3]
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), hinv] at h1
    exact ox₅_inj σ hσ3 ((inv_eq_one.1 h1).trans (ox₅_zero σ hσ3).symm)
  subst hd
  refine ⟨e, f, ?_⟩
  rw [ox₁_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3]
  simp

end CFSG.Quasithin.H13.Sec53F.TriD4
