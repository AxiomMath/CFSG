module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open Subgroup
open CFSG.Blueprint (LieModel)

private theorem lieModel_quot_center_of_szL2 {P A : Type} [Group P] [Group A]
    (e : P ≃* A) (hP : CFSG.Open.IsQuasisimple P) {n : ℕ} (hA : IsSz A n ∨ IsL2 A n) :
    IsSz (P ⧸ Subgroup.center P) n ∨ IsL2 (P ⧸ Subgroup.center P) n := by
  haveI : IsSimpleGroup A := by
    rcases hA with hA | hA
    · exact uc22p22r_lieModel_isSimple_twistedB2 hA
    · exact uc22p22r_lieModel_isSimple_classical (t := .PSL) (Or.inl rfl) hA
  haveI : IsSimpleGroup P := e.isSimpleGroup
  haveI : Nontrivial P := e.toEquiv.nontrivial
  have hc : Subgroup.center P = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center P) with h0 | h0
    · exact h0
    · exfalso
      have h1 : commutator P = ⊥ := (commutator_eq_bot_iff_center_eq_top P).2 h0
      rw [hP.1] at h1
      obtain ⟨a, ha⟩ := exists_ne (1 : P)
      have ha' : a ∈ (⊤ : Subgroup P) := Subgroup.mem_top a
      rw [h1, Subgroup.mem_bot] at ha'
      exact ha ha'
  have e' : P ⧸ Subgroup.center P ≃* A :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
  rcases hA with hA | hA
  · exact Or.inl (LieModel.of_mulEquiv e'.symm hA)
  · exact Or.inr (LieModel.of_mulEquiv e'.symm hA)

private theorem szL2_product_shape {X : Type} [Group X] {n : ℕ} (hn : 2 < n)
    (h : IsSzL2Product X n) :
    ∃ K₁ K₂ : Subgroup X, K₁ ⊔ K₂ = ⊤ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧
      CFSG.Open.IsQuasisimple ↥K₁ ∧ CFSG.Open.IsQuasisimple ↥K₂ ∧
      (∀ K' ∈ ({K₁, K₂} : Set (Subgroup X)),
        IsSz (↥K' ⧸ Subgroup.center ↥K') n ∨ IsL2 (↥K' ⧸ Subgroup.center ↥K') n) := by
  obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := h
  have hAs := uc22p20g_simple_nonab_SzL2 hn hA
  have hBs := uc22p20g_simple_nonab_SzL2 hn hB
  haveI := hAs.1
  haveI := hBs.1
  have hAq : CFSG.Open.IsQuasisimple A := uc22p22a_isQuasisimple_of_simple hAs.2
  have hBq : CFSG.Open.IsQuasisimple B := uc22p22a_isQuasisimple_of_simple hBs.2
  let f₁ : A →* X := e.symm.toMonoidHom.comp (MonoidHom.inl A B)
  let f₂ : B →* X := e.symm.toMonoidHom.comp (MonoidHom.inr A B)
  have hf₁ : Function.Injective f₁ :=
    e.symm.injective.comp fun _ _ h' => by simpa using congrArg Prod.fst h'
  have hf₂ : Function.Injective f₂ :=
    e.symm.injective.comp fun _ _ h' => by simpa using congrArg Prod.snd h'
  have hx : ∀ x : X, x = f₁ (e x).1 * f₂ (e x).2 := by
    intro x
    simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      MulEquiv.coe_toMonoidHom]
    rw [← map_mul]
    simp
  have hsup : f₁.range ⊔ f₂.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [hx x]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  have hcomm : ∀ a ∈ f₁.range, ∀ b ∈ f₂.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    simp
  have hq₁ : CFSG.Open.IsQuasisimple ↥f₁.range :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hf₁).symm hAq
  have hq₂ : CFSG.Open.IsQuasisimple ↥f₂.range :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hf₂).symm hBq
  refine ⟨f₁.range, f₂.range, hsup, hcomm, hq₁, hq₂, ?_⟩
  rintro K' (rfl | rfl)
  · exact lieModel_quot_center_of_szL2 (MonoidHom.ofInjective hf₁).symm hq₁ hA
  · exact lieModel_quot_center_of_szL2 (MonoidHom.ofInjective hf₂).symm hq₂ hB

private theorem su3_central_square_shape {X : Type} [Group X] (h : IsSU3CentralSquare X) :
    ∃ K₁ K₂ : Subgroup X, K₁ ⊔ K₂ = ⊤ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧
      CFSG.Open.IsQuasisimple ↥K₁ ∧ CFSG.Open.IsQuasisimple ↥K₂ ∧
      (∀ K' ∈ ({K₁, K₂} : Set (Subgroup X)),
        IsU3 (↥K' ⧸ Subgroup.center ↥K') 3) := by
  obtain ⟨K₁, K₂, hsup, hcomm, hK₁, hK₂, -⟩ := h
  refine ⟨K₁, K₂, hsup, hcomm, hK₁.1, hK₂.1, ?_⟩
  rintro K' (rfl | rfl)
  · exact hK₁.2
  · exact hK₂.2

theorem shape_cases
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    {X : Type} [Group X] [Finite X] (h : S20_7Shape X) :
    (IsSimpleGroup X ∨ CFSG.Open.IsQuasisimple X) ∨
      ∃ K₁ K₂ : Subgroup X, K₁ ⊔ K₂ = ⊤ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧
        CFSG.Open.IsQuasisimple ↥K₁ ∧ CFSG.Open.IsQuasisimple ↥K₂ ∧
        ((∃ n₀, 2 < n₀ ∧ ∀ K' ∈ ({K₁, K₂} : Set (Subgroup X)),
            IsSz (↥K' ⧸ center ↥K') n₀ ∨ IsL2 (↥K' ⧸ center ↥K') n₀) ∨
          ∀ K' ∈ ({K₁, K₂} : Set (Subgroup X)), IsU3 (↥K' ⧸ center ↥K') 3) := by
  rcases h with ⟨n, hn, h⟩ | h | h | h | h | h | ⟨n, hn, h⟩ | h
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (Or.inl (uc22p22r_lieModel_isSimple_twistedB2 h))
    · exact Or.inl (Or.inl (uc22p22r_lieModel_isSimple_classical (t := .PSL) (Or.inl rfl) h))
    · exact Or.inl (Or.inl (uc22p22r_lieModel_isSimple_classical (t := .PSL) (Or.inl rfl) h))
    · exact Or.inl (Or.inl
        (uc22p22r_lieModel_isSimple_classical (t := .PSU) (Or.inr (Or.inl rfl)) h))
    · exact Or.inl (Or.inl (uc22p22r_lieModel_isSimple_classical (t := .PSL) (Or.inl rfl) h))
    · exact Or.inl (Or.inl
        (uc22p22r_lieModel_isSimple_classical (t := .PSU) (Or.inr (Or.inl rfl)) h))
    · exact Or.inl (Or.inl (hG2 X n h))
    · exact Or.inl (Or.inl (h3D4 X n h))
    · exact Or.inl (Or.inl (h2F4 X n h))
    · exact Or.inl (Or.inl
        (uc22p22r_lieModel_isSimple_classical (t := .PSp) (Or.inr (Or.inr (Or.inl rfl))) h))
    · exact Or.inl (Or.inr h.1)
    · exact Or.inl (Or.inr h.1)
    · exact Or.inl (Or.inl
        (uc22p22r_lieModel_isSimple_classical (t := .PSp) (Or.inr (Or.inr (Or.inl rfl))) h))
    · exact Or.inl (Or.inl
        (uc22p22r_lieModel_isSimple_classical (t := .POmegaMinus) (Or.inr (Or.inr (Or.inr rfl))) h))
  · exact Or.inl (Or.inl
      (uc22p22r_lieModel_isSimple_classical (t := .PSU) (Or.inr (Or.inl rfl)) h))
  · exact Or.inl (Or.inl
      (uc22p22r_lieModel_isSimple_classical (t := .PSU) (Or.inr (Or.inl rfl)) h))
  · exact Or.inl (Or.inl
      (uc22p22r_lieModel_isSimple_classical (t := .POmegaMinus) (Or.inr (Or.inr (Or.inr rfl))) h))
  · exact Or.inl (Or.inl (h3D4 X 2 h))
  · exact Or.inl (Or.inl (h3D4 X 1 h))
  · obtain ⟨K₁, K₂, hsup, hcomm, hq₁, hq₂, hsh⟩ := szL2_product_shape hn h
    exact Or.inr ⟨K₁, K₂, hsup, hcomm, hq₁, hq₂, Or.inl ⟨n, hn, hsh⟩⟩
  · obtain ⟨K₁, K₂, hsup, hcomm, hq₁, hq₂, hsh⟩ := su3_central_square_shape h
    exact Or.inr ⟨K₁, K₂, hsup, hcomm, hq₁, hq₂, Or.inr hsh⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
