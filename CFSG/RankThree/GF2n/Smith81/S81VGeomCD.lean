module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomB
public import CFSG.RankThree.GF2n.Smith81.S81VGeomA

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def ResSet (σ : F ≃+* F) (X : Set (Submodule F (Fin 6 → F))) (R : Submodule F (Fin 6 → F)) :
    Set (Fin 6 → F) :=
  {p | p ≠ 0 ∧ herm σ p p = 0 ∧ (∀ r ∈ R, herm σ r p = 0) ∧
    ∀ G, IsPt σ G → R ≤ G → p ∈ G → GenPts σ X G}

theorem closedPts_resSet (hσ : ∀ c, σ (σ c) = c) (X : Set (Submodule F (Fin 6 → F)))
    (R : Submodule F (Fin 6 → F)) : ClosedPts σ (ResSet σ X R) := by
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, -, -⟩ := hx
    exact ⟨h1, h2⟩
  · intro x hx c hc
    obtain ⟨hx0, hxi, hxR, hGx⟩ := hx
    refine ⟨smul_ne_zero hc hx0, ?_, fun r hr => ?_, fun G hG hRG hcG => ?_⟩
    · simp [herm_smul_left, herm_smul_right, hxi]
    · simp [herm_smul_right, hxR r hr]
    · apply hGx G hG hRG
      have h := Submodule.smul_mem G c⁻¹ hcG
      rwa [inv_smul_smul₀ hc] at h
  · intro x hx y hy hxy z hz0 hzz hzspan
    obtain ⟨hx0, hxi, hxR, hGx⟩ := hx
    obtain ⟨hy0, hyi, hyR, hGy⟩ := hy
    refine ⟨hz0, hzz, fun r hr => ?_, lemmaB hσ hxi hyi hxy hxR hyR hzspan hz0 hzz hGx hGy⟩
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hzspan
    simp [herm_add_right, herm_smul_right, hxR r hr, hyR r hr]

theorem lemmaD [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {X : Set (Submodule F (Fin 6 → F))} {ρ : Fin 6 → F} (hρ0 : ρ ≠ 0) (hρi : herm σ ρ ρ = 0)
    {U : Submodule F (Fin 6 → F)} (hU : NonDeg σ U) (h3 : finrank F U = 3)
    (hUρ : ∀ u ∈ U, herm σ ρ u = 0) {a b c : Fin 6 → F} (haU : a ∈ U) (hbU : b ∈ U) (hcU : c ∈ U)
    (hai : herm σ a a = 0) (hbi : herm σ b b = 0) (hci : herm σ c c = 0)
    (hind : LinearIndependent F ![a, b, c])
    (hGa : ∀ G, IsPt σ G → ρ ∈ G → a ∈ G → GenPts σ X G)
    (hGb : ∀ G, IsPt σ G → ρ ∈ G → b ∈ G → GenPts σ X G)
    (hGc : ∀ G, IsPt σ G → ρ ∈ G → c ∈ G → GenPts σ X G) :
    ∀ G, IsPt σ G → ρ ∈ G → GenPts σ X G := by
  obtain ⟨R, hRdef⟩ : ∃ R : Submodule F (Fin 6 → F), R = Submodule.span F {ρ} := ⟨_, rfl⟩
  have hρR : ρ ∈ R := by
    rw [hRdef]
    exact Submodule.mem_span_singleton_self ρ
  have hperp : ∀ v : Fin 6 → F, herm σ ρ v = 0 → ∀ r ∈ R, herm σ r v = 0 := by
    intro v hv r hr
    rw [hRdef] at hr
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hr
    rw [herm_smul_left, hv, mul_zero]
  have hmemS : ∀ v : Fin 6 → F, v ≠ 0 → herm σ v v = 0 → herm σ ρ v = 0 →
      (∀ G, IsPt σ G → ρ ∈ G → v ∈ G → GenPts σ X G) → v ∈ ResSet σ X R := by
    intro v hv0 hvi hvρ hvG
    refine ⟨hv0, hvi, hperp v hvρ, fun G hG hRG hvG' => ?_⟩
    exact hvG G hG (hRG hρR) hvG'
  have ha0 : a ≠ 0 := by
    have h := hind.ne_zero 0
    simpa using h
  have hb0 : b ≠ 0 := by
    have h := hind.ne_zero 1
    simpa using h
  have hc0 : c ≠ 0 := by
    have h := hind.ne_zero 2
    simpa using h
  have hS : ClosedPts σ (ResSet σ X R) := closedPts_resSet hσ.invol X R
  have haS : a ∈ ResSet σ X R := hmemS a ha0 hai (hUρ a haU) hGa
  have hbS : b ∈ ResSet σ X R := hmemS b hb0 hbi (hUρ b hbU) hGb
  have hcS : c ∈ ResSet σ X R := hmemS c hc0 hci (hUρ c hcU) hGc
  have hA := lemmaA hσ hU h3 hS haS hbS hcS haU hbU hcU hind
  intro G hG hρG
  have hRG : R ≤ G := by
    rw [hRdef]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hρG)
  have hGO : G ≤ orth σ R := by
    intro g hg
    rw [mem_orth]
    intro w hw
    rw [hRdef] at hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [herm_smul_left, hG.1 ρ hρG g hg, mul_zero]
  have hUO : U ≤ orth σ R := by
    intro u hu
    rw [mem_orth]
    intro w hw
    rw [hRdef] at hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [herm_smul_left, hUρ u hu, mul_zero]
  have hO : finrank F (orth σ R) = 5 := by
    have h := finrank_orth hσ.invol R
    have h1 : finrank F R = 1 := by
      rw [hRdef]
      exact finrank_span_singleton hρ0
    omega
  have hsup : finrank F ↥(G ⊔ U) ≤ finrank F (orth σ R) :=
    Submodule.finrank_mono (sup_le hGO hUO)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq G U
  have hGf : finrank F G = 3 := hG.2
  have hinf : 1 ≤ finrank F ↥(G ⊓ U) := by omega
  have hne : G ⊓ U ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hinf
    omega
  obtain ⟨z, hzGU, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hzG, hzU⟩ := Submodule.mem_inf.mp hzGU
  have hzi : herm σ z z = 0 := hG.1 z hzG z hzG
  have hzS : z ∈ ResSet σ X R := hA z hzU hz0 hzi
  obtain ⟨-, -, -, hGen⟩ := hzS
  exact hGen G hG hRG hzG

end CFSG.RankThree.GF2n.Smith81.S81V
