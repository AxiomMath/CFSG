module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaWeylAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsLift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G]

theorem E6QTwo.sup_eq_or_sup_eq_of_card_192 [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A) (hA : ∀ ψ ∈ A, ψ ∈ ggInduced ⊤ Bs)
    {AL : Subgroup (MulAut ↥Bs)} (hALA : AL ≤ A) (hALcard : Nat.card AL = 192)
    (hALr : GGReflGenerated 3 AL) {x : ↥Bs} (hx : x ≠ 1) (hALx : ∀ ψ ∈ AL, ψ x = x)
    {D : Subgroup G} (hDBs : D ≤ Bs) (hD : Nat.card D = 9) (hxD : (x : G) ∈ D)
    (h6 : 6 ≤ Set.ncard {r : MulAut ↥Bs | r ∈ AL ∧ GGIsReflection 3 r ∧
      ∀ d : ↥Bs, (d : G) ∈ D → r d = d})
    {y₁ y₂ : ↥Bs} (hy₁ : (y₁ : G) ∈ D) (hy₂ : (y₂ : G) ∈ D) (hy₁x : y₁ ∉ Subgroup.zpowers x)
    (hy₂x : y₂ ∉ Subgroup.zpowers x) (hy₁₂ : y₂ ∉ Subgroup.zpowers y₁)
    {A₁ A₂ : Subgroup (MulAut ↥Bs)} (hA₁ : A₁ ≤ A) (hA₂ : A₂ ≤ A)
    (hR₁ : ∀ r ∈ AL, GGIsReflection 3 r → (∀ d : ↥Bs, (d : G) ∈ D → r d = d) → r ∈ A₁)
    (hR₂ : ∀ r ∈ AL, GGIsReflection 3 r → (∀ d : ↥Bs, (d : G) ∈ D → r d = d) → r ∈ A₂)
    (hN₁ : ∀ ψ ∈ A, ψ y₁ = y₁ → (∀ a ∈ A₁, ψ * a * ψ⁻¹ ∈ A₁) ∨
      ∀ a ∈ A₁, ∀ b ∈ A₁, a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a)
    (hN₂ : ∀ ψ ∈ A, ψ y₂ = y₂ → (∀ a ∈ A₂, ψ * a * ψ⁻¹ ∈ A₂) ∨
      ∀ a ∈ A₂, ∀ b ∈ A₂, a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a) :
    AL ⊔ A₁ = A ∨ AL ⊔ A₂ = A := by
  classical
  obtain ⟨V, hVadd, hVmod, ι, h, α, hα, β, hV, hmap, hW', hP, hB, hx1⟩ :=
    E6QTwo.norm_eq_one_of_card_192 hBs hNT hcard hWcard hA hW hALA hALcard hx hALx
  letI := hVadd
  letI := hVmod
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have hphi : ∀ (yi : ↥Bs) (Ai : Subgroup (MulAut ↥Bs)), (yi : G) ∈ D →
      yi ∉ Subgroup.zpowers x → Ai ≤ A →
      (∀ r ∈ AL, GGIsReflection 3 r → (∀ d : ↥Bs, (d : G) ∈ D → r d = d) → r ∈ Ai) →
      12 ≤ Set.ncard {v : V | β v v = 2 ∧ β v (ι (Additive.ofMul x)) = 0 ∧
          β v (ι (Additive.ofMul yi)) = 0} ∧
        ∀ (v : V) (hv : β v v = 2), β v (ι (Additive.ofMul x)) = 0 →
          β v (ι (Additive.ofMul yi)) = 0 →
            E6QTwo.rootRefl (B := β) v hv ∈ Ai.map (ggLin (p := 3) ι) := by
    intro yi Ai hyiD hyix hAiA hRi
    exact E6QTwo.rootRefl_mem_of_six_le hP hV hB hα hx1
      (E6QTwo.ne_smul_of_not_mem_zpowers ι hyix)
      (E6QTwo.six_le_ncard_rootRefl_of_six_le (B := β) hP hV hB hα ι hmap hAiA
        (R := {r | r ∈ AL ∧ GGIsReflection 3 r ∧ ∀ d : ↥Bs, (d : G) ∈ D → r d = d})
        (x := x) (y := yi)
        (fun r hr => ⟨hRi r hr.1 hr.2.1 hr.2.2, hr.2.1, hr.2.2 x hxD, hr.2.2 yi hyiD⟩) h6)
  have hroot : ∀ (yi : ↥Bs) (Ai : Subgroup (MulAut ↥Bs)), (yi : G) ∈ D →
      yi ∉ Subgroup.zpowers x → Ai ≤ A →
      (∀ r ∈ AL, GGIsReflection 3 r → (∀ d : ↥Bs, (d : G) ∈ D → r d = d) → r ∈ Ai) →
      β (ι (Additive.ofMul x)) (ι (Additive.ofMul yi)) ≠ 0 →
        β (ι (Additive.ofMul yi)) (ι (Additive.ofMul yi)) = 2 := by
    intro yi Ai hyiD hyix hAiA hRi hxyi
    obtain ⟨-, -, -, hline⟩ := E6QTwo.phiD_facts hP hV hB hα hx1
      (E6QTwo.ne_smul_of_not_mem_zpowers ι hyix) (hphi yi Ai hyiD hyix hAiA hRi).1
    rcases hline 0 1 one_ne_zero with ⟨-, h2⟩ | ⟨h0, -⟩
    · simpa using h2
    · exact absurd (by simpa using h0) hxyi
  have key : ∀ (yi : ↥Bs) (Ai : Subgroup (MulAut ↥Bs)), (yi : G) ∈ D →
      yi ∉ Subgroup.zpowers x → Ai ≤ A →
      (∀ r ∈ AL, GGIsReflection 3 r → (∀ d : ↥Bs, (d : G) ∈ D → r d = d) → r ∈ Ai) →
      (∀ ψ ∈ A, ψ yi = yi → (∀ a ∈ Ai, ψ * a * ψ⁻¹ ∈ Ai) ∨
        ∀ a ∈ Ai, ∀ b ∈ Ai, a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a) →
      β (ι (Additive.ofMul x)) (ι (Additive.ofMul yi)) ≠ 0 → AL ⊔ Ai = A := by
    intro yi Ai hyiD hyix hAiA hRi hNi hxyi
    have hyi2 := hroot yi Ai hyiD hyix hAiA hRi hxyi
    obtain ⟨h12, hKphi⟩ := hphi yi Ai hyiD hyix hAiA hRi
    have hK := E6QTwo.rootRefl_mem_of_dich hP hV hB hα hx1 hyi2
      (E6QTwo.ne_smul_of_not_mem_zpowers ι hyix) h12 hKphi (E6QTwo.dich_map hα ι hmap hNi)
    obtain ⟨w, hw, hwL, hwx, hwy⟩ := E6QTwo.exists_rootRefl_mem_map_of_card_192 hP hV hB hα hW'
      ι hmap hALA hALcard hALr hALx hyi2
    have hw1 : w ≠ ι (Additive.ofMul yi) := by
      rintro rfl
      exact hxyi (by rw [E6QTwo.bilinForm_symm hP hV hB]; exact hwx)
    have hw2 : w ≠ -ι (Additive.ofMul yi) := by
      intro hw'
      apply hxyi
      have h0 : β (ι (Additive.ofMul x)) (-ι (Additive.ofMul yi)) = 0 := by
        rw [← hw', E6QTwo.bilinForm_symm hP hV hB]
        exact hwx
      rw [map_neg] at h0
      exact neg_eq_zero.mp h0
    have hle := E6QTwo.e6Weyl_le_closure_insert hP hV hB hα hyi2 hw hwy hw1 hw2
    have hcl : Subgroup.closure (insert (E6QTwo.rootRefl (B := β) w hw)
        {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : β u u = 2, β u (ι (Additive.ofMul yi)) = 0 ∧
          r = E6QTwo.rootRefl (B := β) u hu}) ≤ (AL ⊔ Ai).map (ggLin (p := 3) ι) := by
      rw [Subgroup.closure_le, Subgroup.map_sup]
      rintro r (rfl | ⟨u, hu, huy, rfl⟩)
      · exact Subgroup.mem_sup_left hwL
      · exact Subgroup.mem_sup_right (hK u hu huy)
    have hmapeq : (AL ⊔ Ai).map (ggLin (p := 3) ι) = A.map (ggLin (p := 3) ι) := by
      refine le_antisymm (Subgroup.map_mono (sup_le hALA hAiA)) ?_
      rw [hmap]
      exact hle.trans hcl
    exact Subgroup.map_injective (ggLin_injective (p := 3) ι) hmapeq
  by_cases h1 : β (ι (Additive.ofMul x)) (ι (Additive.ofMul y₁)) = 0
  · right
    refine key y₂ A₂ hy₂ hy₂x hA₂ hR₂ hN₂ ?_
    obtain ⟨a, b, hab⟩ := E6QTwo.exists_eq_smul_add_smul hBs ι hDBs hD hxD hy₁ hy₂ hx hy₁x
    have hx2 : β (ι (Additive.ofMul x)) (ι (Additive.ofMul y₂)) = a := by
      rw [hab]
      simp [hx1, h1]
    rw [hx2]
    rintro rfl
    apply hy₁₂
    exact E6QTwo.mem_zpowers_of_eq_smul ι (a := b) (by rw [hab, zero_smul, zero_add])
  · left
    exact key y₁ A₁ hy₁ hy₁x hA₁ hR₁ hN₁ h1

end CFSG.StandardType

end
