module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaWeylAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsLift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G]

theorem E6QTwo.card_eq_of_weylOfType_E6_of_card_192 [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840)
    {AL AK : Subgroup (MulAut ↥Bs)} (hind : ∀ φ ∈ AL ⊔ AK, φ ∈ ggInduced ⊤ Bs)
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (AL ⊔ AK)) (hALcard : Nat.card AL = 192)
    (hALr : GGReflGenerated 3 AL) (hAKr : GGReflGenerated 3 AK) {x y : ↥Bs} (hx : x ≠ 1)
    (hALx : ∀ φ ∈ AL, φ x = x) (hAKy : ∀ φ ∈ AK, φ y = y) (hy : y ∉ Subgroup.zpowers x)
    (h6 : 6 ≤ Set.ncard {r : MulAut ↥Bs | r ∈ AL ⊓ AK ∧ GGIsReflection 3 r})
    (hdich : ∀ ψ ∈ AL ⊔ AK, ψ y = y → (∀ a ∈ AK, ψ * a * ψ⁻¹ ∈ AK) ∨
      ∀ a ∈ AK, ∀ b ∈ AK, a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a) :
    9 ∣ Nat.card AK ∧ (∀ b : ↥Bs, (∀ φ ∈ AK, φ b = b) → b ∈ Subgroup.zpowers y) ∧
      Nat.card (Subgroup.closure {b : ↥Bs | ∃ φ ∈ AK, ∃ c : ↥Bs, b = φ c * c⁻¹}) = 3 ^ 4 ∧
      y ∉ Subgroup.closure {b : ↥Bs | ∃ φ ∈ AK, ∃ c : ↥Bs, b = φ c * c⁻¹} := by
  classical
  obtain ⟨V, hVadd, hVmod, ι, h, α, hα, β, hV, hmap, -, hP, hB, hx1⟩ :=
    E6QTwo.norm_eq_one_of_card_192 hBs hNT hcard hWcard hind hW le_sup_left hALcard hx hALx
  letI := hVadd
  letI := hVmod
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have hyx : ∀ a : ZMod 3, ι (Additive.ofMul y) ≠ a • ι (Additive.ofMul x) :=
    E6QTwo.ne_smul_of_not_mem_zpowers ι hy
  have h6' := E6QTwo.six_le_ncard_rootRefl_of_six_le (B := β) hP hV hB hα ι hmap
    (le_sup_right : AK ≤ AL ⊔ AK) (R := {r | r ∈ AL ⊓ AK ∧ GGIsReflection 3 r})
    (fun r hr => ⟨hr.1.2, hr.2, hALx r hr.1.1, hAKy r hr.1.2⟩) h6
  obtain ⟨h12, hKphi⟩ := E6QTwo.rootRefl_mem_of_six_le hP hV hB hα hx1 hyx h6'
  obtain ⟨-, -, -, hline⟩ := E6QTwo.phiD_facts hP hV hB hα hx1 hyx h12
  have hy2 : β (ι (Additive.ofMul y)) (ι (Additive.ofMul y)) = 2 := by
    rcases hline 0 1 one_ne_zero with ⟨-, h2⟩ | ⟨hxy0, h1⟩
    · simpa using h2
    · exfalso
      simp only [zero_smul, one_smul, zero_add] at hxy0 h1
      obtain ⟨w, hw, hwnot⟩ :=
        E6QTwo.exists_rootRefl_not_mem_closure hP hV hB hα hx1 h1 hxy0
      apply hwnot
      have hwW : E6QTwo.rootRefl (B := β) w hw ∈ (AL ⊔ AK).map (ggLin (p := 3) ι) := by
        rw [hmap]
        exact E6QTwo.rootRefl_mem_e6Weyl hP hV hB hα hw
      have hcl : (AL ⊔ AK).map (ggLin (p := 3) ι) ≤ Subgroup.closure
          {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : β u u = 2, (β u (ι (Additive.ofMul x)) = 0 ∨
            β u (ι (Additive.ofMul y)) = 0) ∧ r = E6QTwo.rootRefl (B := β) u hu} := by
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · exact (E6QTwo.map_le_closure_rootRefl_of_fix hP hV hB hα ι hmap le_sup_left hALr
            hALx).trans (Subgroup.closure_mono fun r ⟨u, hu, hux, hr⟩ => ⟨u, hu, Or.inl hux, hr⟩)
        · exact (E6QTwo.map_le_closure_rootRefl_of_fix hP hV hB hα ι hmap le_sup_right hAKr
            hAKy).trans (Subgroup.closure_mono fun r ⟨u, hu, huy, hr⟩ => ⟨u, hu, Or.inr huy, hr⟩)
      exact hcl hwW
  have hK := E6QTwo.rootRefl_mem_of_dich hP hV hB hα hx1 hy2 hyx h12 hKphi
    (E6QTwo.dich_map hα ι hmap hdich)
  refine ⟨?_, ?_, E6QTwo.card_closure_comm_eq hP hV hB hα ι hy2 hAKy ?_ hK⟩
  · have hle : Subgroup.closure {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : β u u = 2,
        β u (ι (Additive.ofMul y)) = 0 ∧ r = E6QTwo.rootRefl (B := β) u hu} ≤
          AK.map (ggLin (p := 3) ι) := by
      rw [Subgroup.closure_le]
      rintro r ⟨u, hu, huy, rfl⟩
      exact hK u hu huy
    have hcardK : Nat.card (AK.map (ggLin (p := 3) ι)) = Nat.card AK :=
      Subgroup.card_map_of_injective (ggLin_injective (p := 3) ι)
    rw [← hcardK]
    exact (E6QTwo.nine_dvd_card_closure_rootRefl hP hV hB hα hy2).trans
      (Subgroup.card_dvd_of_le hle)
  · intro b hb
    obtain ⟨a, ha⟩ := (E6QTwo.perp_facts hP hV hB hα hy2).1 (ι (Additive.ofMul b))
      (fun w hw hwy => by
        obtain ⟨φ, hφ, hφw⟩ := Subgroup.mem_map.mp (hK w hw hwy)
        have hfix : ggLin (p := 3) ι φ (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
          rw [ggLin_apply_ofMul, hb φ hφ]
        rw [hφw] at hfix
        exact (E6QTwo.rootRefl_fix_iff hw _).mp hfix)
    exact E6QTwo.mem_zpowers_of_eq_smul ι ha
  · intro φ hφ u w
    have hφW : ggLin (p := 3) ι φ ∈ E6QTwo.e6Weyl hα := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ (le_sup_right (a := AL) hφ)
    exact E6QTwo.bilinForm_apply_e6Weyl hP hV hB hα hφW u w

end CFSG.StandardType

end
