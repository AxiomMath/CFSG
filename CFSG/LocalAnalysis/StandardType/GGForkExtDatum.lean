module

public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggForkExtDatum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V} {ha : V}
    {αa : Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) (ι : Additive ↥Bs ≃+ V)
    (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs}
    (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) (hu : αa (h b) = 0 ∨ αa (h b) = 1) :
    ∃ (X : Matrix (Option Λ) (Option Λ) ℤ) (φ' : Option Λ → MulAut ↥Bs) (h' : Option Λ → V)
      (α' : Option Λ → Module.Dual (ZMod p) V), GGExtDatum ι X φ' h' α' ∧
      (αa (h b) = 0 → X = ggAttachCartan C c) ∧ (αa (h b) = 1 → X = ggAttachCartan C b) ∧
      (∀ i, φ' (some i) = φ i ∧ h' (some i) = h i ∧ α' (some i) = α i) ∧
      (φ' none = φa ∨ φ' none = φ b * φa * (φ b)⁻¹) := by
  rcases hu with hu | hu
  ·
    have hv : α b ha = 0 :=
      (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).1.mp hu
    have hdiag : ∀ j : Option Λ, ggAttachCartan C c j j = 2 := by
      rintro (_ | j)
      · rfl
      · rw [ggAttachCartan_some_some, hF.diag j]
    have hP : ∀ i j : Option Λ,
        ggOptFam αa α i (ggOptFam ha h j) = (ggAttachCartan C c i j : ZMod p) := by
      rintro (_ | i) (_ | j)
      · simp [hF.aa]
      · by_cases hjb : j = b
        · subst hjb
          simp [hu, hF.ne]
        · simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_none_some, hF.aL j hjb]
          split_ifs <;> simp
      · by_cases hib : i = b
        · subst hib
          simp [hv, hF.ne]
        · simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_some_none, hF.aR i hib]
          split_ifs <;> simp
      · simp only [ggOptFam_some, ggAttachCartan_some_some, hF.pair]
    refine ⟨ggAttachCartan C c, ggOptFam φa φ, ggOptFam ha h, ggOptFam αa α,
      ⟨?_, ?_, hP, hind, hdiag⟩, ?_, ?_, ?_, ?_⟩
    · rintro (_ | i)
      · exact hφa
      · exact hφ i
    · rintro (_ | i) w
      · exact hlina w
      · exact hlin i w
    · intro _; rfl
    · intro h1; exact absurd (hu.symm.trans h1) zero_ne_one
    · intro i; exact ⟨rfl, rfl, rfl⟩
    · exact Or.inl rfl
  ·
    have hv : α b ha = 1 :=
      (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).2.mp hu
    obtain ⟨hψ, hlinψ⟩ := ggFork_ext_reflection ι hF hφ hφa hlin hlina hu hv
    have hθ : (αa - α b) (ha - h b) = 2 := by
      simp only [LinearMap.sub_apply, map_sub, hF.aa, hu, hv, hF.self b]
      ring
    have hdiag : ∀ j : Option Λ, ggAttachCartan C b j j = 2 := by
      rintro (_ | j)
      · rfl
      · rw [ggAttachCartan_some_some, hF.diag j]
    have hP : ∀ i j : Option Λ,
        ggOptFam (αa - α b) α i (ggOptFam (ha - h b) h j) =
          (ggAttachCartan C b i j : ZMod p) := by
      rintro (_ | i) (_ | j)
      · rw [ggOptFam_none, ggOptFam_none, ggAttachCartan_none_none, hθ]
        simp
      · simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_none_some, LinearMap.sub_apply]
        by_cases hjb : j = b
        · subst hjb
          rw [hu, hF.self]
          norm_num
        · rw [hF.aL_sub_bL hjb]
          simp [hjb]
      · simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_some_none, map_sub]
        by_cases hib : i = b
        · subst hib
          rw [hv, hF.self]
          norm_num
        · rw [hF.aR_sub_bR hib]
          simp [hib]
      · simp only [ggOptFam_some, ggAttachCartan_some_some, hF.pair]
    have hind' : LinearIndependent (ZMod p) (ggOptFam (ha - h b) h) := by
      rw [linearIndependent_ggOptFam] at hind ⊢
      refine ⟨hind.1, fun hmem => hind.2 ?_⟩
      have h3 := Submodule.add_mem _ hmem
        (Submodule.subset_span ⟨b, rfl⟩ : h b ∈ Submodule.span (ZMod p) (Set.range h))
      rwa [sub_add_cancel] at h3
    refine ⟨ggAttachCartan C b, ggOptFam (φ b * φa * (φ b)⁻¹) φ, ggOptFam (ha - h b) h,
      ggOptFam (αa - α b) α, ⟨?_, ?_, hP, hind', hdiag⟩, ?_, ?_, ?_, ?_⟩
    · rintro (_ | i)
      · exact hψ
      · exact hφ i
    · rintro (_ | i) w
      · exact hlinψ w
      · exact hlin i w
    · intro h0; exact absurd (hu.symm.trans h0) one_ne_zero
    · intro _; rfl
    · intro i; exact ⟨rfl, rfl, rfl⟩
    · exact Or.inr rfl

end CFSG.StandardType
