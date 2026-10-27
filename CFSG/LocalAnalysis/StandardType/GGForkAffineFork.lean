module

public import CFSG.LocalAnalysis.StandardType.GGForkAffineDatum

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section ForkDatum

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V} {ha : V}
  {αa : Module.Dual (ZMod p) V}

theorem ggReflDatum_of_fork_zero (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤) (hu : αa (h b) = 0) :
    Nonempty (GGReflDatum p ι (ggAttachCartan C c)) := by
  have hv : α b ha = 0 := (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).1.mp hu
  refine ⟨GGReflDatum.mk (ggOptFam φa φ) ?_ (ggOptFam ha h) (ggOptFam αa α) ?_ ?_ ?_ hind
    hspan⟩
  · rintro (_ | i)
    · exact hφa
    · exact hφ i
  · rintro (_ | i) w
    · exact hlina w
    · exact hlin i w
  · rintro (_ | i) (_ | j)
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
  · rintro (_ | i)
    · rfl
    · exact hF.diag i

theorem ggReflDatum_of_fork_one (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤) (hu : αa (h b) = 1) :
    Nonempty (GGReflDatum p ι (ggAttachCartan C b)) := by
  have hv : α b ha = 1 := (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).2.mp hu
  obtain ⟨hψ, hlinψ⟩ := ggFork_ext_reflection ι hF hφ hφa hlin hlina hu hv
  let ψ : MulAut ↥Bs := φ b * φa * (φ b)⁻¹
  have hψ' : ψ ∈ ggInduced ⊤ Bs := hψ
  have hlinψ' : ∀ z, ggLin (p := p) ι ψ z = z - (αa - α b) z • (ha - h b) := hlinψ
  have hθ : (αa - α b) (ha - h b) = 2 := by
    simp only [LinearMap.sub_apply, map_sub, hF.aa, hu, hv, hF.self b]
    ring
  have hind' : LinearIndependent (ZMod p) (ggOptFam (ha - h b) h) := by
    rw [linearIndependent_ggOptFam] at hind ⊢
    refine ⟨hind.1, fun hmem => hind.2 ?_⟩
    have h3 := Submodule.add_mem _ hmem
      (Submodule.subset_span ⟨b, rfl⟩ : h b ∈ Submodule.span (ZMod p) (Set.range h))
    rwa [sub_add_cancel] at h3
  refine ⟨GGReflDatum.mk (ggOptFam ψ φ) ?_ (ggOptFam (ha - h b) h) (ggOptFam (αa - α b) α) ?_ ?_
    ?_ hind' ?_⟩
  · rintro (_ | i)
    · exact hψ'
    · exact hφ i
  · rintro (_ | i) w
    · exact hlinψ' w
    · exact hlin i w
  · rintro (_ | i) (_ | j)
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
  · rintro (_ | i)
    · rfl
    · exact hF.diag i
  · rw [eq_top_iff, ← hspan]
    apply Submodule.span_le.2
    rintro x ⟨(_ | i), rfl⟩
    · change ha ∈ Submodule.span (ZMod p) (Set.range (ggOptFam (ha - h b) h))
      have h1 : ha - h b ∈ Submodule.span (ZMod p) (Set.range (ggOptFam (ha - h b) h)) :=
        Submodule.subset_span (Set.mem_range_self none)
      have h2 : h b ∈ Submodule.span (ZMod p) (Set.range (ggOptFam (ha - h b) h)) :=
        Submodule.subset_span ⟨some b, rfl⟩
      have h3 := Submodule.add_mem _ h1 h2
      rwa [sub_add_cancel] at h3
    · exact Submodule.subset_span ⟨some i, rfl⟩

end ForkDatum

end CFSG.StandardType
