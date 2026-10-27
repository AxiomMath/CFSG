module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Pointwise

variable {G : Type} [Group G] {G₀ Bs : Subgroup G} {R : Type} [Group R]
  {θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R} {I : Set (MulAut R)}

theorem ggInduces_closure_pair (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I)
    (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) (hinn : ∀ r : R, MulAut.conj r ∈ I) (hN : GGInndiagNormal R I)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hBs : ∀ c ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ)
    {n : G} (hn : n ∈ Subgroup.normalizer (G₀ : Set G)) {b d : G} (hb : b ∈ Bs) (hd : d ∈ Bs) :
    ∀ a ∈ Subgroup.closure ({b, n * d * n⁻¹} : Set G),
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ := by
  have hb' : b ∈ ggInndiagPre G₀ θ I := le_ggInndiagPre_of_induces hBsN hBs hb
  have hd' : d ∈ ggInndiagPre G₀ θ I := le_ggInndiagPre_of_induces hBsN hBs hd
  have he' : n * d * n⁻¹ ∈ ggInndiagPre G₀ θ I := conj_mem_ggInndiagPre hN hn hd'
  have hcl : Subgroup.closure ({b, n * d * n⁻¹} : Set G) ≤ ggInndiagPre G₀ θ I := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hb'
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact he'
  intro a ha
  obtain ⟨haN, haI⟩ := mem_ggInndiagPre_iff.mp (hcl ha)
  exact (ggL45_exists_induces_iff hinv haN).mpr ((ggL45_mem_ggInndiag_iff hmul hinv hinn).mp haI)

end Pointwise

section Marked

variable {G : Type} [Group G] {G₀ Bs : Subgroup G}

theorem ggMarking_closure_pair (hR : GGRawInnSubgroupInput) (hN : GGInndiagNormalInput)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hmk : LargeEvenMarking ↥G₀ fun _ _ _ I _ θ => ∀ c ∈ Bs,
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ)
    {n : G} (hn : n ∈ Subgroup.normalizer (G₀ : Set G)) {b d : G} (hb : b ∈ Bs) (hd : d ∈ Bs) :
    LargeEvenMarking ↥G₀ fun _ _ _ I _ θ => ∀ a ∈ Subgroup.closure ({b, n * d * n⁻¹} : Set G),
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ := by
  have h1 := largeEvenMarking_and_labelAll_simple (S := fun _ => True) (P' := GGRawInnSubgroup)
    (fun lab hl _ => hR lab hl) (fun _ _ _ _ _ _ _ => trivial) hmk
  have h2 := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := fun R _ I _ => GGInndiagNormal R I) (fun lab hl _ => hN lab hl)
    (fun _ _ _ _ _ _ _ => trivial) h1
  refine largeEvenMarking_mono ?_ h2
  rintro _ R _ I F θ ⟨⟨hP, hmul, hinv, hinn⟩, hNn⟩
  exact ggInduces_closure_pair hmul hinv hinn hNn hBsN hP hn hb hd

theorem ggMarking_single {e : G} (he : e ∈ Bs)
    (hmk : LargeEvenMarking ↥G₀ fun _ _ _ I _ θ => ∀ c ∈ Bs,
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) :
    LargeEvenMarking ↥G₀ fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = e⁻¹ * l * e) φ :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ h => h e he) hmk

end Marked

end CFSG.StandardType
