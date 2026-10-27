module

public import CFSG.Quasithin.EmptyFaithful.ModHJ4Def
public import CFSG.Quasithin.EmptyFaithful.S146yBorelBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem isTwoLocalSub_normalizer {Γ : Type} [Group Γ] [IsSimpleGroup Γ] {N : Subgroup Γ}
    (hN : IsPGroup 2 N) (hne : N ≠ ⊥) (htop : N ≠ ⊤) :
    ModH.IsTwoLocalSub (Subgroup.normalizer (N : Set Γ)) := by
  refine ⟨?_, N, hN, hne, rfl⟩
  intro h
  have hn : N.Normal := Subgroup.normalizer_eq_top_iff.1 h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
  · exact hne h1
  · exact htop h1

theorem map_normalizer_equiv {A B : Type} [Group A] [Group B] (ψ : A ≃* B) (H : Subgroup A) :
    Subgroup.normalizer ((Subgroup.map (ψ : A →* B) H : Subgroup B) : Set B) =
      Subgroup.map (ψ : A →* B) (Subgroup.normalizer (H : Set A)) := by
  have m : ∀ z : A, ψ z ∈ Subgroup.map (ψ : A →* B) H ↔ z ∈ H := fun z => by
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact (ψ.injective hwz) ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := ψ.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ Subgroup.normalizer (H : Set A)
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro w
    have h1 := hy (ψ w)
    rw [m, show ψ x * ψ w * (ψ x)⁻¹ = ψ (x * w * x⁻¹) by simp, m] at h1
    exact h1
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Subgroup.normalizer (H : Set A) := hx
    show ψ x ∈ Subgroup.normalizer ((Subgroup.map (ψ : A →* B) H : Subgroup B) : Set B)
    rw [Subgroup.mem_normalizer_iff] at hx' ⊢
    intro y'
    obtain ⟨y, rfl⟩ := ψ.surjective y'
    rw [show ψ x * ψ y * (ψ x)⁻¹ = ψ (x * y * x⁻¹) by simp, m, m]
    exact hx' y

theorem isTwoLocalSub_map {A B : Type} [Group A] [Group B] (ψ : A ≃* B) {M : Subgroup A}
    (h : ModH.IsTwoLocalSub M) : ModH.IsTwoLocalSub (Subgroup.map (ψ : A →* B) M) := by
  obtain ⟨hM, N, hN, hne, rfl⟩ := h
  refine ⟨?_, Subgroup.map (ψ : A →* B) N, hN.map (ψ : A →* B), ?_, ?_⟩
  · intro htop
    apply hM
    apply Subgroup.map_injective (f := (ψ : A →* B)) ψ.injective
    rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.2 ψ.surjective]
  · intro hbot
    exact hne ((Subgroup.map_eq_bot_iff_of_injective N ψ.injective).1 hbot)
  · rw [map_normalizer_equiv]

theorem isMaxTwoLocal_map {A B : Type} [Group A] [Group B] (ψ : A ≃* B) {M : Subgroup A}
    (h : ModH.IsMaxTwoLocal M) : ModH.IsMaxTwoLocal (Subgroup.map (ψ : A →* B) M) := by
  refine ⟨isTwoLocalSub_map ψ h.1, fun M' hM' hle => ?_⟩
  have h1 : ModH.IsTwoLocalSub (Subgroup.map (ψ.symm : B →* A) M') := isTwoLocalSub_map ψ.symm hM'
  have h2 : M ≤ Subgroup.map (ψ.symm : B →* A) M' := fun x hx =>
    ⟨ψ x, hle ⟨x, hx, rfl⟩, by simp⟩
  have h3 := h.2 _ h1 h2
  ext x'
  constructor
  · intro hx'
    have : ψ.symm x' ∈ M := by
      rw [← h3]
      exact ⟨x', hx', rfl⟩
    exact ⟨ψ.symm x', this, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← h3] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = ψ x := by
      have := congrArg ψ hyx
      simpa using this
    show ψ x ∈ M'
    rw [← this]
    exact hy

theorem sylow_transport {Γ : Type} [Group Γ] [Finite Γ] {P₀ : Subgroup Γ}
    (hP0 : IsSylowTwoOf P₀ ⊤) {Q : Type} [Group Q] [Finite Q] (φ : Q ≃* Γ) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : ∃ ψ : Q ≃* Γ, Subgroup.map (ψ : Q →* Γ) S = P₀ := by
  have hSΓ : IsSylowTwoOf (Subgroup.map (φ : Q →* Γ) S) ⊤ :=
    CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map φ hS
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hSΓ hP0
  refine ⟨φ.trans (MulAut.conj g), ?_⟩
  rw [← hg, Subgroup.map_map]
  rfl

end CFSG.Quasithin.J4Loc
