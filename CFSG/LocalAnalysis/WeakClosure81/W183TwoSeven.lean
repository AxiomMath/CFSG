module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNine
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem IsSevenNineGroup.congr {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {D : Set X}
    {D' : Set X'} (hD : ∀ x, x ∈ D ↔ e x ∈ D') (h : IsSevenNineGroup X D) :
    IsSevenNineGroup X' D' := by
  unfold IsSevenNineGroup IsReflModel IsReflQuotModel at h ⊢
  rcases h with ⟨f, h1, h2, h3, ε, he⟩ | ⟨f, h1, h2, ⟨ε, he⟩ | ⟨ε, he⟩⟩
  · exact Or.inl ⟨f, h1, h2, h3, e.symm.trans ε,
      fun d' hd' => he (e.symm d') ((hD (e.symm d')).mpr (by simpa using hd'))⟩
  · exact Or.inr ⟨f, h1, h2, Or.inl ⟨e.symm.trans ε,
      fun d' hd' => he (e.symm d') ((hD (e.symm d')).mpr (by simpa using hd'))⟩⟩
  · exact Or.inr ⟨f, h1, h2, Or.inr ⟨e.symm.trans ε,
      fun d' hd' => he (e.symm d') ((hD (e.symm d')).mpr (by simpa using hd'))⟩⟩

section Seven


theorem false_of_sevenNine_class {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ} (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) (ha2 : orderOf a = 2) (hG2 : pCoreOf 2 G = ⊥)
    (hIn : OrthReflParabolic) {X₁ : Subgroup ↥G} (haX : a ∈ X₁)
    (hX₁N : X₁ ≤ Subgroup.normalClosure ({a} : Set ↥G)) {L : Subgroup ↥X₁}
    (hsL : (⟨a, haX⟩ : ↥X₁) ∈ L)
    (hL : IsSevenNineGroup ↥L
      {x : ↥L | (x : ↥X₁) ∈ Subgroup.zpowers (⟨a, haX⟩ : ↥X₁) ∧ x ≠ 1}) : False := by
  let U : Subgroup (VG G) := UAOf G VA (Subgroup.zpowers (a : LGL 2 V))
  let K : Subgroup (VG G) := kSub U (⊤ : Subgroup (VG G)) (vHat G)
  have h73 : Hyp73 U (⊤ : Subgroup (VG G)) (vHat G) (pCoreOf 2 K) :=
    hyp73_UAOf_zpowers h hrank hVAle ha (U := U) rfl
  obtain ⟨φ, hφbar, -, hφU⟩ :=
    exists_isBarMap_kSub_UAOf_zpowers h hrank hVAle ha ha2 hG2 (U := U) (K := K) rfl rfl
  let N : Subgroup ↥G := Subgroup.normalClosure ({a} : Set ↥G)
  let ι : ↥X₁ →* ↥N := Subgroup.inclusion hX₁N
  have hι : Function.Injective ι := Subgroup.inclusion_injective hX₁N
  let L' : Subgroup ↥N := L.map ι
  let eL : ↥L ≃* ↥L' := Subgroup.equivMapOfInjective L ι hι
  have hιa : ι ⟨a, haX⟩ = (⟨a, Subgroup.subset_normalClosure rfl⟩ : ↥N) :=
    Subtype.ext rfl
  have hVL : barSub K φ U ≤ L' := by
    rw [hφU, ← hιa]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem ι hsL)
  have hD : ∀ x : ↥L,
      (x ∈ {x : ↥L | (x : ↥X₁) ∈ Subgroup.zpowers (⟨a, haX⟩ : ↥X₁) ∧ x ≠ 1}) ↔
      (eL x ∈ {y : ↥L' | (y : ↥N) ∈ barSub K φ U ∧ y ≠ 1}) := by
    intro x
    have hxcoe : (eL x : ↥N) = ι (x : ↥X₁) := Subgroup.coe_equivMapOfInjective_apply L ι hι x
    have hbar : barSub K φ U = Subgroup.zpowers (ι (⟨a, haX⟩ : ↥X₁)) := by
      rw [hφU, hιa]
    change ((x : ↥X₁) ∈ Subgroup.zpowers (⟨a, haX⟩ : ↥X₁) ∧ x ≠ 1) ↔
      ((eL x : ↥N) ∈ barSub K φ U ∧ eL x ≠ 1)
    rw [hxcoe, hbar]
    constructor
    · rintro ⟨hz, hne⟩
      have hz' : ι (x : ↥X₁) ∈ (Subgroup.zpowers (⟨a, haX⟩ : ↥X₁)).map ι :=
        (Subgroup.mem_map_iff_mem hι).mpr hz
      exact ⟨by simpa only [MonoidHom.map_zpowers] using hz', eL.map_ne_one_iff.mpr hne⟩
    · rintro ⟨hz, hne⟩
      have hz' : ι (x : ↥X₁) ∈ (Subgroup.zpowers (⟨a, haX⟩ : ↥X₁)).map ι := by
        simpa only [MonoidHom.map_zpowers] using hz
      exact ⟨(Subgroup.mem_map_iff_mem hι).mp hz', eL.map_ne_one_iff.mp hne⟩
  refine seven_nine_in hIn h73 hφbar (L := L') hVL ?_
  exact IsSevenNineGroup.congr eL hD hL

end Seven

end CFSG.LocalAnalysis.WeakClosure81

end
