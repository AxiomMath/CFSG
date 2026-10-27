module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoBridge
public import CFSG.LocalAnalysis.StandardType.GGLevTwoEngineA
public import CFSG.LocalAnalysis.StandardType.GGLevTwoEngineB
public import CFSG.LocalAnalysis.StandardType.GGLevTwoEngineD
public import CFSG.LocalAnalysis.StandardType.GGLevTwoExcKac
public import CFSG.LocalAnalysis.StandardType.GGLevTwoExcFinite

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType

theorem levTwoEngine_E6 :
    LevTwoEngine LevTwoType.E6 := levTwoEngine_E6_of_finite excFinite_E6

theorem levTwoEngine_E7 :
    LevTwoEngine LevTwoType.E7 := levTwoEngine_E7_of_finite excFinite_E7

theorem levTwoEngine_E8 :
    LevTwoEngine LevTwoType.E8 := levTwoEngine_E8_of_finite excFinite_E8

theorem levTwoEngine_F4 :
    LevTwoEngine LevTwoType.F4 := levTwoEngine_F4_of_finite excFinite_F4

theorem levTwoEngine_all
    (T : LevTwoType) (hT : T.Valid) : LevTwoEngine T := by
  cases T with
  | A n => exact levTwoEngine_A n hT
  | B n => exact levTwoEngine_B n hT
  | D n => exact levTwoEngine_D n hT
  | E6 => exact levTwoEngine_E6
  | E7 => exact levTwoEngine_E7
  | E8 => exact levTwoEngine_E8
  | F4 => exact levTwoEngine_F4

section Glue

theorem levTwoFamilyOfHtc {B : Type} [Group B] (A AL : Subgroup B) (Rf : Set B)
    (htc : ∀ T : Set B, T ⊆ Rf → ∃ T' : Finset B, (T' : Set B) ⊆ T ∧ T'.card ≤ 2 ∧
      AL ⊔ Subgroup.closure T = AL ⊔ Subgroup.closure (T' : Set B))
    (𝒮 : Set (Subgroup B)) (h𝒮 : ∀ K ∈ 𝒮, K ≤ A ∧ K = Subgroup.closure {a | a ∈ K ∧ a ∈ Rf}) :
    ∃ 𝒮' : Finset (Subgroup B), (𝒮' : Set (Subgroup B)) ⊆ 𝒮 ∧ 𝒮'.card ≤ 2 ∧
      AL ⊔ ⨆ K ∈ 𝒮, K = AL ⊔ ⨆ K ∈ 𝒮', K := by
  classical
  set T : Set B := {a | ∃ K ∈ 𝒮, a ∈ K ∧ a ∈ Rf} with hT
  have hTR : T ⊆ Rf := fun a ⟨_, _, _, ha⟩ => ha
  obtain ⟨T', hT'T, hcard, heq⟩ := htc T hTR
  have hS : ⨆ K ∈ 𝒮, K = Subgroup.closure T := by
    apply le_antisymm
    · refine iSup₂_le fun K hK => ?_
      rw [(h𝒮 K hK).2]
      exact Subgroup.closure_mono (fun a ⟨haK, haR⟩ => ⟨K, hK, haK, haR⟩)
    · rw [Subgroup.closure_le]
      intro a ⟨K, hK, haK, _⟩
      exact (le_iSup₂ (f := fun K (_ : K ∈ 𝒮) => K) K hK) haK
  have hex : ∀ t ∈ T, ∃ K : Subgroup B, K ∈ 𝒮 ∧ t ∈ K := fun t ⟨K, hK, htK, _⟩ => ⟨K, hK, htK⟩
  let Kof : B → Subgroup B := fun t => if h : t ∈ T then Classical.choose (hex t h) else ⊥
  have hKof : ∀ t ∈ T, Kof t ∈ 𝒮 ∧ t ∈ Kof t := by
    intro t ht
    simp only [Kof, dif_pos ht]
    exact Classical.choose_spec (hex t ht)
  refine ⟨T'.image Kof, ?_, Finset.card_image_le.trans hcard, ?_⟩
  · intro K hK
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hK)
    exact (hKof t (hT'T ht)).1
  · rw [hS, heq]
    apply le_antisymm
    · refine sup_le_sup_left ?_ AL
      rw [Subgroup.closure_le]
      intro t ht
      exact (le_iSup₂ (f := fun K (_ : K ∈ T'.image Kof) => K) (Kof t)
        (Finset.mem_image_of_mem Kof ht)) (hKof t (hT'T ht)).2
    · refine sup_le le_sup_left (iSup₂_le fun K hK => ?_)
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hK
      have h1 := (hKof t (hT'T ht)).1
      have h2 : Kof t ≤ ⨆ K ∈ 𝒮, K := le_iSup₂ (f := fun K (_ : K ∈ 𝒮) => K) (Kof t) h1
      rw [hS] at h2
      exact h2.trans (le_sup_right.trans heq.le)

theorem levTwoHtcOfTwoCover {W B : Type} [Group W] [Group B] (φ : W →* B) (X : Subgroup W)
    (Refl' : Set W)
    (htc : ∀ T : Set W, T ⊆ Refl' → ∃ T' : Finset W, (T' : Set W) ⊆ T ∧ T'.card ≤ 2 ∧
      X ⊔ Subgroup.closure T = X ⊔ Subgroup.closure (T' : Set W))
    (AL : Subgroup B) (hAL : X.map φ = AL) (Rf : Set B) (hRf : Rf = φ '' Refl') :
    ∀ T : Set B, T ⊆ Rf → ∃ T' : Finset B, (T' : Set B) ⊆ T ∧ T'.card ≤ 2 ∧
      AL ⊔ Subgroup.closure T = AL ⊔ Subgroup.closure (T' : Set B) := by
  classical
  intro T hT
  set T₀ : Set W := {g | g ∈ Refl' ∧ φ g ∈ T} with hT₀
  have hT₀R : T₀ ⊆ Refl' := fun g hg => hg.1
  have himg : φ '' T₀ = T := by
    ext b
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg.2
    · intro hb
      have := hT hb
      rw [hRf] at this
      obtain ⟨g, hg, rfl⟩ := this
      exact ⟨g, ⟨hg, hb⟩, rfl⟩
  obtain ⟨T₀', hsub, hcard, heq⟩ := htc T₀ hT₀R
  refine ⟨T₀'.image φ, ?_, Finset.card_image_le.trans hcard, ?_⟩
  · intro b hb
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    exact (hsub hg).2
  · have h1 := congrArg (Subgroup.map φ) heq
    rw [Subgroup.map_sup, Subgroup.map_sup, hAL, MonoidHom.map_closure, MonoidHom.map_closure,
      himg] at h1
    rw [Finset.coe_image]
    exact h1

end Glue

section Assembly

theorem levTwoDispatch {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hG2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) (f : M.Group ≃* ↥A)
    (hf : ∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) :
    ∃ (T : LevTwoType) (_ : T.Valid) (f' : T.coxeter.Group ≃* ↥A),
      ∀ i : Fin T.n, GGIsReflection p ((f' (T.coxeter.simple i) : ↥A) : MulAut ↥Bs) := by
  have hW : GGWeylOfType p M A := ⟨f, hf⟩
  rcases hM with ⟨n, e, hn, rfl | ⟨hn2, rfl⟩ | ⟨hn4, rfl⟩⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ |
    ⟨e, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨f', hf'⟩ := hW.of_reindex
    exact ⟨LevTwoType.A n, hn, f', hf'⟩
  · obtain ⟨f', hf'⟩ := hW.of_reindex
    exact ⟨LevTwoType.B n, hn2, f', hf'⟩
  · obtain ⟨f', hf'⟩ := hW.of_reindex
    exact ⟨LevTwoType.D n, hn4, f', hf'⟩
  · obtain ⟨f', hf'⟩ := hW.of_reindex
    exact ⟨LevTwoType.E6, trivial, f', hf'⟩
  · obtain ⟨f', hf'⟩ := hW.of_reindex
    exact ⟨LevTwoType.E7, trivial, f', hf'⟩
  · obtain ⟨f', hf'⟩ := hW.of_reindex
    exact ⟨LevTwoType.E8, trivial, f', hf'⟩
  · obtain ⟨f', hf'⟩ := hW.of_reindex
    exact ⟨LevTwoType.F4, trivial, f', hf'⟩
  · exact absurd ⟨e, rfl⟩ hG2

theorem _root_.CFSG.StandardType.ggSecFiveLevTwoInput'_holds :
    GGSecFiveLevTwoInput' := by
  intro G _ _ p Bs hp hp2 hEl hNT A hA ι M hM hG2 f hf x AL ιL _ ML hAL hfix hML hW hcard hSat 𝒮 h𝒮
  obtain ⟨T, hT, f', hf'⟩ := levTwoDispatch hM hG2 f hf
  obtain ⟨c, Φ, ρ, hdata, hdict, hAL'⟩ :=
    levTwoModel T hT p Bs hp hp2 hEl hNT A hA f' hf' x AL ιL ML hAL hfix hML hW hcard hSat
  have htc := twoCover_of_tcRoot T.rootFT hdata.isRt
    (levTwoEngine_all T hT p hp hp2 c Φ hdata)
  refine levTwoFamilyOfHtc A AL {a | a ∈ A ∧ GGIsReflection p a}
    (levTwoHtcOfTwoCover (A.subtype.comp ρ.toMonoidHom) (Wsub T.rootFT Φ) (Refl T.rootFT) htc AL hAL' _ ?_)
    𝒮 (fun K hK => ⟨(h𝒮 K hK).1, ?_⟩)
  · ext a
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro ha
      obtain ⟨g, hg, hga⟩ := (hdict a).1 ha
      exact ⟨g, hg, by simpa using hga⟩
    · rintro ⟨g, hg, rfl⟩
      exact (hdict _).2 ⟨g, hg, by simp⟩
  · have hKA := (h𝒮 K hK).1
    have hset : {a | a ∈ K ∧ a ∈ {a | a ∈ A ∧ GGIsReflection p a}} =
        {a | a ∈ K ∧ GGIsReflection p a} := by
      ext a
      constructor
      · rintro ⟨haK, _, hr⟩
        exact ⟨haK, hr⟩
      · rintro ⟨haK, hr⟩
        exact ⟨haK, hKA haK, hr⟩
    rw [hset]
    exact (h𝒮 K hK).2

end Assembly

end CFSG.StandardType.LevTwo
