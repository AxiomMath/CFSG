module

public import CFSG.LocalAnalysis.StandardType.GGResIDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L K : Subgroup G} {Λ : Type}
  [Fintype Λ] [DecidableEq Λ] {b : Λ} {CL : Matrix Λ Λ ℤ}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
  {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}

theorem ggResI_stdDatum (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hind : LinearIndependent (ZMod p) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hu : α none (h (some b)) = 0) {M₀ : CoxeterMatrix (Option Λ)} (hW₀ : GGIsWeylMatrix M₀)
    (hC₀ : GGIntCartan M₀ (ggResIGlue b CL CK)) : GGCoxeterStdDatum p Bs L K := by
  refine ⟨Λ, inferInstance, inferInstance, M₀, ggResIGlue b CL CK, V, inferInstance,
    inferInstance, ι, φ, h, α, b, hW₀, hC₀, hφ, hind, ?_, ?_, hAL, hAK⟩
  · rintro (_ | i) (_ | j) hne
    · exact hK none none
    · by_cases hj : j = b
      · subst hj
        rw [hu]
        simp [ggResIGlue]
      · rw [show ggResIGlue b CL CK none (some j) = CK none (some ⟨j, hj⟩) by
          simp [ggResIGlue, hj]]
        exact hK none (some ⟨j, hj⟩)
    · by_cases hi : i = b
      · subst hi
        exact absurd rfl hne
      · rw [show ggResIGlue b CL CK (some i) none = CK (some ⟨i, hi⟩) none by
          simp [ggResIGlue, hi]]
        exact hK (some ⟨i, hi⟩) none
    · exact hL i j
  · simp [ggResIGlue]

theorem ggResI_forkDatum {ML : CoxeterMatrix Λ} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    (hCK : GGIntCartan MK CK) (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hind : LinearIndependent (ZMod p) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hfork : GGResIForkShape b CL CK) : GGCoxeterForkDatum p Bs L K := by
  obtain ⟨c, hbL, hbR, haL, haR⟩ := hfork
  have hsub : ∀ i (hi : i ≠ b), ((⟨i, hi⟩ : {i : Λ // i ≠ b}) = c ↔ i = c.1) := fun i hi =>
    Subtype.ext_iff
  have hfam : ggOptFam (h none) (fun i : Λ => h (some i)) = h := by
    funext o
    cases o <;> rfl
  have hpair : GGForkPairing CL b c.1 (fun i => h (some i)) (fun i => α (some i)) (h none)
      (α none) := by
    refine ⟨c.2.symm, hL, hCL.1, fun i hi => ?_, fun i hi => ?_, ?_, fun i hi => ?_,
      fun i hi => ?_⟩
    · have := hbL ⟨i, hi⟩
      simp only [hsub i hi] at this
      exact this
    · have := hbR ⟨i, hi⟩
      simp only [hsub i hi] at this
      exact this
    · have := hK none none
      rw [hCK.1 none] at this
      simpa using this
    · have h1 := hK none (some ⟨i, hi⟩)
      rw [haL ⟨i, hi⟩] at h1
      simp only [Option.map_none, Option.map_some] at h1
      rw [h1]
      by_cases hc : i = c.1
      · rw [if_pos ((hsub i hi).mpr hc), if_pos hc]
        simp
      · rw [if_neg (fun h' => hc ((hsub i hi).mp h')), if_neg hc]
        simp
    · have h1 := hK (some ⟨i, hi⟩) none
      rw [haR ⟨i, hi⟩] at h1
      simp only [Option.map_none, Option.map_some] at h1
      rw [h1]
      by_cases hc : i = c.1
      · rw [if_pos ((hsub i hi).mpr hc), if_pos hc]
        simp
      · rw [if_neg (fun h' => hc ((hsub i hi).mp h')), if_neg hc]
        simp
  have hAK' : ggAutomizer K Bs = Subgroup.closure
      ((fun i : Λ => φ (some i)) '' {i | i ≠ b} ∪ {φ none}) := by
    rw [hAK]
    congr 1
    ext γ
    simp only [Set.mem_union, Set.mem_range, Set.mem_image, Set.mem_setOf_eq,
      Set.mem_singleton_iff, Subtype.exists]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr rfl
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr rfl
  exact ⟨Λ, inferInstance, inferInstance, ML, CL, V, inferInstance, inferInstance, ι,
    fun i => φ (some i), φ none, fun i => h (some i), fun i => α (some i), h none, α none, b, c.1,
    hWL, hCL, hpair, fun i w => hφ (some i) w, hφ none, by rw [hfam]; exact hind, hAL, hAK'⟩

end CFSG.StandardType
