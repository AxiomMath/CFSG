module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem ggPairing_eq_of_label (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {Γ : Type}
    {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) (φ : Γ → MulAut ↥Bs)
    (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (h : Γ → V) (α : Γ → Module.Dual (ZMod p) V)
    (hα : ∀ i, α i (h i) = 2) (hlin : ∀ i, ggLin (p := p) ι (φ i) = reflection (hα i)) (a b : Γ)
    (hP : ∀ i j, (i, j) ≠ (b, a) → α i (h j) = (C i j : ZMod p)) (hCba : C b a = 0) :
    ∀ i j, α i (h j) = (C i j : ZMod p) := by
  intro i j
  by_cases hij : (i, j) = (b, a)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
    by_cases hab : j = i
    · subst hab
      rw [hα, hC.1]
      norm_num
    · have hu : α j (h i) = 0 := by
        rw [hP j i (fun h' => hab (Prod.mk.inj h').1), hC.eq_zero_symm hab hCba, Int.cast_zero]
      rw [hCba, Int.cast_zero]
      exact ggCross_eq_zero_of_noTransvection hp2 hNT ι (hφ j) (hφ i) (hα j) (hα i)
        (hlin j) (hlin i) hu
  · exact hP i j hij

theorem ggWeylReflectionGroup_of_label_of_isFiniteType (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ} (hM : GGIsWeylMatrix M)
    {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) (hFT : TauCeti.IsFiniteType C)
    (φ : Γ → MulAut ↥Bs) (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (h : Γ → V) (α : Γ → Module.Dual (ZMod p) V)
    (hα : ∀ i, α i (h i) = 2) (hlin : ∀ i, ggLin (p := p) ι (φ i) = reflection (hα i))
    (hind : LinearIndependent (ZMod p) h) (a b : Γ)
    (hP : ∀ i j, (i, j) ≠ (b, a) → α i (h j) = (C i j : ZMod p)) (hCba : C b a = 0) :
    GGWeylReflectionGroup p (Subgroup.closure (Set.range φ)) := by
  have hPall := ggPairing_eq_of_label hp2 hNT hC φ hφ ι h α hα hlin a b hP hCba
  have hlinL := isLiftable_reflection_of_intCartan hC h α hα hPall
  have hφL : M.IsLiftable φ := by
    intro i j
    apply ggLin_injective (p := p) ι
    rw [map_pow, map_mul, hlin, hlin, map_one]
    exact hlinL i j
  refine ggWeylReflectionGroup_of_lift hM φ hφL
    (fun i => ggIsReflection_of_eq_reflection hp2 ι (hα i) (hlin i)) ?_
  have hinjL := ggCartanFaithful_of_isFiniteType hα hPall hp2 hFT hC hind
  have hcomp : (ggLin (p := p) ι).comp (M.toCoxeterSystem.lift ⟨φ, hφL⟩) =
      M.toCoxeterSystem.lift ⟨_, hlinL⟩ := by
    refine M.toCoxeterSystem.ext_simple fun i => ?_
    rw [MonoidHom.comp_apply, CoxeterSystem.lift_apply_simple, CoxeterSystem.lift_apply_simple,
      hlin]
  intro w₁ w₂ hw
  apply hinjL
  rw [← hcomp, MonoidHom.comp_apply, MonoidHom.comp_apply, hw]

theorem ggWeylReflectionGroup_sup_of_label_of_isFiniteType (hp2 : p ≠ 2)
    (hNT : GGNoTransvection p Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix (Option Λ)} (hM : GGIsWeylMatrix M) {C : Matrix (Option Λ) (Option Λ) ℤ}
    (hC : GGIntCartan M C) (hFT : TauCeti.IsFiniteType C) (φ : Option Λ → MulAut ↥Bs)
    (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V)
    (hα : ∀ i, α i (h i) = 2) (hlin : ∀ i, ggLin (p := p) ι (φ i) = reflection (hα i))
    (hind : LinearIndependent (ZMod p) h) (b : Λ)
    (hP : ∀ i j, (i, j) ≠ (some b, none) → α i (h j) = (C i j : ZMod p))
    (hCba : C (some b) none = 0) {L K : Subgroup G}
    (hL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none})) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hrange : (Set.range fun i : Λ => φ (some i)) ∪
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}) = Set.range φ := by
    ext ψ
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Subtype.exists]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, -, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨i | i, rfl⟩
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨i, rfl⟩
  rw [hL, hK, ← Subgroup.closure_union, hrange]
  exact ggWeylReflectionGroup_of_label_of_isFiniteType hp2 hNT hM hC hFT φ hφ ι h α hα hlin hind
    none (some b) hP hCba

end CFSG.StandardType
