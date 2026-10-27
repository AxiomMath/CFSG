module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Option

variable {Λ X : Type*}

@[expose] def ggOptFam (x : X) (f : Λ → X) : Option Λ → X := fun o => Option.casesOn' o x f

@[simp] theorem ggOptFam_none (x : X) (f : Λ → X) : ggOptFam x f none = x := rfl

@[simp] theorem ggOptFam_some (x : X) (f : Λ → X) (i : Λ) : ggOptFam x f (some i) = f i := rfl

theorem range_ggOptFam (x : X) (f : Λ → X) :
    Set.range (ggOptFam x f) = Set.range f ∪ {x} := by
  ext y
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_ | i, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨some i, rfl⟩
    · exact ⟨none, rfl⟩

theorem linearIndependent_ggOptFam {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {x : V} {f : Λ → V} :
    LinearIndependent K (ggOptFam x f) ↔
      LinearIndependent K f ∧ x ∉ Submodule.span K (Set.range f) :=
  linearIndependent_option'

variable [DecidableEq Λ]

@[expose] def ggAttachCartan (C : Matrix Λ Λ ℤ) (k : Λ) : Matrix (Option Λ) (Option Λ) ℤ :=
  Matrix.of fun i j => Option.casesOn' i (Option.casesOn' j 2 fun j => if j = k then -1 else 0)
    fun i => Option.casesOn' j (if i = k then -1 else 0) fun j => C i j

@[simp] theorem ggAttachCartan_none_none (C : Matrix Λ Λ ℤ) (k : Λ) :
    ggAttachCartan C k none none = 2 := rfl

@[simp] theorem ggAttachCartan_none_some (C : Matrix Λ Λ ℤ) (k j : Λ) :
    ggAttachCartan C k none (some j) = if j = k then -1 else 0 := rfl

@[simp] theorem ggAttachCartan_some_none (C : Matrix Λ Λ ℤ) (k i : Λ) :
    ggAttachCartan C k (some i) none = if i = k then -1 else 0 := rfl

@[simp] theorem ggAttachCartan_some_some (C : Matrix Λ Λ ℤ) (k i j : Λ) :
    ggAttachCartan C k (some i) (some j) = C i j := rfl

end Option

section Fork

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

structure GGForkPairing {Λ : Type*} [DecidableEq Λ] (C : Matrix Λ Λ ℤ) (b c : Λ) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (ha : V) (αa : Module.Dual (ZMod p) V) : Prop where
  ne : b ≠ c
  pair : ∀ i j, α i (h j) = (C i j : ZMod p)
  diag : ∀ i, C i i = 2
  bL : ∀ i, i ≠ b → C b i = if i = c then -1 else 0
  bR : ∀ i, i ≠ b → C i b = if i = c then -1 else 0
  aa : αa ha = 2
  aL : ∀ i, i ≠ b → αa (h i) = if i = c then -1 else 0
  aR : ∀ i, i ≠ b → α i ha = if i = c then -1 else 0

variable {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V}
  {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}

theorem GGForkPairing.self (hF : GGForkPairing C b c h α ha αa) (i : Λ) : α i (h i) = 2 := by
  rw [hF.pair, hF.diag]
  simp

theorem GGForkPairing.b_c (hF : GGForkPairing C b c h α ha αa) : α b (h c) = -1 := by
  rw [hF.pair, hF.bL c hF.ne.symm]
  simp

theorem GGForkPairing.c_b (hF : GGForkPairing C b c h α ha αa) : α c (h b) = -1 := by
  rw [hF.pair, hF.bR c hF.ne.symm]
  simp

theorem GGForkPairing.a_c (hF : GGForkPairing C b c h α ha αa) : αa (h c) = -1 := by
  rw [hF.aL c hF.ne.symm]
  simp

theorem GGForkPairing.c_a (hF : GGForkPairing C b c h α ha αa) : α c ha = -1 := by
  rw [hF.aR c hF.ne.symm]
  simp

theorem GGForkPairing.aL_sub_bL (hF : GGForkPairing C b c h α ha αa) {i : Λ} (hi : i ≠ b) :
    αa (h i) - α b (h i) = 0 := by
  rw [hF.aL i hi, hF.pair, hF.bL i hi]
  split_ifs <;> simp

theorem GGForkPairing.aR_sub_bR (hF : GGForkPairing C b c h α ha αa) {i : Λ} (hi : i ≠ b) :
    α i ha - α i (h b) = 0 := by
  rw [hF.aR i hi, hF.pair, hF.bR i hi]
  split_ifs <;> simp

end Fork

section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V]

theorem ggLin_conj_reflection (ι : Additive ↥Bs ≃+ V) {φ ψ : MulAut ↥Bs} {x y : V}
    {f g : Module.Dual (ZMod p) V} (hgy : g y = 2)
    (hψ : ∀ w, ggLin (p := p) ι ψ w = w - f w • x)
    (hφ : ∀ w, ggLin (p := p) ι φ w = w - g w • y) (z : V) :
    ggLin (p := p) ι (φ * ψ * φ⁻¹) z = z - (f z - f y * g z) • (x - g x • y) := by
  have hinv : ggLin (p := p) ι φ⁻¹ = ggLin (p := p) ι φ := by
    rw [map_inv, ggLin_eq_reflection ι hgy hφ, reflection_inv]
  rw [map_mul, map_mul, hinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact conj_apply_of_reflection_formula (Q := (ggLin (p := p) ι ψ).toLinearMap)
    (S := (ggLin (p := p) ι φ).toLinearMap) hψ hφ hgy z

variable {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V}
  {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}

theorem ggFork_cross_iff (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) (ι : Additive ↥Bs ≃+ V)
    (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs}
    (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha) :
    (αa (h b) = 0 ↔ α b ha = 0) ∧ (αa (h b) = 1 ↔ α b ha = 1) := by
  have hLa := ggLin_eq_reflection ι hF.aa hlina
  have hLb := ggLin_eq_reflection ι (hF.self b) (hlin b)
  have hψ : φ c * φa * (φ c)⁻¹ ∈ ggInduced ⊤ Bs :=
    mul_mem_ggInduced (mul_mem_ggInduced (hφ c) hφa) (inv_mem_ggInduced (hφ c))
  have hθ : (αa + α c) (ha + h c) = 2 := by
    simp only [LinearMap.add_apply, map_add, hF.aa, hF.a_c, hF.c_a, hF.self c]
    ring
  have hlinψ : ∀ z, ggLin (p := p) ι (φ c * φa * (φ c)⁻¹) z =
      z - (αa + α c) z • (ha + h c) := by
    intro z
    rw [ggLin_conj_reflection ι (hF.self c) hlina (hlin c), hF.a_c, hF.c_a,
      LinearMap.add_apply]
    module
  have hLψ := ggLin_eq_reflection ι hθ hlinψ
  have hθb : (αa + α c) (h b) = αa (h b) - 1 := by
    rw [LinearMap.add_apply, hF.c_b]
    ring
  have hbθ : α b (ha + h c) = α b ha - 1 := by
    rw [map_add, hF.b_c]
    ring
  refine ⟨⟨fun h0 => ggCross_eq_zero_of_noTransvection hp2 hNT ι hφa (hφ b) hF.aa (hF.self b)
      hLa hLb h0, fun h0 => ggCross_eq_zero_of_noTransvection hp2 hNT ι (hφ b) hφa (hF.self b)
      hF.aa hLb hLa h0⟩, ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · have h0 : (αa + α c) (h b) = 0 := by rw [hθb, h1, sub_self]
    have := ggCross_eq_zero_of_noTransvection hp2 hNT ι hψ (hφ b) hθ (hF.self b) hLψ hLb h0
    rw [hbθ] at this
    exact sub_eq_zero.mp this
  · have h0 : α b (ha + h c) = 0 := by rw [hbθ, h1, sub_self]
    have := ggCross_eq_zero_of_noTransvection hp2 hNT ι (hφ b) hψ (hF.self b) hθ hLb hLψ h0
    rw [hθb] at this
    exact sub_eq_zero.mp this

theorem ggFork_ext_reflection (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa)
    {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs)
    (hφa : φa ∈ ggInduced ⊤ Bs) (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha) (hu : αa (h b) = 1)
    (hv : α b ha = 1) :
    φ b * φa * (φ b)⁻¹ ∈ ggInduced ⊤ Bs ∧ ∀ z, ggLin (p := p) ι (φ b * φa * (φ b)⁻¹) z =
      z - (αa - α b) z • (ha - h b) := by
  refine ⟨mul_mem_ggInduced (mul_mem_ggInduced (hφ b) hφa) (inv_mem_ggInduced (hφ b)),
    fun z => ?_⟩
  rw [ggLin_conj_reflection ι (hF.self b) hlina (hlin b), hu, hv, LinearMap.sub_apply]
  module

end GG

section Weyl

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V} {ha : V}
  {αa : Module.Dual (ZMod p) V}

theorem ggWeylReflectionGroup_of_fork_zero (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) (hu : αa (h b) = 0)
    {M : CoxeterMatrix (Option Λ)} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M (ggAttachCartan C c)) :
    GGWeylReflectionGroup p (Subgroup.closure (Set.range φ ∪ {φa})) := by
  have hFT := isFiniteType_of_ggIsWeylMatrixFixed (hM : GGIsWeylMatrixFixed M) hC
  have hα : ∀ o, ggOptFam αa α o (ggOptFam ha h o) = 2 := by
    rintro (_ | i)
    · exact hF.aa
    · exact hF.self i
  have hlin' : ∀ o, ggLin (p := p) ι (ggOptFam φa φ o) = reflection (hα o) := by
    rintro (_ | i)
    · exact ggLin_eq_reflection ι (hα none) hlina
    · exact ggLin_eq_reflection ι (hα (some i)) (hlin i)
  have hP : ∀ i j, (i, j) ≠ (some b, none) →
      ggOptFam αa α i (ggOptFam ha h j) = (ggAttachCartan C c i j : ZMod p) := by
    rintro (_ | i) (_ | j) hij
    · simp [hF.aa]
    · by_cases hjb : j = b
      · subst hjb
        simp [hu, hF.ne]
      · simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_none_some, hF.aL j hjb]
        split_ifs <;> simp
    · have hib : i ≠ b := fun h' => hij (by rw [h'])
      simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_some_none, hF.aR i hib]
      split_ifs <;> simp
    · simp only [ggOptFam_some, ggAttachCartan_some_some, hF.pair]
  have key := ggWeylReflectionGroup_of_label_of_isFiniteType hp2 hNT hM hC hFT
    (ggOptFam φa φ) (by rintro (_ | i); exacts [hφa, hφ i]) ι (ggOptFam ha h) (ggOptFam αa α) hα
    hlin' hind none (some b) hP (by simp [hF.ne])
  rwa [range_ggOptFam] at key

theorem ggWeylReflectionGroup_of_fork_one (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) (hu : αa (h b) = 1)
    {M : CoxeterMatrix (Option Λ)} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M (ggAttachCartan C b)) :
    GGWeylReflectionGroup p (Subgroup.closure (Set.range φ ∪ {φa})) := by
  have hv : α b ha = 1 := (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).2.mp hu
  obtain ⟨hψ, hlinψ⟩ := ggFork_ext_reflection ι hF hφ hφa hlin hlina hu hv
  have hFT := isFiniteType_of_ggIsWeylMatrixFixed (hM : GGIsWeylMatrixFixed M) hC
  have hθ : (αa - α b) (ha - h b) = 2 := by
    simp only [LinearMap.sub_apply, map_sub, hF.aa, hu, hv, hF.self b]
    ring
  have hα : ∀ o, ggOptFam (αa - α b) α o (ggOptFam (ha - h b) h o) = 2 := by
    rintro (_ | i)
    · exact hθ
    · exact hF.self i
  have hlin' : ∀ o, ggLin (p := p) ι (ggOptFam (φ b * φa * (φ b)⁻¹) φ o) =
      reflection (hα o) := by
    rintro (_ | i)
    · exact ggLin_eq_reflection ι (hα none) hlinψ
    · exact ggLin_eq_reflection ι (hα (some i)) (hlin i)
  have hind' : LinearIndependent (ZMod p) (ggOptFam (ha - h b) h) := by
    rw [linearIndependent_ggOptFam] at hind ⊢
    refine ⟨hind.1, fun hmem => hind.2 ?_⟩
    have h3 := Submodule.add_mem _ hmem
      (Submodule.subset_span ⟨b, rfl⟩ : h b ∈ Submodule.span (ZMod p) (Set.range h))
    rwa [sub_add_cancel] at h3
  have hP : ∀ i j, ggOptFam (αa - α b) α i (ggOptFam (ha - h b) h j) =
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
  have key := ggWeylReflectionGroup_of_label_of_isFiniteType hp2 hNT hM hC hFT
    (ggOptFam (φ b * φa * (φ b)⁻¹) φ) (by rintro (_ | i); exacts [hψ, hφ i]) ι
    (ggOptFam (ha - h b) h) (ggOptFam (αa - α b) α) hα hlin' hind' none (some c)
    (fun i j _ => hP i j) (by simp [hF.ne.symm])
  rwa [range_ggOptFam, closure_union_conj (Set.range φ) φa (φ b)
    (Subgroup.subset_closure ⟨b, rfl⟩)] at key

theorem ggWeylReflectionGroup_of_fork (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hlab : (αa (h b) = 0 ∧ ∃ M : CoxeterMatrix (Option Λ), GGIsWeylMatrix M ∧
        GGIntCartan M (ggAttachCartan C c)) ∨
      (αa (h b) = 1 ∧ ∃ M : CoxeterMatrix (Option Λ), GGIsWeylMatrix M ∧
        GGIntCartan M (ggAttachCartan C b))) :
    GGWeylReflectionGroup p (Subgroup.closure (Set.range φ ∪ {φa})) := by
  rcases hlab with ⟨hu, M, hM, hC⟩ | ⟨hu, M, hM, hC⟩
  · exact ggWeylReflectionGroup_of_fork_zero hp2 hNT ι hF hφ hφa hlin hlina hind hu hM hC
  · exact ggWeylReflectionGroup_of_fork_one hp2 hNT ι hF hφ hφa hlin hlina hind hu hM hC

theorem ggWeylReflectionGroup_sup_of_fork (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hlab : (αa (h b) = 0 ∧ ∃ M : CoxeterMatrix (Option Λ), GGIsWeylMatrix M ∧
        GGIntCartan M (ggAttachCartan C c)) ∨
      (αa (h b) = 1 ∧ ∃ M : CoxeterMatrix (Option Λ), GGIsWeylMatrix M ∧
        GGIntCartan M (ggAttachCartan C b)))
    {L K : Subgroup G} (hL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hK : ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa})) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i =>
    mem_ggInduced_top_of_mem_ggAutomizer (H := L)
      (by rw [hL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hφa : φa ∈ ggInduced ⊤ Bs := mem_ggInduced_top_of_mem_ggAutomizer (H := K)
    (by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl))
  have hj : ggAutomizer L Bs ⊔ ggAutomizer K Bs =
      Subgroup.closure (Set.range φ ∪ {φa}) := by
    rw [hL, hK, ← Subgroup.closure_union]
    congr 1
    ext ψ
    simp only [Set.mem_union, Set.mem_range, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, -, rfl⟩ | rfl)
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr rfl
    · rintro (⟨i, rfl⟩ | rfl)
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr (Or.inr rfl)
  rw [hj]
  exact ggWeylReflectionGroup_of_fork hp2 hNT ι hF hφ hφa hlin hlina hind hlab

end Weyl

end CFSG.StandardType
