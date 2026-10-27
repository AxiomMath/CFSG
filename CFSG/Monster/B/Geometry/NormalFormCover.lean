module

public import CFSG.Monster.B.Geometry.StrictGallery
public import CFSG.Monster.B.Geometry.ChamberCover
public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.GroupActions.Exchange

namespace ChamberSystem

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {X : ChamberSystem ι C}

theorem IsReducedOrdinary.of_append_left {x : C} {γ η : List (ι × C)}
    (h : X.IsReducedOrdinary cs x (γ ++ η)) : X.IsReducedOrdinary cs x γ := by
  refine ⟨((isOrdinary_append x γ η).mp h.1).1, ?_⟩
  have := h.2.take γ.length
  rwa [galleryType_append, List.take_left' (length_galleryType γ)] at this

theorem IsReducedOrdinary.of_append_right {x : C} {γ η : List (ι × C)}
    (h : X.IsReducedOrdinary cs x (γ ++ η)) : X.IsReducedOrdinary cs (galleryEnd x γ) η := by
  refine ⟨((isOrdinary_append x γ η).mp h.1).2, ?_⟩
  have := h.2.drop γ.length
  rwa [galleryType_append, List.drop_left' (length_galleryType γ)] at this

theorem exists_strictHomotopic_concat
    (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y) {a : C}
    {ρ : List (ι × C)} (hρ : X.IsReducedOrdinary cs a ρ) {i : ι}
    (hi : cs.length (cs.wordProd (galleryType ρ) * cs.simple i) + 1 =
      cs.length (cs.wordProd (galleryType ρ))) :
    ∃ ρ₁ z, X.StrictHomotopic cs a ρ (ρ₁ ++ [(i, z)]) := by
  obtain ⟨w, hw⟩ : ∃ w, cs.wordProd (galleryType ρ) = w := ⟨_, rfl⟩
  rw [hw] at hi
  obtain ⟨β, hβ, hβw⟩ := cs.exists_isReduced (w * cs.simple i)
  have hβw' : cs.wordProd (β ++ [i]) = w := by
    rw [cs.wordProd_append, ← hβw, cs.wordProd_singleton, mul_assoc, cs.simple_mul_simple_self,
      mul_one]
  have hβi : cs.IsReduced (β ++ [i]) := by
    rw [CoxeterSystem.IsReduced, hβw', List.length_append, List.length_singleton, ← hβ.eq, ← hβw]
    omega
  obtain ⟨ρ', h1, -, h3⟩ := exists_strictHomotopic_of_isReduced hres hρ hβi (hβw'.trans hw.symm)
  obtain ⟨ρ₁, ⟨j, z⟩, rfl⟩ : ∃ ρ₁ q, ρ' = ρ₁ ++ [q] := by
    rcases List.eq_nil_or_concat' ρ' with h | h
    · subst h
      simp at h3
    · exact h
  have hj : j = i := by
    rw [galleryType_append] at h3
    simpa using (List.append_inj' h3 rfl).2
  subst hj
  exact ⟨ρ₁, z, h1⟩

variable (X cs) in
open _root_.Classical in
noncomputable def nfStep (a : C) (ρ : List (ι × C)) (i : ι) (y : C) : List (ι × C) :=
  if y = galleryEnd a ρ then ρ
  else if cs.length (cs.wordProd (galleryType ρ) * cs.simple i) =
      cs.length (cs.wordProd (galleryType ρ)) + 1 then ρ ++ [(i, y)]
  else if h : ∃ ρ₁ : List (ι × C), ∃ z : C, X.StrictHomotopic cs a ρ (ρ₁ ++ [(i, z)]) then
    if y = galleryEnd a h.choose then h.choose else h.choose ++ [(i, y)]
  else ρ

variable (X cs) in
noncomputable def normalForm (a : C) (γ : List (ι × C)) : List (ι × C) :=
  γ.foldl (fun ρ p => X.nfStep cs a ρ p.1 p.2) []

theorem normalForm_append (a : C) (γ η : List (ι × C)) :
    X.normalForm cs a (γ ++ η) =
      η.foldl (fun ρ p => X.nfStep cs a ρ p.1 p.2) (X.normalForm cs a γ) :=
  List.foldl_append ..

theorem normalForm_concat (a : C) (γ : List (ι × C)) (p : ι × C) :
    X.normalForm cs a (γ ++ [p]) = X.nfStep cs a (X.normalForm cs a γ) p.1 p.2 := by
  rw [normalForm_append]
  rfl

theorem nfStep_of_eq {a : C} {ρ : List (ι × C)} {i : ι} {y : C} (h : y = galleryEnd a ρ) :
    X.nfStep cs a ρ i y = ρ := by
  rw [nfStep, ite_eq_left h]

theorem nfStep_of_lt {a : C} {ρ : List (ι × C)} {i : ι} {y : C} (hne : y ≠ galleryEnd a ρ)
    (hl : cs.length (cs.wordProd (galleryType ρ) * cs.simple i) =
      cs.length (cs.wordProd (galleryType ρ)) + 1) :
    X.nfStep cs a ρ i y = ρ ++ [(i, y)] := by
  rw [nfStep, ite_eq_right hne, ite_eq_left hl]

theorem nfStep_of_gt (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
    {a : C} {ρ : List (ι × C)} (hρ : X.IsReducedOrdinary cs a ρ) {i : ι} {y : C}
    (hne : y ≠ galleryEnd a ρ)
    (hl : cs.length (cs.wordProd (galleryType ρ) * cs.simple i) + 1 =
      cs.length (cs.wordProd (galleryType ρ))) :
    ∃ ρ₁ z, X.StrictHomotopic cs a ρ (ρ₁ ++ [(i, z)]) ∧
      ((y = galleryEnd a ρ₁ ∧ X.nfStep cs a ρ i y = ρ₁) ∨
        (y ≠ galleryEnd a ρ₁ ∧ X.nfStep cs a ρ i y = ρ₁ ++ [(i, y)])) := by
  have hex := exists_strictHomotopic_concat hres hρ hl
  have hl' : ¬cs.length (cs.wordProd (galleryType ρ) * cs.simple i) =
      cs.length (cs.wordProd (galleryType ρ)) + 1 := by omega
  refine ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec, ?_⟩
  rw [nfStep, ite_eq_right hne, ite_eq_right hl', dite_eq_left hex]
  by_cases hy : y = galleryEnd a hex.choose
  · exact Or.inl ⟨hy, ite_eq_left hy⟩
  · exact Or.inr ⟨hy, ite_eq_right hy⟩

variable (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
include hres

theorem nfStep_spec {a : C} {ρ : List (ι × C)} (hρ : X.IsReducedOrdinary cs a ρ) {i : ι} {y : C}
    (hy : X.adj i (galleryEnd a ρ) y) :
    X.IsReducedOrdinary cs a (X.nfStep cs a ρ i y) ∧ galleryEnd a (X.nfStep cs a ρ i y) = y := by
  by_cases h1 : y = galleryEnd a ρ
  · rw [nfStep_of_eq h1]
    exact ⟨hρ, h1.symm⟩
  rcases cs.length_mul_simple (cs.wordProd (galleryType ρ)) i with h2 | h2
  · rw [nfStep_of_lt h1 h2]
    refine ⟨⟨(isOrdinary_concat a ρ (i, y)).mpr ⟨hρ.1, hy, Ne.symm h1⟩, ?_⟩, by simp⟩
    rw [CoxeterSystem.IsReduced, galleryType_append, cs.wordProd_append]
    simp [h2, hρ.2.eq]
  · obtain ⟨ρ₁, z, h3, h4⟩ := nfStep_of_gt hres hρ h1 h2
    have h5 := h3.isReducedOrdinary_iff.mp hρ
    have hend : galleryEnd a ρ = z := by rw [h3.galleryEnd_eq, galleryEnd_concat]
    obtain ⟨-, h6, -⟩ := (isOrdinary_concat a ρ₁ (i, z)).mp h5.1
    rcases h4 with ⟨h7, h8⟩ | ⟨h7, h8⟩
    · rw [h8]
      exact ⟨h5.of_append_left, h7.symm⟩
    · rw [h8]
      refine ⟨⟨(isOrdinary_concat a ρ₁ (i, y)).mpr ⟨h5.1.isGallery.of_append_left |>
        fun _ => ((isOrdinary_append a ρ₁ _).mp h5.1).1, adj_trans h6 (hend ▸ hy), Ne.symm h7⟩,
        ?_⟩, by simp⟩
      have := h5.2
      simpa [galleryType_append] using this

theorem normalForm_spec {a : C} {γ : List (ι × C)} (hγ : X.IsGallery a γ) :
    X.IsReducedOrdinary cs a (X.normalForm cs a γ) ∧
      galleryEnd a (X.normalForm cs a γ) = galleryEnd a γ := by
  induction γ using List.reverseRecOn with
  | nil => exact ⟨IsReducedOrdinary.nil a, rfl⟩
  | append_singleton γ p ih =>
    obtain ⟨h1, h2⟩ := (isGallery_concat a γ p).mp hγ
    obtain ⟨ih1, ih2⟩ := ih h1
    rw [normalForm_concat, galleryEnd_concat]
    exact nfStep_spec hres ih1 (ih2 ▸ h2)

theorem foldl_nfStep_spec {a : C} {ρ : List (ι × C)} (hρ : X.IsReducedOrdinary cs a ρ)
    {η : List (ι × C)} (hη : X.IsGallery (galleryEnd a ρ) η) :
    X.IsReducedOrdinary cs a (η.foldl (fun ρ p => X.nfStep cs a ρ p.1 p.2) ρ) ∧
      galleryEnd a (η.foldl (fun ρ p => X.nfStep cs a ρ p.1 p.2) ρ) =
        galleryEnd (galleryEnd a ρ) η := by
  induction η generalizing ρ with
  | nil => exact ⟨hρ, rfl⟩
  | cons p η ih =>
    obtain ⟨h1, h2⟩ := hη
    obtain ⟨h3, h4⟩ := nfStep_spec hres hρ h1
    rw [List.foldl_cons, galleryEnd_cons]
    have := ih h3 (by rw [h4]; exact h2)
    rwa [h4] at this

variable {a : C}
  (hrig : ∀ γ γ' : List (ι × C), X.IsReducedOrdinary cs a γ → X.StrictHomotopic cs a γ γ' →
    galleryType γ = galleryType γ' → γ = γ')
include hrig

theorem strictHomotopic_of_concat {ρ₁ ρ₂ : List (ι × C)} {i : ι} {z₁ z₂ : C}
    (h1 : X.IsReducedOrdinary cs a (ρ₁ ++ [(i, z₁)]))
    (h : X.StrictHomotopic cs a (ρ₁ ++ [(i, z₁)]) (ρ₂ ++ [(i, z₂)])) :
    X.StrictHomotopic cs a ρ₁ ρ₂ := by
  have h2 := h.isReducedOrdinary_iff.mp h1
  have hρ₁ := h1.of_append_left
  have hρ₂ := h2.of_append_left
  have hprod : cs.wordProd (galleryType ρ₂) = cs.wordProd (galleryType ρ₁) := by
    have := h.wordProd_eq
    simp only [galleryType_append, galleryType_cons, galleryType_nil, cs.wordProd_append,
      cs.wordProd_singleton] at this
    exact (mul_right_cancel this).symm
  obtain ⟨ρ₃, h3, h4, h5⟩ := exists_strictHomotopic_of_isReduced hres hρ₁ hρ₂.2 hprod
  have h6 : X.StrictHomotopic cs a (ρ₃ ++ [(i, z₁)]) (ρ₂ ++ [(i, z₂)]) :=
    (h3.symm.append_right _).trans h
  have h7 : X.IsReducedOrdinary cs a (ρ₃ ++ [(i, z₁)]) := h6.isReducedOrdinary_iff.mpr h2
  have h8 := hrig _ _ h7 h6 (by simp [galleryType_append, h5])
  obtain ⟨rfl, -⟩ := List.append_inj' h8 rfl
  exact h3

theorem nfStep_congr {ρ ρ' : List (ι × C)} (hρ : X.IsReducedOrdinary cs a ρ)
    (h : X.StrictHomotopic cs a ρ ρ') (i : ι) (y : C) :
    X.StrictHomotopic cs a (X.nfStep cs a ρ i y) (X.nfStep cs a ρ' i y) := by
  have hρ' := h.isReducedOrdinary_iff.mp hρ
  have hend := h.galleryEnd_eq
  have hprod := h.wordProd_eq
  by_cases h1 : y = galleryEnd a ρ
  · rw [nfStep_of_eq h1, nfStep_of_eq (hend ▸ h1)]
    exact h
  rcases cs.length_mul_simple (cs.wordProd (galleryType ρ)) i with h2 | h2
  · rw [nfStep_of_lt h1 h2, nfStep_of_lt (hend ▸ h1) (hprod ▸ h2)]
    exact h.append_right _
  · obtain ⟨ρ₁, z₁, h3, h4⟩ := nfStep_of_gt hres hρ h1 h2
    obtain ⟨ρ₂, z₂, h5, h6⟩ := nfStep_of_gt hres hρ' (hend ▸ h1) (hprod ▸ h2)
    have h7 : X.StrictHomotopic cs a (ρ₁ ++ [(i, z₁)]) (ρ₂ ++ [(i, z₂)]) :=
      (h3.symm.trans h).trans h5
    have h8 := strictHomotopic_of_concat hres hrig (h3.isReducedOrdinary_iff.mp hρ) h7
    have h9 := h8.galleryEnd_eq
    rcases h4 with ⟨h10, h11⟩ | ⟨h10, h11⟩ <;> rcases h6 with ⟨h12, h13⟩ | ⟨h12, h13⟩
    · rw [h11, h13]; exact h8
    · exact absurd (h10.trans h9) h12
    · exact absurd (h12.trans h9.symm) h10
    · rw [h11, h13]; exact h8.append_right _

theorem foldl_nfStep_congr {ρ ρ' : List (ι × C)} (hρ : X.IsReducedOrdinary cs a ρ)
    (h : X.StrictHomotopic cs a ρ ρ') {η : List (ι × C)} (hη : X.IsGallery (galleryEnd a ρ) η) :
    X.StrictHomotopic cs a (η.foldl (fun ρ p => X.nfStep cs a ρ p.1 p.2) ρ)
      (η.foldl (fun ρ p => X.nfStep cs a ρ p.1 p.2) ρ') := by
  induction η generalizing ρ ρ' with
  | nil => exact h
  | cons p η ih =>
    obtain ⟨h1, h2⟩ := hη
    obtain ⟨h3, h4⟩ := nfStep_spec hres hρ h1
    exact ih h3 (nfStep_congr hres hrig hρ h p.1 p.2) (by rw [h4]; exact h2)

theorem normalForm_strictHomotopic {γ : List (ι × C)} (hγ : X.IsReducedOrdinary cs a γ) :
    X.StrictHomotopic cs a (X.normalForm cs a γ) γ := by
  induction γ using List.reverseRecOn with
  | nil => rfl
  | append_singleton γ p ih =>
    have hγ₀ := hγ.of_append_left
    obtain ⟨-, hp1, hp2⟩ := (isOrdinary_concat a γ p).mp hγ.1
    have h1 := ih hγ₀
    obtain ⟨h2, h3⟩ := normalForm_spec hres hγ₀.1.isGallery
    rw [normalForm_concat]
    refine (nfStep_congr hres hrig h2 h1 p.1 p.2).trans ?_
    have hlen := length_mul_simple_of_isReduced_concat (cs := cs) (ω := galleryType γ) (i := p.1)
      (by simpa [galleryType_append] using hγ.2)
    rw [nfStep_of_lt (Ne.symm hp2) hlen]

variable (X cs) in
def IsRepAt (a : C) (κ₀ : List (ι × C)) (J : Set ι) (ρ : List (ι × C)) (d : C) : Prop :=
  ∃ σ, X.IsReducedOrdinary cs (galleryEnd a κ₀) σ ∧ (∀ s ∈ galleryType σ, s ∈ J) ∧
    galleryEnd (galleryEnd a κ₀) σ = d ∧ X.StrictHomotopic cs a ρ (κ₀ ++ σ)

section Residue

variable {κ₀ : List (ι × C)} (hκ₀ : X.IsReducedOrdinary cs a κ₀) {J : Set ι}
  (hadd : ∀ v ∈ cs.parabolic J, cs.length (cs.wordProd (galleryType κ₀) * v) =
    cs.length (cs.wordProd (galleryType κ₀)) + cs.length v)
include hκ₀ hadd

omit hres hrig in
theorem isReducedOrdinary_append_of_isRepAt {σ : List (ι × C)}
    (hσ : X.IsReducedOrdinary cs (galleryEnd a κ₀) σ) (hσJ : ∀ s ∈ galleryType σ, s ∈ J) :
    X.IsReducedOrdinary cs a (κ₀ ++ σ) := by
  refine ⟨(isOrdinary_append a κ₀ σ).mpr ⟨hκ₀.1, hσ.1⟩, ?_⟩
  rw [CoxeterSystem.IsReduced, galleryType_append, cs.wordProd_append,
    hadd _ (cs.wordProd_mem_parabolic hσJ), hκ₀.2.eq, hσ.2.eq, List.length_append]

omit hres hrig in
theorem IsRepAt.isReducedOrdinary {ρ : List (ι × C)} {d : C}
    (h : X.IsRepAt cs a κ₀ J ρ d) : X.IsReducedOrdinary cs a ρ ∧ galleryEnd a ρ = d := by
  obtain ⟨σ, hσ, hσJ, rfl, h⟩ := h
  refine ⟨h.isReducedOrdinary_iff.mpr (isReducedOrdinary_append_of_isRepAt hκ₀ hadd hσ hσJ), ?_⟩
  rw [h.galleryEnd_eq, galleryEnd_append]

variable {i j : ι} (hij : i ≠ j)
include hij

omit hrig hκ₀ hadd in
theorem strictHomotopic_of_isRepAt (hJ : J = {i, j}) {ρ ρ' : List (ι × C)} {d : C}
    (h : X.IsRepAt cs a κ₀ J ρ d) (h' : X.IsRepAt cs a κ₀ J ρ' d) :
    X.StrictHomotopic cs a ρ ρ' := by
  subst hJ
  obtain ⟨σ, hσ, hσJ, hσe, h⟩ := h
  obtain ⟨σ', hσ', hσ'J, hσ'e, h'⟩ := h'
  obtain ⟨δ, hB, hadj⟩ := hres i j hij (galleryEnd a κ₀)
  have hb := X.self_mem_residue {i, j} (galleryEnd a κ₀)
  have hd1 := dist_eq_of_isOrdinary hB hadj hb hσ.1 hσJ hσ.2
  have hd2 := dist_eq_of_isOrdinary hB hadj hb hσ'.1 hσ'J hσ'.2
  rw [hσe] at hd1
  rw [hσ'e] at hd2
  obtain ⟨p, hp⟩ := exists_isBraidPath_index hσ.2 hσ'.2 (hd1.symm.trans hd2)
  obtain ⟨σ'', hl, hσ''o, hσ''t, hσ''e⟩ := exists_isStrictLift hres hp hσ.1 rfl
  have heq : σ'' = σ' := eq_of_isOrdinary_of_isBuildingOn hB hadj hb hσ''o hσ'.1
    (by rw [hσ''t]; exact hσ'J) hσ''t (by rw [hσ''t]; exact hσ'.2) (by rw [hσ''e, hσe, hσ'e])
  subst heq
  have hs := (hl.strictHomotopic fun e he => hp.isValid_of_mem he).append_left (x := a) κ₀
  exact (h.trans hs).trans h'.symm

theorem IsRepAt.nfStep (hJ : J = {i, j}) {ρ : List (ι × C)} {d : C}
    (h : X.IsRepAt cs a κ₀ J ρ d) {s : ι} (hs : s ∈ J) {d' : C} (hd' : X.adj s d d') :
    X.IsRepAt cs a κ₀ J (X.nfStep cs a ρ s d') d' := by
  obtain ⟨hρ, hρe⟩ := h.isReducedOrdinary hκ₀ hadd
  obtain ⟨σ, hσ, hσJ, hσe, hρσ⟩ := h
  have hκσ := isReducedOrdinary_append_of_isRepAt hκ₀ hadd hσ hσJ
  have hstep := nfStep_congr hres hrig hρ hρσ s d'
  suffices H : X.IsRepAt cs a κ₀ J (X.nfStep cs a (κ₀ ++ σ) s d') d' by
    obtain ⟨σ₁, h1, h2, h3, h4⟩ := H
    exact ⟨σ₁, h1, h2, h3, hstep.trans h4⟩
  have hendκσ : galleryEnd a (κ₀ ++ σ) = d := by rw [galleryEnd_append, hσe]
  by_cases h1 : d' = d
  · rw [nfStep_of_eq (h1.trans hendκσ.symm)]
    exact ⟨σ, hσ, hσJ, hσe.trans h1.symm, .refl _⟩
  have hxJ : cs.wordProd (galleryType σ) ∈ cs.parabolic J := cs.wordProd_mem_parabolic hσJ
  have hsJ : cs.simple s ∈ cs.parabolic J := cs.simple_mem_parabolic hs
  have e1 : cs.length (cs.wordProd (galleryType (κ₀ ++ σ)) * cs.simple s) =
      cs.length (cs.wordProd (galleryType κ₀)) +
        cs.length (cs.wordProd (galleryType σ) * cs.simple s) := by
    rw [galleryType_append, cs.wordProd_append, mul_assoc, hadd _ (mul_mem hxJ hsJ)]
  have e2 : cs.length (cs.wordProd (galleryType (κ₀ ++ σ))) =
      cs.length (cs.wordProd (galleryType κ₀)) + cs.length (cs.wordProd (galleryType σ)) := by
    rw [galleryType_append, cs.wordProd_append, hadd _ hxJ]
  have hne : d' ≠ galleryEnd a (κ₀ ++ σ) := hendκσ ▸ h1
  rcases cs.length_mul_simple (cs.wordProd (galleryType σ)) s with h2 | h2
  ·
    rw [nfStep_of_lt hne (by rw [e1, e2, h2]; omega)]
    refine ⟨σ ++ [(s, d')], ⟨(isOrdinary_concat _ σ (s, d')).mpr ⟨hσ.1, hσe ▸ hd',
      hσe ▸ Ne.symm h1⟩, ?_⟩, ?_, by simp, by rw [List.append_assoc]⟩
    · rw [CoxeterSystem.IsReduced, galleryType_append, cs.wordProd_append]
      simp [h2, hσ.2.eq]
    · intro t ht
      simp only [galleryType_append, galleryType_cons, galleryType_nil, List.mem_append,
        List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact hσJ t ht
      · exact hs
  ·
    obtain ⟨ρ₁, z, h3, h4⟩ := nfStep_of_gt hres hκσ hne (by rw [e1, e2, ← h2]; omega)
    subst hJ
    obtain ⟨δ, hB, hadj⟩ := hres i j hij (galleryEnd a κ₀)
    have hb := X.self_mem_residue {i, j} (galleryEnd a κ₀)
    have hdist := dist_eq_of_isOrdinary hB hadj hb hσ.1 hσJ hσ.2
    rw [hσe] at hdist
    obtain ⟨β, hβ, hβJ, hβw⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic
      (mul_mem hxJ hsJ)
    have hβs : cs.IsReduced (β ++ [s]) := by
      rw [CoxeterSystem.IsReduced, cs.wordProd_append, hβw, cs.wordProd_singleton, mul_assoc,
        cs.simple_mul_simple_self, mul_one, List.length_append, List.length_singleton, ← hβ.eq,
        hβw]
      omega
    have hβsw : cs.wordProd (β ++ [s]) = δ (galleryEnd a κ₀) d := by
      rw [cs.wordProd_append, hβw, cs.wordProd_singleton, mul_assoc, cs.simple_mul_simple_self,
        mul_one, hdist]
    have hdR : d ∈ X.residue {i, j} (galleryEnd a κ₀) := by
      rw [← hσe]
      exact galleryEnd_mem_residue hσ.1.isGallery hσJ
    obtain ⟨τ, hτo, hτt, hτe⟩ := exists_isOrdinary_of_isBuildingOn hB hadj hb hdR hβs hβsw
    obtain ⟨σ₁, ⟨t, e⟩, rfl⟩ : ∃ σ₁ q, τ = σ₁ ++ [q] := by
      rcases List.eq_nil_or_concat' τ with h | h
      · subst h
        simp at hτt
      · exact h
    have ht : t = s := by
      rw [galleryType_append] at hτt
      simpa using (List.append_inj' hτt rfl).2
    subst ht
    rw [galleryEnd_concat] at hτe
    dsimp only at hτe
    subst hτe
    have hτJ : ∀ s' ∈ galleryType (σ₁ ++ [(t, e)]), s' ∈ ({i, j} : Set ι) := by
      rw [hτt]
      intro s' hs'
      rcases List.mem_append.mp hs' with hs' | hs'
      · exact hβJ s' hs'
      · rw [List.mem_singleton.mp hs']
        exact hs
    have hτ : X.IsReducedOrdinary cs (galleryEnd a κ₀) (σ₁ ++ [(t, e)]) := ⟨hτo, hτt ▸ hβs⟩
    have h5 : X.StrictHomotopic cs a (κ₀ ++ σ) (κ₀ ++ σ₁ ++ [(t, e)]) := by
      rw [List.append_assoc]
      exact strictHomotopic_of_isRepAt hres hij rfl
        ⟨σ, hσ, hσJ, hσe, .refl _⟩ ⟨σ₁ ++ [(t, e)], hτ, hτJ, by simp, .refl _⟩
    have h6 : X.StrictHomotopic cs a ρ₁ (κ₀ ++ σ₁) :=
      strictHomotopic_of_concat hres hrig (h3.isReducedOrdinary_iff.mp hκσ) (h3.symm.trans h5)
    have h7 : galleryEnd a ρ₁ = galleryEnd (galleryEnd a κ₀) σ₁ := by
      rw [h6.galleryEnd_eq, galleryEnd_append]
    obtain ⟨hσ₁o, hσ₁adj, hσ₁ne⟩ := (isOrdinary_concat _ σ₁ (t, e)).mp hτo
    have hσ₁J : ∀ s' ∈ galleryType σ₁, s' ∈ ({i, j} : Set ι) := fun s' hs' =>
      hτJ s' (by simp [galleryType_append, hs'])
    have hσ₁ : X.IsReducedOrdinary cs (galleryEnd a κ₀) σ₁ := hτ.of_append_left
    rcases h4 with ⟨h8, h9⟩ | ⟨h8, h9⟩
    · rw [h9]
      exact ⟨σ₁, hσ₁, hσ₁J, h7 ▸ h8.symm, h6⟩
    · rw [h9]
      refine ⟨σ₁ ++ [(t, d')], ⟨(isOrdinary_concat _ σ₁ (t, d')).mpr ⟨hσ₁o,
        adj_trans hσ₁adj hd', h7 ▸ Ne.symm h8⟩, ?_⟩, ?_, by simp, ?_⟩
      · have := hτ.2
        simpa [galleryType_append] using this
      · intro s' hs'
        simp only [galleryType_append, galleryType_cons, galleryType_nil, List.mem_append,
          List.mem_singleton] at hs'
        rcases hs' with hs' | rfl
        · exact hσ₁J s' hs'
        · exact hs
      · rw [← List.append_assoc]
        exact h6.append_right _

theorem IsRepAt.foldl_nfStep (hJ : J = {i, j}) {ρ : List (ι × C)} {d : C}
    (h : X.IsRepAt cs a κ₀ J ρ d) {η : List (ι × C)} (hη : X.IsGallery d η)
    (hηJ : ∀ s ∈ galleryType η, s ∈ J) :
    X.IsRepAt cs a κ₀ J (η.foldl (fun ρ p => X.nfStep cs a ρ p.1 p.2) ρ) (galleryEnd d η) := by
  induction η generalizing ρ d with
  | nil => exact h
  | cons p η ih =>
    obtain ⟨h1, h2⟩ := hη
    exact ih (h.nfStep hres hrig hκ₀ hadd hij hJ (hηJ p.1 (by simp)) h1) h2
      fun s hs => hηJ s (by simp [hs])

end Residue

omit hrig in
theorem exists_coset_split {κ : List (ι × C)} (hκ : X.IsReducedOrdinary cs a κ) (J : Set ι) :
    ∃ κ₀ κ₁ : List (ι × C), X.StrictHomotopic cs a κ (κ₀ ++ κ₁) ∧
      X.IsReducedOrdinary cs a (κ₀ ++ κ₁) ∧ (∀ s ∈ galleryType κ₁, s ∈ J) ∧
      ∀ v ∈ cs.parabolic J, cs.length (cs.wordProd (galleryType κ₀) * v) =
        cs.length (cs.wordProd (galleryType κ₀)) + cs.length v := by
  obtain ⟨⟨u, v⟩, ⟨hu, hv, hw⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul J
    (cs.wordProd (galleryType κ))
  dsimp only at hu hv hw
  obtain ⟨ωu, hωu, hωuw⟩ := cs.exists_isReduced u
  obtain ⟨ωv, hωv, hωvJ, hωvw⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hv
  have hω : cs.IsReduced (ωu ++ ωv) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, ← hωuw, hωvw,
      cs.length_mul_of_isMinimalCosetRep hu hv, List.length_append, ← hωu.eq, ← hωv.eq, ← hωuw,
      hωvw]
  obtain ⟨κ', h1, h2, h3⟩ := exists_strictHomotopic_of_isReduced hres hκ hω
    (by rw [cs.wordProd_append, ← hωuw, hωvw, hw])
  obtain ⟨κ₀, κ₁, rfl, h4, h5⟩ := exists_split_of_galleryType_eq_append h3
  refine ⟨κ₀, κ₁, h1, h2, by rw [h5]; exact hωvJ, fun x hx => ?_⟩
  rw [h4, ← hωuw]
  exact cs.length_mul_of_isMinimalCosetRep hu hx

omit hres hrig in
theorem exists_pair_of_encard_le_two [Nontrivial ι] {J : Set ι} (hJ : J.encard ≤ 2) :
    ∃ i j : ι, i ≠ j ∧ J ⊆ {i, j} := by
  obtain ⟨i₀, j₀, h₀⟩ := exists_pair_ne ι
  have h2 : (2 : ℕ∞) ≤ (Set.univ : Set ι).encard := by
    rw [← Set.encard_pair h₀]
    exact Set.encard_le_encard (Set.subset_univ _)
  obtain ⟨K, hJK, -, hK⟩ := Set.exists_superset_subset_encard_eq (Set.subset_univ J) hJ h2
  obtain ⟨i, j, hij, rfl⟩ := Set.encard_eq_two.mp hK
  exact ⟨i, j, hij, hJK⟩

theorem normalForm_elemMove [Nontrivial ι] {γ γ' : List (ι × C)} (hγ : X.IsGallery a γ)
    (h : X.ElemMove a γ γ') :
    X.StrictHomotopic cs a (X.normalForm cs a γ) (X.normalForm cs a γ') := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  obtain ⟨i, j, hij, hJij⟩ := exists_pair_of_encard_le_two hJ
  rw [List.append_assoc] at hγ
  have hγ₁ := hγ.of_append_left
  obtain ⟨hκ, hκe⟩ := normalForm_spec hres hγ₁
  obtain ⟨κ₀, κ₁, h1, h2, h3, h4⟩ := exists_coset_split hres hκ {i, j}
  have hκ₀ := h2.of_append_left
  have hrep : X.IsRepAt cs a κ₀ {i, j} (X.normalForm cs a γ₁) (galleryEnd a γ₁) :=
    ⟨κ₁, h2.of_append_right, h3, by rw [← galleryEnd_append, ← h1.galleryEnd_eq, hκe], h1⟩
  have hrη := hrep.foldl_nfStep hres hrig hκ₀ h4 hij rfl hη fun s hs => hJij (hηJ s hs)
  have hrη' := hrep.foldl_nfStep hres hrig hκ₀ h4 hij rfl hη' fun s hs => hJij (hη'J s hs)
  rw [← hend] at hrη'
  have h5 := strictHomotopic_of_isRepAt hres hij rfl hrη hrη'
  have h6 := (hγ.of_append_right).of_append_right
  rw [List.append_assoc, List.append_assoc, normalForm_append, normalForm_append, List.foldl_append,
    List.foldl_append]
  refine foldl_nfStep_congr hres hrig (hrη.isReducedOrdinary hκ₀ h4).1 h5 ?_
  rw [(hrη.isReducedOrdinary hκ₀ h4).2]
  simpa [galleryEnd_append] using h6

theorem strictHomotopic_of_twoHomotopic [Nontrivial ι] {ρ ρ' : List (ι × C)}
    (hρ : X.IsReducedOrdinary cs a ρ) (hρ' : X.IsReducedOrdinary cs a ρ')
    (h : X.TwoHomotopic a ρ ρ') : X.StrictHomotopic cs a ρ ρ' := by
  have key : ∀ γ γ', Relation.ReflTransGen (X.ElemMove a) γ γ' → X.IsGallery a γ →
      X.StrictHomotopic cs a (X.normalForm cs a γ) (X.normalForm cs a γ') := by
    intro γ γ' hγγ' hγ
    induction hγγ' with
    | refl => rfl
    | tail h12 h23 ih =>
      exact ih.trans (normalForm_elemMove hres hrig
        ((TwoHomotopic.iff_reflTransGen.mpr h12).isGallery_iff.mp hγ) h23)
  have h1 := key ρ ρ' (TwoHomotopic.iff_reflTransGen.mp h) hρ.1.isGallery
  exact ((normalForm_strictHomotopic hres hrig hρ).symm.trans h1).trans
    (normalForm_strictHomotopic hres hrig hρ')

omit hres hrig

variable (X cs) in
@[expose] def strictSetoid (a : C) : Setoid {γ : List (ι × C) // X.IsReducedOrdinary cs a γ} where
  r γ γ' := X.StrictHomotopic cs a γ.1 γ'.1
  iseqv := ⟨fun γ => .refl γ.1, fun h => h.symm, fun h h' => h.trans h'⟩

variable (X cs) in
@[expose] noncomputable def strictClassToCover (a : C) :
    Quotient (X.strictSetoid cs a) → X.Cover a :=
  Quotient.lift (fun γ => X.cls a γ.1) fun _ _ h => cls_congr (StrictHomotopic.twoHomotopic h)

theorem strictClassToCover_mk (a : C) (γ : {γ : List (ι × C) // X.IsReducedOrdinary cs a γ}) :
    X.strictClassToCover cs a (Quotient.mk _ γ) = X.cls a γ.1 :=
  rfl

theorem exists_twoHomotopic_isReducedOrdinary (hres : ∀ s t : ι, s ≠ t → ∀ y : C,
      X.IsResidueBuilding cs {s, t} y) {γ : List (ι × C)} (hγ : X.IsGallery a γ) :
    ∃ ρ, X.IsReducedOrdinary cs a ρ ∧ X.TwoHomotopic a γ ρ := by
  obtain ⟨γ₁, h1, -, h3⟩ := exists_isOrdinary_of_isGallery hγ
  obtain ⟨γ₂, h4, h5⟩ := exists_reduction hres h1
  exact ⟨γ₂, h4, (TwoHomotopic.iff_reflTransGen.mpr
    (Relation.ReflTransGen.mono (fun _ _ h => ConstantDeletion.elemMove h) _ _ h3)).trans
    (reflTransGen_reductionStep_twoHomotopic h5)⟩

theorem bijective_strictClassToCover [Nontrivial ι]
    (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
    (hrig : ∀ γ γ' : List (ι × C), X.IsReducedOrdinary cs a γ → X.StrictHomotopic cs a γ γ' →
      galleryType γ = galleryType γ' → γ = γ') :
    Function.Bijective (X.strictClassToCover cs a) := by
  refine ⟨fun A B hAB => ?_, fun A => ?_⟩
  · induction A using Quotient.inductionOn with
    | h ρ =>
    induction B using Quotient.inductionOn with
    | h ρ' =>
    rw [strictClassToCover_mk, strictClassToCover_mk,
      cls_eq_iff ρ.2.1.isGallery ρ'.2.1.isGallery] at hAB
    exact Quotient.sound (strictHomotopic_of_twoHomotopic hres hrig ρ.2 ρ'.2 hAB)
  · obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls A
    obtain ⟨ρ, hρ, h⟩ := exists_twoHomotopic_isReducedOrdinary hres hγ
    exact ⟨Quotient.mk _ ⟨ρ, hρ⟩, (cls_congr h).symm⟩

end ChamberSystem

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ChamberSystem

theorem F4_strict_gallery_normal_form_cover
    {C : Type*} (X : ChamberSystem (Fin Tag.F4.rank) C)
    (hres : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 2 → ∀ x,
      X.IsResidueBuilding (coxeterSystem .F4) J x) (a : C)
    (hrig : ∀ γ γ' : List (Fin Tag.F4.rank × C), X.IsReducedOrdinary (coxeterSystem .F4) a γ →
      X.IsReducedOrdinary (coxeterSystem .F4) a γ' →
      X.StrictHomotopic (coxeterSystem .F4) a γ γ' → galleryType γ = galleryType γ' → γ = γ') :
    (∀ ρ ρ' : List (Fin Tag.F4.rank × C), X.IsReducedOrdinary (coxeterSystem .F4) a ρ →
      X.IsReducedOrdinary (coxeterSystem .F4) a ρ' → X.TwoHomotopic a ρ ρ' →
        X.StrictHomotopic (coxeterSystem .F4) a ρ ρ') ∧
    Function.Bijective (X.strictClassToCover (coxeterSystem .F4) a) := by
  have : Nontrivial (Fin Tag.F4.rank) := Fin.nontrivial_iff_two_le.mpr (by decide)
  have hres' : ∀ s t : Fin Tag.F4.rank, s ≠ t → ∀ y : C,
      X.IsResidueBuilding (coxeterSystem .F4) {s, t} y := fun s t hst y =>
    hres {s, t} (Set.ncard_pair hst) y
  have hrig' : ∀ γ γ' : List (Fin Tag.F4.rank × C),
      X.IsReducedOrdinary (coxeterSystem .F4) a γ →
      X.StrictHomotopic (coxeterSystem .F4) a γ γ' → galleryType γ = galleryType γ' → γ = γ' :=
    fun γ γ' hγ h ht => hrig γ γ' hγ (h.isReducedOrdinary_iff.mp hγ) h ht
  exact ⟨fun ρ ρ' hρ hρ' h => strictHomotopic_of_twoHomotopic hres' hrig' hρ hρ' h,
    bijective_strictClassToCover hres' hrig'⟩

end CFSG.Monster.B.Geometry
