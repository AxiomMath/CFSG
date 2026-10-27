module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoMoves
import CFSG.LocalAnalysis.StandardType.GGQ2SignedPermMem

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {t : ℕ}

theorem coe_swapEquiv (i j : Fin t) :
    ⇑(swapEquiv t i j) = ChoiceTwo.moveExp (Equiv.swap i j) fun _ => false := by
  funext u k
  simp [swapEquiv, ChoiceTwo.moveExp_apply, ChoiceTwo.sgnZ,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

theorem coe_negEquiv (i : Fin t) :
    ⇑(negEquiv t i) = ChoiceTwo.moveExp 1 fun k => decide (k = i) := by
  funext u k
  simp only [negEquiv, LinearEquiv.piCongrRight_apply, ChoiceTwo.moveExp_apply,
    ChoiceTwo.sgnZ]
  by_cases h : k = i <;> simp [h]

theorem coe_negEquiv_mul_negEquiv {i j : Fin t} (hij : i ≠ j) :
    ⇑(negEquiv t i * negEquiv t j) = ChoiceTwo.moveExp 1 fun k => decide (k = i ∨ k = j) := by
  funext u k
  rw [LinearEquiv.mul_apply]
  simp only [negEquiv, LinearEquiv.piCongrRight_apply, ChoiceTwo.moveExp_apply,
    ChoiceTwo.sgnZ]
  by_cases hki : k = i
  · rw [hki]
    simp [hij]
  · by_cases hkj : k = j
    · rw [hkj] at hki ⊢
      simp [hki]
    · simp [hki, hkj]

theorem card_filter_decide_eq_or_eq {i j : Fin t} (hij : i ≠ j) :
    (Finset.univ.filter fun k => decide (k = i ∨ k = j) = true).card = 2 := by
  have h : (Finset.univ.filter fun k => decide (k = i ∨ k = j) = true) = {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, decide_eq_true_eq]
  rw [h, Finset.card_pair hij]

theorem moveExp_single_eq_single_iff (π : Equiv.Perm (Fin t)) (η : Fin t → Bool) (j : Fin t) :
    ChoiceTwo.moveExp π η (Pi.single j 1) = Pi.single j 1 ↔ π j = j ∧ η j = false := by
  constructor
  · intro h
    have h1 := congrFun h j
    simp only [ChoiceTwo.moveExp_apply, Pi.single_eq_same] at h1
    by_cases hπ : π j = j
    · by_cases hη : η j
      · simp [hπ, hη, ChoiceTwo.sgnZ] at h1
        exfalso
        exact (by decide : (-1 : F) ≠ 1) h1
      · exact ⟨hπ, by cases hj : η j <;> simp_all⟩
    · simp [hπ, ChoiceTwo.sgnZ_zero] at h1
  · rintro ⟨hπ, hη⟩
    funext k
    by_cases hk : k = j
    · subst hk
      simp [ChoiceTwo.moveExp_apply, ChoiceTwo.sgnZ, hπ, hη]
    · have hπk : π k ≠ j := fun h' => hk (π.injective (h'.trans hπ.symm))
      simp [ChoiceTwo.moveExp_apply, hk, hπk, ChoiceTwo.sgnZ_zero]

theorem mem_signedPermGroupOn_of_coe_eq_moveExp (S : Finset (Fin t)) {φ : V t ≃ₗ[F] V t}
    {π : Equiv.Perm (Fin t)} {η : Fin t → Bool} (hφ : ⇑φ = ChoiceTwo.moveExp π η)
    (hπ : ∀ i ∉ S, π i = i) (hη : ∀ i ∉ S, η i = false) : φ ∈ signedPermGroupOn t S := by
  classical
  set ε : Fin t → F := fun i => if η (π.symm i) then (-1 : F) else 1 with hεdef
  have hπ' : ∀ i ∉ S, π.symm i = i := by
    intro i hi
    calc π.symm i = π.symm (π i) := by rw [hπ i hi]
      _ = i := Equiv.symm_apply_apply π i
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    rw [hεdef]
    by_cases h : η (π.symm i) <;> simp [h]
  have hεS : ∀ i ∉ S, ε i = 1 := by
    intro i hi
    rw [hεdef]
    simp [hπ' i hi, hη i hi]
  refine mem_signedPermGroupOn_of_apply S φ π.symm ε hε hπ' hεS ?_
  intro u i
  rw [hφ]
  simp only [ChoiceTwo.moveExp_apply, Equiv.apply_symm_apply, hεdef]
  by_cases h : η (π.symm i) <;> simp [h, ChoiceTwo.sgnZ]

private theorem pme_funCongrLeft_mem_evenSignedPermGroupOn {t : ℕ} (S : Finset (Fin t))
    (σ : Equiv.Perm (Fin t)) (hσ : ∀ i ∉ S, σ i = i) :
    LinearEquiv.funCongrLeft F F σ ∈ evenSignedPermGroupOn t S := by
  classical
  have hσsupp : ∀ x, σ x ≠ x → x ∈ S := by
    intro x hx
    by_contra h
    exact hx (hσ x h)
  have hσinv : ∀ x, σ x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · intro hxS
      by_contra h
      have h1 : σ x = x := hσ x h
      exact h (by rwa [h1] at hxS)
    · intro hx
      by_contra h
      have h1 : σ (σ x) = σ x := hσ (σ x) h
      have h2 : σ x = x := σ.injective h1
      exact h (by rwa [← h2] at hx)
  have hσ' : σ = Equiv.Perm.ofSubtype (σ.subtypePerm hσinv) :=
    (Equiv.Perm.ofSubtype_subtypePerm hσinv hσsupp).symm
  rw [hσ']
  refine Equiv.Perm.swap_induction_on (σ.subtypePerm hσinv) ?_ ?_
  · rw [map_one]
    have h1 : LinearEquiv.funCongrLeft F F (1 : Equiv.Perm (Fin t)) = 1 := rfl
    rw [h1]
    exact Subgroup.one_mem _
  · intro f x y hxy ih
    have hswap : LinearEquiv.funCongrLeft F F
        (Equiv.Perm.ofSubtype (Equiv.swap x y)) ∈ evenSignedPermGroupOn t S := by
      rw [Equiv.Perm.ofSubtype_swap_eq]
      exact Subgroup.subset_closure (Or.inl ⟨x.1, x.2, y.1, y.2, rfl⟩)
    rw [map_mul]
    change LinearEquiv.funCongrLeft F F (Equiv.Perm.ofSubtype f) *
      LinearEquiv.funCongrLeft F F (Equiv.Perm.ofSubtype (Equiv.swap x y)) ∈
      evenSignedPermGroupOn t S
    exact mul_mem ih hswap

private theorem pme_orientEquiv_pair {t : ℕ} (a b : Fin t) (A : Finset (Fin t))
    (ha : a ∉ insert b A) (hb : b ∉ A) :
    orientEquiv t (fun j => if j ∈ insert a (insert b A) then (-1 : F) else 1) =
      negEquiv t a *
        (negEquiv t b * orientEquiv t (fun j => if j ∈ A then (-1 : F) else 1)) := by
  ext u k
  simp only [negEquiv, orientEquiv, LinearEquiv.piCongrRight_apply, LinearEquiv.mul_apply]
  by_cases hka : k = a
  · rw [hka]
    have hab : a ≠ b := fun h => ha (by rw [h]; exact Finset.mem_insert_self b A)
    have hkA : a ∉ A := fun h => ha (Finset.mem_insert_of_mem h)
    have hne1 : (1 : F) ≠ -1 := by decide
    simp [hab, hkA, hne1, LinearEquiv.neg_apply, LinearEquiv.refl_apply]
  · by_cases hkb : k = b
    · rw [hkb] at hka ⊢
      have hne1 : (1 : F) ≠ -1 := by decide
      simp [hka, hb, hne1, LinearEquiv.neg_apply, LinearEquiv.refl_apply]
    · have hne1 : (1 : F) ≠ -1 := by decide
      have hk : k ∈ insert a (insert b A) ↔ k ∈ A := by
        simp [hka, hkb]
      simp [hka, hkb, hk, hne1, LinearEquiv.refl_apply]

private theorem pme_orientEquiv_mem_evenSignedPermGroupOn {t : ℕ} (S : Finset (Fin t))
    (A : Finset (Fin t)) (hA : A ⊆ S) (hev : Even A.card) :
    orientEquiv t (fun j => if j ∈ A then (-1 : F) else 1) ∈ evenSignedPermGroupOn t S := by
  classical
  revert hA hev
  refine Finset.strongInductionOn A ?_
  intro A ih hA hev
  by_cases hA0 : A = ∅
  · subst hA0
    have h1 : orientEquiv t (fun j => if j ∈ (∅ : Finset (Fin t)) then (-1 : F) else 1) =
        1 := by
      ext u k
      simp [orientEquiv]
      rw [if_neg (by decide : (1 : F) ≠ -1)]
      rfl
    rw [h1]
    exact Subgroup.one_mem _
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hA0
    have hposA : 0 < A.card := Finset.card_pos.mpr ⟨a, ha⟩
    have hcard : (A.erase a).card = A.card - 1 := Finset.card_erase_of_mem ha
    have hpos : 0 < (A.erase a).card := by
      rw [hcard]
      obtain ⟨m, hm⟩ := hev
      omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    have hbA : b ∈ A := Finset.mem_of_mem_erase hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    set A' : Finset (Fin t) := (A.erase a).erase b with hA'def
    have hA'eq : insert a (insert b A') = A := by
      rw [hA'def, Finset.insert_erase hb, Finset.insert_erase ha]
    have hA'sub : A' ⊆ S := fun x hx =>
      hA (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    have hsubA' : A' ⊆ A := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have haA' : a ∉ A' := by rw [hA'def]; simp
    have hbA' : b ∉ A' := by rw [hA'def]; simp
    have hA'lt : A' ⊂ A :=
      (Finset.ssubset_iff_of_subset hsubA').mpr ⟨a, ha, haA'⟩
    have ha' : a ∉ insert b A' := by
      intro h
      rcases Finset.mem_insert.mp h with hab | hA''
      · exact hba hab.symm
      · exact haA' hA''
    have hA'ev : Even A'.card := by
      obtain ⟨m, hm⟩ := hev
      have hstep : A'.card + 2 = A.card := by
        have h1 : A'.card = (A.erase a).card - 1 := by
          rw [hA'def]
          exact Finset.card_erase_of_mem hb
        omega
      refine ⟨m - 1, ?_⟩
      omega
    rw [← hA'eq]
    rw [pme_orientEquiv_pair a b A' ha' hbA', ← mul_assoc]
    exact mul_mem (Subgroup.subset_closure (Or.inr ⟨a, hA ha, b, hA hbA, hba.symm, rfl⟩))
      (ih A' hA'lt hA'sub hA'ev)

theorem mem_evenSignedPermGroupOn_of_coe_eq_moveExp (S : Finset (Fin t)) {φ : V t ≃ₗ[F] V t}
    {π : Equiv.Perm (Fin t)} {η : Fin t → Bool} (hφ : ⇑φ = ChoiceTwo.moveExp π η)
    (hπ : ∀ i ∉ S, π i = i) (hη : ∀ i ∉ S, η i = false)
    (hev : Even (Finset.univ.filter fun i => η i = true).card) :
    φ ∈ evenSignedPermGroupOn t S := by
  classical
  set ε : Fin t → F := fun i => if η i then (-1 : F) else 1 with hεdef
  set A : Finset (Fin t) := Finset.univ.filter (fun i => η i = true) with hAdef
  have hεfun : ε = fun j => if j ∈ A then (-1 : F) else 1 := by
    funext j
    rw [hεdef, hAdef]
    by_cases h : η j = true
    · simp [h]
    · have h' : η j = false := by cases hj : η j <;> simp_all
      simp [h']
  have hAS : A ⊆ S := by
    intro i hi
    by_contra h
    have h1 : η i = false := hη i h
    have h2 : η i = true := (Finset.mem_filter.mp hi).2
    rw [h1] at h2
    exact Bool.false_ne_true h2
  have hAev : Even A.card := by simpa [hAdef] using hev
  have hne1 : (1 : F) ≠ -1 := by decide
  have hφeq : φ = orientEquiv t ε * LinearEquiv.funCongrLeft F F π := by
    ext u i
    rw [hφ]
    simp only [ChoiceTwo.moveExp_apply, hεdef, ChoiceTwo.sgnZ, LinearEquiv.mul_apply,
      orientEquiv, LinearEquiv.piCongrRight_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply]
    by_cases h : η i <;> simp [h, hne1]
  rw [hφeq, hεfun]
  exact mul_mem (pme_orientEquiv_mem_evenSignedPermGroupOn S A hAS hAev)
    (pme_funCongrLeft_mem_evenSignedPermGroupOn S π hπ)

theorem mem_signedPermGroup_of_coe_eq_moveExp {φ : V t ≃ₗ[F] V t} {π : Equiv.Perm (Fin t)}
    {η : Fin t → Bool} (hφ : ⇑φ = ChoiceTwo.moveExp π η) : φ ∈ signedPermGroup t := by
  rw [← signedPermGroupOn_univ t]
  exact mem_signedPermGroupOn_of_coe_eq_moveExp Finset.univ hφ
    (fun i hi => absurd (Finset.mem_univ i) hi) (fun i hi => absurd (Finset.mem_univ i) hi)

theorem mem_evenSignedPermGroup_of_coe_eq_moveExp {φ : V t ≃ₗ[F] V t} {π : Equiv.Perm (Fin t)}
    {η : Fin t → Bool} (hφ : ⇑φ = ChoiceTwo.moveExp π η)
    (hev : Even (Finset.univ.filter fun i => η i = true).card) :
    φ ∈ evenSignedPermGroup t := by
  have huniv : evenSignedPermGroupOn t Finset.univ = evenSignedPermGroup t := by
    rw [evenSignedPermGroupOn, evenSignedPermGroup]
    congr 1
    ext T
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_univ, true_and]
  rw [← huniv]
  exact mem_evenSignedPermGroupOn_of_coe_eq_moveExp Finset.univ hφ
    (fun i hi => absurd (Finset.mem_univ i) hi) (fun i hi => absurd (Finset.mem_univ i) hi) hev

theorem mem_ambientNormalizer_orthogonal_of_coe_eq_moveExp (δ : Fin 2) {φ : V t ≃ₗ[F] V t}
    {π : Equiv.Perm (Fin t)} {η : Fin t → Bool} (hφ : ⇑φ = ChoiceTwo.moveExp π η)
    (hpar : δ.val = 0 → Even (Finset.univ.filter fun i => η i = true).card) :
    φ ∈ ambientNormalizer (.orthogonal δ) t := by
  rw [ambientNormalizer]
  by_cases h : δ.val = 0
  · rw [if_pos h]
    exact mem_evenSignedPermGroup_of_coe_eq_moveExp hφ (hpar h)
  · rw [if_neg h]
    exact mem_signedPermGroup_of_coe_eq_moveExp hφ

theorem mem_normalizerOf_orthogonal_zero_of_coe_eq_moveExp (δ : Fin 2) (S : Finset (Fin t))
    {φ : V t ≃ₗ[F] V t} {π : Equiv.Perm (Fin t)} {η : Fin t → Bool}
    (hφ : ⇑φ = ChoiceTwo.moveExp π η) (hπ : ∀ i ∉ S, π i = i) (hη : ∀ i ∉ S, η i = false)
    (hpar : δ.val = 0 → Even (Finset.univ.filter fun i => η i = true).card) :
    φ ∈ normalizerOf (.orthogonal δ) t (.zero S) := by
  rw [normalizerOf]
  by_cases h : δ.val = 0
  · rw [if_pos h]
    exact mem_evenSignedPermGroupOn_of_coe_eq_moveExp S hφ hπ hη (hpar h)
  · rw [if_neg h]
    exact mem_signedPermGroupOn_of_coe_eq_moveExp S hφ hπ hη

end CFSG.StandardType.GGQ2Frame.PlaneRaw
