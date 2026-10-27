module

public import CFSG.Monster.B.GSide.NativeCompletionCore
public import CFSG.Monster.B.Recog.GenericTrianglePresentation

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

section Triangle

variable {v w u : CVert}

open _root_.Classical in
@[expose] noncomputable def triIdx (v w x : CVert) : Fin 3 :=
  if x = v then 0 else if x = w then 1 else 2

@[expose] def triPt (v w u : CVert) : Fin 3 → CVert := ![v, w, u]

theorem triPt_triIdx {x : CVert} (hx : x ∈ ({v, w, u} : Set CVert)) :
    triPt v w u (triIdx v w x) = x := by
  unfold triIdx triPt
  rcases hx with rfl | rfl | rfl
  · simp
  · by_cases h : x = v
    · subst h; simp
    · simp [h]
  · by_cases h : x = v
    · subst h; simp
    · by_cases h' : x = w
      · subst h'; simp [h]
      · simp [h, h']

theorem triIdx_triPt (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) (i : Fin 3) :
    triIdx v w (triPt v w u i) = i := by
  unfold triIdx triPt
  fin_cases i
  · simp
  · simp [hvw.symm]
  · simp [hvu.symm, hwu.symm]

theorem triPt_mem (i : Fin 3) : triPt v w u i ∈ ({v, w, u} : Set CVert) := by
  unfold triPt
  fin_cases i
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

theorem cvMul_mem_tri {g : Shat} (hg : g ∈ cvSetStab {v, w, u}) {x : CVert}
    (hx : x ∈ ({v, w, u} : Set CVert)) : cvMul x g ∈ ({v, w, u} : Set CVert) :=
  (mem_cvSetStab.1 hg x).2 hx

@[expose] noncomputable def triChi (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) :
    cvSetStab {v, w, u} →* Equiv.Perm (Fin 3) where
  toFun g :=
    { toFun := fun i => triIdx v w (cvMul (triPt v w u i) (g : Shat)⁻¹)
      invFun := fun i => triIdx v w (cvMul (triPt v w u i) g)
      left_inv := fun i => by
        simp only
        rw [triPt_triIdx (cvMul_mem_tri (inv_mem g.2) (triPt_mem i)), cvMul_inv_cancel',
          triIdx_triPt hvw hvu hwu]
      right_inv := fun i => by
        simp only
        rw [triPt_triIdx (cvMul_mem_tri g.2 (triPt_mem i)), cvMul_inv_cancel,
          triIdx_triPt hvw hvu hwu] }
  map_one' := Equiv.ext fun i => by
    simp only [OneMemClass.coe_one, inv_one, cvMul_one, Equiv.coe_fn_mk, Equiv.Perm.one_apply]
    exact triIdx_triPt hvw hvu hwu i
  map_mul' g h := Equiv.ext fun i => by
    simp only [Subgroup.coe_mul, mul_inv_rev, cvMul_mul, Equiv.coe_fn_mk, Equiv.Perm.mul_apply]
    rw [triPt_triIdx (cvMul_mem_tri (inv_mem h.2) (triPt_mem i))]

theorem triIdx_eq_iff (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) {x : CVert}
    (hx : x ∈ ({v, w, u} : Set CVert)) (i : Fin 3) : triIdx v w x = i ↔ x = triPt v w u i := by
  constructor
  · rintro rfl
    exact (triPt_triIdx hx).symm
  · rintro rfl
    exact triIdx_triPt hvw hvu hwu i

theorem triChi_apply (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) (g : cvSetStab {v, w, u})
    (i : Fin 3) : triChi hvw hvu hwu g i = triIdx v w (cvMul (triPt v w u i) (g : Shat)⁻¹) :=
  rfl

theorem triChi_eq_iff (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) (g : cvSetStab {v, w, u})
    (i j : Fin 3) :
    triChi hvw hvu hwu g i = j ↔ cvMul (triPt v w u j) (g : Shat) = triPt v w u i := by
  rw [triChi_apply, triIdx_eq_iff hvw hvu hwu (cvMul_mem_tri (inv_mem g.2) (triPt_mem i))]
  constructor
  · intro h
    rw [← h, cvMul_inv_cancel']
  · intro h
    rw [← h, cvMul_inv_cancel]

theorem mem_cvSetStab_pair_iff_of_mem (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) {g : Shat}
    (hg : g ∈ cvSetStab {v, w, u}) : g ∈ cvSetStab {v, w} ↔ cvMul u g = u := by
  have hT : ∀ x, cvMul x g ∈ ({v, w, u} : Set CVert) ↔ x ∈ ({v, w, u} : Set CVert) :=
    mem_cvSetStab.1 hg
  constructor
  · intro h
    have hu := (hT u).2 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    rcases hu with hu | hu | hu
    · exact absurd ((mem_cvSetStab.1 h u).1 (hu ▸ Set.mem_insert _ _)) (by
        rintro (h' | h')
        · exact hvu h'.symm
        · exact hwu h'.symm)
    · exact absurd ((mem_cvSetStab.1 h u).1 (hu ▸ Set.mem_insert_of_mem _ rfl)) (by
        rintro (h' | h')
        · exact hvu h'.symm
        · exact hwu h'.symm)
    · exact hu
  · intro hu
    refine mem_cvSetStab.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hxT := (hT x).1 (by
        rcases hx with hx | hx
        · exact hx ▸ Set.mem_insert _ _
        · exact hx ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      rcases hxT with rfl | rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
      · exfalso
        rw [hu] at hx
        rcases hx with h' | h'
        · exact hvu h'.symm
        · exact hwu h'.symm
    · have hxT := (hT x).2 (by
        rcases hx with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      rcases hxT with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exfalso
        have := cvMul_injective g (h'.trans hu.symm)
        rcases hx with rfl | rfl
        · exact hvu this
        · exact hwu this

theorem exists_unique_extend_cvTriangle
    (h : IsCTriangle v w u) {Y : Type*} [Group Y]
    (f₁ : ↥(cvSetStab {v, w, u} ⊓ vStab v) →* Y)
    (f₂ : ↥(cvSetStab {v, w, u} ⊓ cvSetStab {v, w}) →* Y)
    (hf : ∀ k (h₁ : k ∈ cvSetStab {v, w, u} ⊓ vStab v)
      (h₂ : k ∈ cvSetStab {v, w, u} ⊓ cvSetStab {v, w}), f₁ ⟨k, h₁⟩ = f₂ ⟨k, h₂⟩)
    {a b : Shat} (ha : cvMul v a = v ∧ cvMul w a = u ∧ cvMul u a = w)
    (hb : cvMul v b = w ∧ cvMul w b = v ∧ cvMul u b = u)
    (hrel : ∀ h₁ h₂ h₃, (f₁ ⟨a, h₁⟩ * f₂ ⟨b, h₂⟩) ^ 3 = f₁ ⟨(a * b) ^ 3, h₃⟩) :
    ∃! f : ↥(cvSetStab {v, w, u}) →* Y,
      (∀ x (hx : x ∈ cvSetStab {v, w, u}) (h₁ : x ∈ cvSetStab {v, w, u} ⊓ vStab v),
        f ⟨x, hx⟩ = f₁ ⟨x, h₁⟩) ∧
      (∀ x (hx : x ∈ cvSetStab {v, w, u}) (h₂ : x ∈ cvSetStab {v, w, u} ⊓ cvSetStab {v, w}),
        f ⟨x, hx⟩ = f₂ ⟨x, h₂⟩) := by
  obtain ⟨hvw', hvu', hwu'⟩ := h
  have hvw := hvw'.ne
  have hvu := hvu'.ne
  have hwu := hwu'.ne
  let χ := triChi hvw hvu hwu
  have hmemT : ∀ x, x = v ∨ x = w ∨ x = u → x ∈ ({v, w, u} : Set CVert) := fun x hx => hx
  have haB : a ∈ cvSetStab {v, w, u} := mem_cvSetStab_triple
    ⟨by rw [ha.1]; exact hmemT v (Or.inl rfl), by rw [ha.2.1]; exact hmemT u (Or.inr (Or.inr rfl)),
      by rw [ha.2.2]; exact hmemT w (Or.inr (Or.inl rfl))⟩
    (by
      rintro y (rfl | rfl | rfl)
      · exact ⟨y, hmemT y (Or.inl rfl), ha.1⟩
      · exact ⟨u, hmemT u (Or.inr (Or.inr rfl)), ha.2.2⟩
      · exact ⟨w, hmemT w (Or.inr (Or.inl rfl)), ha.2.1⟩)
  have hbB : b ∈ cvSetStab {v, w, u} := mem_cvSetStab_triple
    ⟨by rw [hb.1]; exact hmemT w (Or.inr (Or.inl rfl)), by rw [hb.2.1]; exact hmemT v (Or.inl rfl),
      by rw [hb.2.2]; exact hmemT u (Or.inr (Or.inr rfl))⟩
    (by
      rintro y (rfl | rfl | rfl)
      · exact ⟨w, hmemT w (Or.inr (Or.inl rfl)), hb.2.1⟩
      · exact ⟨v, hmemT v (Or.inl rfl), hb.1⟩
      · exact ⟨y, hmemT y (Or.inr (Or.inr rfl)), hb.2.2⟩)
  let A₁ : Subgroup (cvSetStab {v, w, u}) :=
    (cvSetStab {v, w, u} ⊓ vStab v).subgroupOf (cvSetStab {v, w, u})
  let A₂ : Subgroup (cvSetStab {v, w, u}) :=
    (cvSetStab {v, w, u} ⊓ cvSetStab {v, w}).subgroupOf (cvSetStab {v, w, u})
  have hA₁ : ∀ x : cvSetStab {v, w, u}, x ∈ A₁ ↔ χ x 0 = 0 := fun x => by
    rw [triChi_eq_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_vStab]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hA₂ : ∀ x : cvSetStab {v, w, u}, x ∈ A₂ ↔ χ x 2 = 2 := fun x => by
    rw [triChi_eq_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_cvSetStab_pair_iff_of_mem hvw hvu hwu x.2]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hχa : χ ⟨a, haB⟩ = Equiv.swap 1 2 := by
    refine Equiv.ext fun i => ?_
    fin_cases i
    · rw [triChi_eq_iff]
      exact ha.1
    · rw [triChi_eq_iff]
      exact ha.2.2
    · rw [triChi_eq_iff]
      exact ha.2.1
  have hχb : χ ⟨b, hbB⟩ = Equiv.swap 0 1 := by
    refine Equiv.ext fun i => ?_
    fin_cases i
    · rw [triChi_eq_iff]
      exact hb.2.1
    · rw [triChi_eq_iff]
      exact hb.1
    · rw [triChi_eq_iff]
      exact hb.2.2
  let f₁' : A₁ →* Y := f₁.comp (Subgroup.subgroupOfEquivOfLe inf_le_left).toMonoidHom
  let f₂' : A₂ →* Y := f₂.comp (Subgroup.subgroupOfEquivOfLe inf_le_left).toMonoidHom
  obtain ⟨f, ⟨hf1, hf2⟩, huniq⟩ := Recog.exists_unique_extend_of_permThree χ hA₁ hA₂ hχa hχb
    f₁' f₂' (fun k h₁ h₂ => hf k h₁ h₂) (fun h₁ h₂ h₃ => hrel h₁ h₂ h₃)
  refine ⟨f, ⟨fun x hx h₁ => ?_, fun x hx h₂ => ?_⟩, fun f' hf' => huniq f' ⟨?_, ?_⟩⟩
  · exact congrArg (fun φ : A₁ →* Y => φ ⟨⟨x, hx⟩, h₁⟩) hf1
  · exact congrArg (fun φ : A₂ →* Y => φ ⟨⟨x, hx⟩, h₂⟩) hf2
  · exact MonoidHom.ext fun x => hf'.1 _ x.1.2 _
  · exact MonoidHom.ext fun x => hf'.2 _ x.1.2 _

theorem exists_triangle_swaps
    (h : IsCTriangle v w u) :
    ∃ a b : Shat, (cvMul v a = v ∧ cvMul w a = u ∧ cvMul u a = w) ∧
      (cvMul v b = w ∧ cvMul w b = v ∧ cvMul u b = u) := by
  obtain ⟨b, hb⟩ := exists_swap_of_isCTriangle h
  obtain ⟨a, haw, hau, hav⟩ := exists_swap_of_isCTriangle
    (⟨h.2.2, h.1.symm, h.2.1.symm⟩ : IsCTriangle w u v)
  exact ⟨a, b, ⟨hav, haw, hau⟩, hb⟩

end Triangle

end CFSG.Monster.B.GSide
