module

public import CFSG.Quasithin.Background.SmithB42HatA6Model
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitHatA6

public section

namespace CFSG.Quasithin.HatA6

open CFSG.CharacterTheory.SteinbergBY
open scoped Matrix

section Frame

variable {K : Type*} [Field K]

theorem eq_smul_of_frame {c₀ c₁ c₂ c₃ : Fin 3 → K}
    (h012 : LinearIndependent K ![c₀, c₁, c₂]) (h013 : LinearIndependent K ![c₀, c₁, c₃])
    (h023 : LinearIndependent K ![c₀, c₂, c₃]) (h123 : LinearIndependent K ![c₁, c₂, c₃])
    (y : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) {a₀ a₁ a₂ a₃ : K}
    (hy₀ : y c₀ = a₀ • c₀) (hy₁ : y c₁ = a₁ • c₁) (hy₂ : y c₂ = a₂ • c₂)
    (hy₃ : y c₃ = a₃ • c₃) : y = a₃ • LinearMap.id := by
  have hspan : Submodule.span K (Set.range ![c₀, c₁, c₂]) = ⊤ :=
    h012.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : ∀ v : Fin 3 → K, ∃ b : Fin 3 → K, v = b 0 • c₀ + b 1 • c₁ + b 2 • c₂ := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range ![c₀, c₁, c₂]) := hspan ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
    refine ⟨b, ?_⟩
    rw [← hb, Fin.sum_univ_three]
    rfl
  have hli := Fintype.linearIndependent_iff.1 h012
  have hli013 := Fintype.linearIndependent_iff.1 h013
  have hli023 := Fintype.linearIndependent_iff.1 h023
  have hli123 := Fintype.linearIndependent_iff.1 h123
  obtain ⟨b, hb⟩ := hmem c₃
  have hb2 : b 2 ≠ 0 := by
    intro h0
    have := hli013 ![b 0, b 1, -1] (by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul]
      rw [hb, h0, zero_smul, add_zero]
      module) 2
    simp at this
  have hb1 : b 1 ≠ 0 := by
    intro h0
    have := hli023 ![b 0, b 2, -1] (by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul]
      rw [hb, h0, zero_smul, add_zero]
      module) 2
    simp at this
  have hb0 : b 0 ≠ 0 := by
    intro h0
    have := hli123 ![b 1, b 2, -1] (by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul]
      rw [hb, h0, zero_smul, zero_add]
      module) 2
    simp at this
  have h1 : y c₃ = b 0 • y c₀ + b 1 • y c₁ + b 2 • y c₂ := by
    rw [hb, map_add, map_add, map_smul, map_smul, map_smul]
  rw [hy₃, hy₀, hy₁, hy₂, hb] at h1
  have hrel := hli ![b 0 * a₀ - a₃ * b 0, b 1 * a₁ - a₃ * b 1, b 2 * a₂ - a₃ * b 2] (by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h2 : (b 0 * a₀ - a₃ * b 0) • c₀ + (b 1 * a₁ - a₃ * b 1) • c₁ +
        (b 2 * a₂ - a₃ * b 2) • c₂ =
        (b 0 • a₀ • c₀ + b 1 • a₁ • c₁ + b 2 • a₂ • c₂) -
          a₃ • (b 0 • c₀ + b 1 • c₁ + b 2 • c₂) := by module
    rw [h2, h1, sub_self])
  have e0 : a₀ = a₃ := by
    have h : b 0 * a₀ - a₃ * b 0 = 0 := hrel 0
    have h' : b 0 * (a₀ - a₃) = 0 := by rw [← h]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hb0)
  have e1 : a₁ = a₃ := by
    have h : b 1 * a₁ - a₃ * b 1 = 0 := hrel 1
    have h' : b 1 * (a₁ - a₃) = 0 := by rw [← h]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hb1)
  have e2 : a₂ = a₃ := by
    have h : b 2 * a₂ - a₃ * b 2 = 0 := hrel 2
    have h' : b 2 * (a₂ - a₃) = 0 := by rw [← h]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hb2)
  refine LinearMap.ext fun v => ?_
  obtain ⟨d, hd⟩ := hmem v
  rw [hd, map_add, map_add, map_smul, map_smul, map_smul, hy₀, hy₁, hy₂, e0, e1, e2,
    LinearMap.smul_apply, LinearMap.id_apply, smul_add, smul_add, smul_comm (d 0),
    smul_comm (d 1), smul_comm (d 2)]

end Frame


section Lines

theorem ff_unit_cases (u : FieldFourˣ) :
    (u : FieldFour) = 1 ∨ (u : FieldFour) = FieldFour.ω ∨ (u : FieldFour) = FieldFour.ω₂ := by
  have h := u.ne_zero
  revert h
  generalize (u : FieldFour) = c
  revert c
  decide

theorem span_eq_iff {c d : Fin 3 → FieldFour} :
    (FieldFour ∙ c) = (FieldFour ∙ d) ↔ ∃ u : FieldFourˣ, u • d = c := by
  rw [eq_comm, Submodule.span_singleton_eq_span_singleton]

theorem map_span_singleton (T : (Fin 3 → FieldFour) →ₗ[FieldFour] (Fin 3 → FieldFour))
    (c : Fin 3 → FieldFour) : (FieldFour ∙ c).map T = (FieldFour ∙ T c) := by
  rw [Submodule.map_span, Set.image_singleton]

theorem card_span_pair_le (c d : Fin 3 → FieldFour) :
    Nat.card (Submodule.span FieldFour {c, d}) ≤ 16 := by
  have hs : Function.Surjective (fun p : FieldFour × FieldFour =>
      (⟨p.1 • c + p.2 • d, Submodule.mem_span_pair.2 ⟨p.1, p.2, rfl⟩⟩ :
        Submodule.span FieldFour {c, d})) := by
    rintro ⟨v, hv⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
    exact ⟨(a, b), rfl⟩
  calc _ ≤ Nat.card (FieldFour × FieldFour) := Nat.card_le_card_of_surjective _ hs
    _ = 16 := by rw [Nat.card_prod, FieldFour.natCard_eq]

end Lines


section Action

variable {V : Type} [CommGroup V] {hsq : ∀ v : V, v * v = 1} {z : MulAut V}
  {u : Fin 3 → V} (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)
  {L : Subgroup (MulAut V)} (hLz : ∀ x ∈ L, ∀ w, x (z w) = z (x w)) (O : Set V)

@[expose] noncomputable def linL (l : ↥L) : (Fin 3 → FieldFour) →ₗ[FieldFour] (Fin 3 → FieldFour) :=
  linOf hb hzz (hLz l l.2)

theorem linL_mul (l₁ l₂ : ↥L) :
    linL hb hzz hLz (l₁ * l₂) = (linL hb hzz hLz l₁).comp (linL hb hzz hLz l₂) :=
  linOf_mul hb hzz (hLz _ l₁.2) (hLz _ l₂.2) (hLz _ (l₁ * l₂).2)

theorem linL_one : linL hb hzz hLz 1 = LinearMap.id :=
  linOf_one hb hzz (hLz _ (1 : ↥L).2)

theorem coordEquiv_linL (l : ↥L) (c : Fin 3 → FieldFour) :
    coordEquiv hb (Multiplicative.ofAdd (linL hb hzz hLz l c)) =
      (l : MulAut V) (coordEquiv hb (Multiplicative.ofAdd c)) :=
  coordEquiv_linOf hb hzz _ c

open Classical in
@[expose] noncomputable def okSet : Finset (Fin 3 → FieldFour) :=
  Finset.univ.filter fun c => coordEquiv hb (Multiplicative.ofAdd c) ∈ O

theorem mem_okSet {c : Fin 3 → FieldFour} :
    c ∈ okSet hb O ↔ coordEquiv hb (Multiplicative.ofAdd c) ∈ O := by
  classical
  unfold okSet
  rw [Finset.mem_filter]
  simp

open Classical in
@[expose] noncomputable def pts : Finset (Submodule FieldFour (Fin 3 → FieldFour)) :=
  (okSet hb O).image fun c => FieldFour ∙ c

theorem mem_pts {p : Submodule FieldFour (Fin 3 → FieldFour)} :
    p ∈ pts hb O ↔ ∃ c ∈ okSet hb O, (FieldFour ∙ c) = p := by
  classical
  unfold pts
  rw [Finset.mem_image]

variable (hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O)
include hO

theorem linL_mem_okSet (l : ↥L) {c : Fin 3 → FieldFour} (hc : c ∈ okSet hb O) :
    linL hb hzz hLz l c ∈ okSet hb O := by
  rw [mem_okSet, coordEquiv_linL]
  exact hO _ l.2 _ ((mem_okSet hb O).1 hc)

@[expose] noncomputable def ptAct (l : ↥L) : ↥(pts hb O) → ↥(pts hb O) := fun p =>
  ⟨p.1.map (linL hb hzz hLz l), by
    obtain ⟨c, hc, hcp⟩ := (mem_pts hb O).1 p.2
    rw [← hcp, map_span_singleton]
    exact (mem_pts hb O).2 ⟨_, linL_mem_okSet hb hzz hLz O hO l hc, rfl⟩⟩

theorem ptAct_coe (l : ↥L) (p : ↥(pts hb O)) :
    (ptAct hb hzz hLz O hO l p : Submodule FieldFour (Fin 3 → FieldFour)) =
      (p : Submodule FieldFour (Fin 3 → FieldFour)).map (linL hb hzz hLz l) := rfl

theorem ptAct_mul (l₁ l₂ : ↥L) (p : ↥(pts hb O)) :
    ptAct hb hzz hLz O hO (l₁ * l₂) p = ptAct hb hzz hLz O hO l₁ (ptAct hb hzz hLz O hO l₂ p) := by
  apply Subtype.ext
  rw [ptAct_coe, ptAct_coe, ptAct_coe, linL_mul, Submodule.map_comp]

theorem ptAct_one (p : ↥(pts hb O)) : ptAct hb hzz hLz O hO 1 p = p := by
  apply Subtype.ext
  rw [ptAct_coe, linL_one, Submodule.map_id]

@[expose] noncomputable def ptPerm : ↥L →* Equiv.Perm ↥(pts hb O) where
  toFun l :=
    { toFun := ptAct hb hzz hLz O hO l
      invFun := ptAct hb hzz hLz O hO l⁻¹
      left_inv := fun p => by rw [← ptAct_mul, inv_mul_cancel, ptAct_one]
      right_inv := fun p => by rw [← ptAct_mul, mul_inv_cancel, ptAct_one] }
  map_one' := Equiv.ext fun p => ptAct_one hb hzz hLz O hO p
  map_mul' l₁ l₂ := Equiv.ext fun p => ptAct_mul hb hzz hLz O hO l₁ l₂ p

theorem ptPerm_apply (l : ↥L) (p : ↥(pts hb O)) :
    ptPerm hb hzz hLz O hO l p = ptAct hb hzz hLz O hO l p := rfl

end Action


section Count

variable {V : Type} [CommGroup V] [Finite V] {hsq : ∀ v : V, v * v = 1} {z : MulAut V}
  {u : Fin 3 → V} (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)
  (O : Set V)

theorem card_okSet : (okSet hb O).card = Nat.card O := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have h : okSet hb O = (Set.toFinset O).image fun v =>
      Multiplicative.toAdd ((coordEquiv hb).symm v) := by
    ext c
    rw [mem_okSet, Finset.mem_image]
    constructor
    · intro hc
      exact ⟨_, Set.mem_toFinset.2 hc, by rw [MulEquiv.symm_apply_apply, toAdd_ofAdd]⟩
    · rintro ⟨v, hv, rfl⟩
      rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      exact Set.mem_toFinset.1 hv
  rw [h, Finset.card_image_of_injective _ (fun v w hvw => (coordEquiv hb).symm.injective
    (Multiplicative.toAdd.injective hvw)), Set.toFinset_card, Nat.card_eq_fintype_card]

omit [Finite V] in
theorem ne_zero_of_mem_okSet (h1O : (1 : V) ∉ O) {c : Fin 3 → FieldFour}
    (hc : c ∈ okSet hb O) : c ≠ 0 := by
  rintro rfl
  apply h1O
  have := (mem_okSet hb O).1 hc
  rwa [ofAdd_zero, map_one] at this

include hzz in
omit [Finite V] in
theorem smul_mem_okSet (hzO : ∀ v ∈ O, z v ∈ O) {c : Fin 3 → FieldFour} (hc : c ∈ okSet hb O)
    (k : FieldFourˣ) :
    (k : FieldFour) • c ∈ okSet hb O := by
  have hω : FieldFour.ω • c ∈ okSet hb O := by
    rw [mem_okSet, coordEquiv_smul hb hzz, fsmul_ω]
    exact hzO _ ((mem_okSet hb O).1 hc)
  rcases ff_unit_cases k with h | h | h <;> rw [h]
  · rwa [one_smul]
  · exact hω
  · have e : FieldFour.ω₂ = FieldFour.ω * FieldFour.ω := by decide
    rw [e, mul_smul]
    rw [mem_okSet, coordEquiv_smul hb hzz, fsmul_ω]
    exact hzO _ ((mem_okSet hb O).1 hω)

include hzz in
omit [Finite V] in
theorem card_fiber (h1O : (1 : V) ∉ O) (hzO : ∀ v ∈ O, z v ∈ O) {c : Fin 3 → FieldFour}
    (hc : c ∈ okSet hb O) :
    ((okSet hb O).filter fun d => (FieldFour ∙ d) = (FieldFour ∙ c)).card = 3 := by
  classical
  have hc0 := ne_zero_of_mem_okSet hb O h1O hc
  have hfib : ((okSet hb O).filter fun d => (FieldFour ∙ d) = (FieldFour ∙ c)) =
      {c, FieldFour.ω • c, FieldFour.ω₂ • c} := by
    ext d
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hd⟩
      obtain ⟨k, hk⟩ := (span_eq_iff).1 hd
      rcases ff_unit_cases k with h | h | h
      · left; rw [← hk, Units.smul_def, h, one_smul]
      · right; left; rw [← hk, Units.smul_def, h]
      · right; right; rw [← hk, Units.smul_def, h]
    · have hω : FieldFour.ω ≠ 0 := by decide
      have hω₂ : FieldFour.ω₂ ≠ 0 := by decide
      rintro (rfl | rfl | rfl)
      · exact ⟨hc, rfl⟩
      · exact ⟨smul_mem_okSet hb hzz O hzO hc (Units.mk0 _ hω),
          Submodule.span_singleton_smul_eq (Units.mk0 _ hω).isUnit c⟩
      · exact ⟨smul_mem_okSet hb hzz O hzO hc (Units.mk0 _ hω₂),
          Submodule.span_singleton_smul_eq (Units.mk0 _ hω₂).isUnit c⟩
  rw [hfib]
  have h1 : c ≠ FieldFour.ω • c := by
    intro h
    have : (1 - FieldFour.ω) • c = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact hc0 ((smul_eq_zero.1 this).resolve_left (by decide))
  have h2 : c ≠ FieldFour.ω₂ • c := by
    intro h
    have : (1 - FieldFour.ω₂) • c = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact hc0 ((smul_eq_zero.1 this).resolve_left (by decide))
  have h3 : FieldFour.ω • c ≠ FieldFour.ω₂ • c := by
    intro h
    have : (FieldFour.ω - FieldFour.ω₂) • c = 0 := by rw [sub_smul, h, sub_self]
    exact hc0 ((smul_eq_zero.1 this).resolve_left (by decide))
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]

include hzz in
theorem card_pts (h1O : (1 : V) ∉ O) (hzO : ∀ v ∈ O, z v ∈ O) :
    3 * (pts hb O).card = Nat.card O := by
  classical
  rw [← card_okSet hb O, Finset.card_eq_sum_card_image (fun c => FieldFour ∙ c) (okSet hb O)]
  have : ∀ p ∈ (okSet hb O).image (fun c => FieldFour ∙ c),
      ((okSet hb O).filter fun d => (FieldFour ∙ d) = p).card = 3 := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    exact card_fiber hb hzz O h1O hzO hc
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

end Count


section Sub

variable {V : Type} [CommGroup V] {hsq : ∀ v : V, v * v = 1} {z : MulAut V}
  {u : Fin 3 → V} (hb : Function.Bijective (coordHom hsq z u))

@[expose] noncomputable def subOf (W : Submodule FieldFour (Fin 3 → FieldFour)) : Subgroup V :=
  (AddSubgroup.toSubgroup W.toAddSubgroup).map (coordEquiv hb).toMonoidHom

theorem mem_subOf {W : Submodule FieldFour (Fin 3 → FieldFour)} {v : V} :
    v ∈ subOf hb W ↔ Multiplicative.toAdd ((coordEquiv hb).symm v) ∈ W := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    change Multiplicative.toAdd ((coordEquiv hb).symm (coordEquiv hb c)) ∈ W
    rw [MulEquiv.symm_apply_apply]
    exact hc
  · intro hv
    exact ⟨(coordEquiv hb).symm v, hv, MulEquiv.apply_symm_apply _ v⟩

theorem card_subOf (W : Submodule FieldFour (Fin 3 → FieldFour)) :
    Nat.card (subOf hb W) = Nat.card W := by
  rw [subOf, Subgroup.card_map_of_injective (f := (coordEquiv hb).toMonoidHom)
    (coordEquiv hb).injective]
  exact Nat.card_congr (Equiv.refl _)

end Sub

section Six

variable {V : Type} [CommGroup V] [Finite V] {hsq : ∀ v : V, v * v = 1} {z : MulAut V}
  {u : Fin 3 → V} (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)
  {L : Subgroup (MulAut V)} (hLz : ∀ x ∈ L, ∀ w, x (z w) = z (x w)) {O : Set V}
  (hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O)

omit [Finite V] in
theorem ptPerm_eq_one_of_smul {l : ↥L} {k : FieldFour} (hk : k ≠ 0)
    (hl : linL hb hzz hLz l = k • LinearMap.id) : ptPerm hb hzz hLz O hO l = 1 := by
  refine Equiv.ext fun p => Subtype.ext ?_
  change (p : Submodule FieldFour (Fin 3 → FieldFour)).map (linL hb hzz hLz l) = p
  obtain ⟨c, -, hcp⟩ := (mem_pts hb O).1 p.2
  rw [← hcp, map_span_singleton, hl, LinearMap.smul_apply, LinearMap.id_apply]
  exact Submodule.span_singleton_smul_eq (Units.mk0 k hk).isUnit c

variable (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
  (hV : Nat.card V = 2 ^ 6)

omit [Finite V] in
include hirr hV in
theorem not_forall_ptAct_eq (c : Fin 3 → FieldFour) (hc : c ≠ 0) :
    ¬ ∀ l : ↥L, (FieldFour ∙ c).map (linL hb hzz hLz l) = (FieldFour ∙ c) := by
  intro h
  have hinv : ∀ l ∈ L, ∀ v ∈ subOf hb (FieldFour ∙ c), l v ∈ subOf hb (FieldFour ∙ c) := by
    intro l hl v hv
    rw [mem_subOf] at hv ⊢
    rw [symm_apply_eq_linOf hb hzz (hLz l hl), toAdd_ofAdd]
    rw [← h ⟨l, hl⟩]
    exact ⟨_, hv, rfl⟩
  have hcard : Nat.card (FieldFour ∙ c) ≤ 4 := by
    have hs : Function.Surjective (fun k : FieldFour =>
        (⟨k • c, Submodule.mem_span_singleton.2 ⟨k, rfl⟩⟩ : (FieldFour ∙ c))) := by
      rintro ⟨v, hv⟩
      obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hv
      exact ⟨k, rfl⟩
    calc _ ≤ Nat.card FieldFour := Nat.card_le_card_of_surjective _ hs
      _ = 4 := FieldFour.natCard_eq
  rcases hirr _ hinv with h0 | h0
  · have hmem : coordEquiv hb (Multiplicative.ofAdd c) ∈ subOf hb (FieldFour ∙ c) := by
      rw [mem_subOf, MulEquiv.symm_apply_apply, toAdd_ofAdd]
      exact Submodule.mem_span_singleton_self c
    rw [h0, Subgroup.mem_bot] at hmem
    apply hc
    have := congrArg (fun w => Multiplicative.toAdd ((coordEquiv hb).symm w)) hmem
    simpa using this
  · have := card_subOf hb (FieldFour ∙ c)
    rw [h0, Subgroup.card_top, hV] at this
    omega

end Six


section Alt

variable {V : Type} [CommGroup V] [Finite V] {hsq : ∀ v : V, v * v = 1} {z : MulAut V}
  {u : Fin 3 → V} (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)
  {L : Subgroup (MulAut V)} (hLz : ∀ x ∈ L, ∀ w, x (z w) = z (x w)) {O : Set V}
  (hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O)
  (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
  (hV : Nat.card V = 2 ^ 6) {zL : ↥L} (hzL : (zL : MulAut V) = z)
  (hcen : Subgroup.center ↥L = Subgroup.zpowers zL)
  (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
  (hOcard : Nat.card O = 18) (h1O : (1 : V) ∉ O)

omit [Finite V] in
include hzL hcen in
theorem center_le_ker_ptPerm : Subgroup.center ↥L ≤ (ptPerm hb hzz hLz O hO).ker := by
  rw [hcen, Subgroup.zpowers_le, MonoidHom.mem_ker]
  exact ptPerm_eq_one_of_smul hb hzz hLz hO (k := FieldFour.ω) (by decide)
    (linOf_eq_smul hb hzz _ hzL)

@[expose] noncomputable def altPerm : alternatingGroup (Fin 6) →* Equiv.Perm ↥(pts hb O) :=
  (QuotientGroup.lift _ (ptPerm hb hzz hLz O hO) (center_le_ker_ptPerm hb hzz hLz hO hzL hcen)).comp
    e.symm.toMonoidHom

omit [Finite V] in
theorem ptPerm_eq_altPerm (l : ↥L) :
    ptPerm hb hzz hLz O hO l = altPerm hb hzz hLz hO hzL hcen e (e (QuotientGroup.mk l)) := by
  simp [altPerm]

include hirr hV hOcard h1O in
theorem altPerm_injective : Function.Injective (altPerm hb hzz hLz hO hzL hcen e) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hn := (altPerm hb hzz hLz hO hzL hcen e).normal_ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (altPerm hb hzz hLz hO hzL hcen e).ker with
    h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    have hall : ∀ l : ↥L, ptPerm hb hzz hLz O hO l = 1 := fun l => by
      rw [ptPerm_eq_altPerm hb hzz hLz hO hzL hcen e l, ← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top _
    have hne : (okSet hb O).Nonempty := by
      rw [← Finset.card_pos, card_okSet, hOcard]
      norm_num
    obtain ⟨c, hc⟩ := hne
    refine not_forall_ptAct_eq hb hzz hLz hirr hV c (ne_zero_of_mem_okSet hb O h1O hc) ?_
    intro l
    have h1 := congrArg (fun σ : Equiv.Perm ↥(pts hb O) =>
      ((σ ⟨_, (mem_pts hb O).2 ⟨c, hc, rfl⟩⟩ : ↥(pts hb O)) :
        Submodule FieldFour (Fin 3 → FieldFour))) (hall l)
    exact h1


include hzz hO hzL hOcard h1O in
theorem card_pts_eq : (pts hb O).card = 6 := by
  have hzO : ∀ v ∈ O, z v ∈ O := fun v hv => hzL ▸ hO _ zL.2 v hv
  have h := card_pts hb hzz O h1O hzO
  omega

include hirr hV hOcard h1O hzL hcen e in
theorem range_ptPerm :
    (ptPerm hb hzz hLz O hO).range = alternatingGroup ↥(pts hb O) := by
  classical
  have hrange : (ptPerm hb hzz hLz O hO).range = (altPerm hb hzz hLz hO hzL hcen e).range := by
    ext σ
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨_, (ptPerm_eq_altPerm hb hzz hLz hO hzL hcen e l).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm a)
      refine ⟨l, ?_⟩
      rw [ptPerm_eq_altPerm hb hzz hLz hO hzL hcen e l, hl, MulEquiv.apply_symm_apply]
  rw [hrange]
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hinj := altPerm_injective hb hzz hLz hO hirr hV hzL hcen e hOcard h1O
  have hcr : Nat.card (altPerm hb hzz hLz hO hzL hcen e).range = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, H13.Orbit.card_alt6_eq]
  have hcP : Nat.card (Equiv.Perm ↥(pts hb O)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe,
      card_pts_eq hb hzz hO hzL hOcard h1O]
    decide
  have h := (altPerm hb hzz hLz hO hzL hcen e).range.card_mul_index
  rw [hcr, hcP] at h
  omega

include hirr hV hOcard h1O hzL hcen e in
theorem exists_ptPerm_eq {n : ℕ} (hn : n ≤ 4) (g h : Fin n ↪ ↥(pts hb O)) :
    ∃ l : ↥L, ∀ i, ptPerm hb hzz hLz O hO l (g i) = h i := by
  classical
  have hc : Nat.card ↥(pts hb O) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_pts_eq hb hzz hO hzL hOcard h1O]
  have hmt : MulAction.IsMultiplyPretransitive (alternatingGroup ↥(pts hb O)) ↥(pts hb O) 4 := by
    have := alternatingGroup.isMultiplyPretransitive ↥(pts hb O)
    rw [hc] at this
    exact this
  have hmt' : MulAction.IsMultiplyPretransitive (alternatingGroup ↥(pts hb O)) ↥(pts hb O) n :=
    MulAction.isMultiplyPretransitive_of_le hn (by rw [hc]; norm_num)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup ↥(pts hb O)) g h
  have hσr : (σ : Equiv.Perm ↥(pts hb O)) ∈ (ptPerm hb hzz hLz O hO).range := by
    rw [range_ptPerm hb hzz hLz hO hirr hV hzL hcen e hOcard h1O]
    exact σ.2
  obtain ⟨l, hl⟩ := hσr
  refine ⟨l, fun i => ?_⟩
  rw [hl, ← hσ]
  rfl


omit [Finite V] in
theorem pair_indep {c d : Fin 3 → FieldFour} (hc : c ≠ 0) (hd : d ≠ 0)
    (hcd : (FieldFour ∙ c) ≠ (FieldFour ∙ d)) : LinearIndependent FieldFour ![c, d] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hc, ht⟩
  · exfalso
    by_cases hs : s = 0
    · rw [hs, zero_smul, zero_add] at hst
      exact hd ((smul_eq_zero.1 hst).resolve_left ht)
    · apply hcd
      have hdc : d = (-(s / t)) • c := by
        have h1 : t • d = -(s • c) := eq_neg_of_add_eq_zero_right hst
        calc d = t⁻¹ • (t • d) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(s / t)) • c := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [hdc]
      exact (Submodule.span_singleton_smul_eq
        (Units.mk0 _ (neg_ne_zero.2 (div_ne_zero hs ht))).isUnit c).symm


omit [Finite V] in
theorem vec3_eq_snoc {M : Type*} (a b c : M) : ![a, b, c] = Fin.snoc ![a, b] c := by
  funext i
  fin_cases i <;> rfl

include hirr hO in
omit [Finite V] in
theorem closure_eq_top (hne : O.Nonempty) (h1O : (1 : V) ∉ O) : Subgroup.closure O = ⊤ := by
  have hinv : ∀ l ∈ L, ∀ v ∈ Subgroup.closure O, l v ∈ Subgroup.closure O := by
    intro l hl v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (hO l hl y hy)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha
  rcases hirr _ hinv with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hne
    have : v ∈ Subgroup.closure O := Subgroup.subset_closure hv
    rw [h, Subgroup.mem_bot] at this
    exact h1O (this ▸ hv)
  · exact h

include hzz hLz hO hirr hV hOcard h1O hzL hcen e in
theorem indep_of_three {c₁ c₂ c₃ : Fin 3 → FieldFour} (h₁ : c₁ ∈ okSet hb O)
    (h₂ : c₂ ∈ okSet hb O) (h₃ : c₃ ∈ okSet hb O) (h12 : (FieldFour ∙ c₁) ≠ (FieldFour ∙ c₂))
    (h13 : (FieldFour ∙ c₁) ≠ (FieldFour ∙ c₃)) (h23 : (FieldFour ∙ c₂) ≠ (FieldFour ∙ c₃)) :
    LinearIndependent FieldFour ![c₁, c₂, c₃] := by
  classical
  by_contra hdep
  have hA : ∀ d₁ d₂ d₃ : Fin 3 → FieldFour, d₁ ∈ okSet hb O → d₂ ∈ okSet hb O →
      d₃ ∈ okSet hb O → (FieldFour ∙ d₁) ≠ (FieldFour ∙ d₂) →
      (FieldFour ∙ d₁) ≠ (FieldFour ∙ d₃) → (FieldFour ∙ d₂) ≠ (FieldFour ∙ d₃) →
      ¬ LinearIndependent FieldFour ![d₁, d₂, d₃] := by
    intro d₁ d₂ d₃ hd₁ hd₂ hd₃ h'12 h'13 h'23 hind
    let P := pts hb O
    let pt : ∀ c : Fin 3 → FieldFour, c ∈ okSet hb O → ↥P := fun c hc =>
      ⟨FieldFour ∙ c, (mem_pts hb O).2 ⟨c, hc, rfl⟩⟩
    have hpt : ∀ c hc, ((pt c hc : ↥P) : Submodule FieldFour (Fin 3 → FieldFour)) =
        (FieldFour ∙ c) := fun _ _ => rfl
    let g : Fin 3 ↪ ↥P := ⟨![pt c₁ h₁, pt c₂ h₂, pt c₃ h₃], by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [pt]⟩
    let h : Fin 3 ↪ ↥P := ⟨![pt d₁ hd₁, pt d₂ hd₂, pt d₃ hd₃], by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [pt]⟩
    obtain ⟨l, hl⟩ := exists_ptPerm_eq hb hzz hLz hO hirr hV hzL hcen e hOcard h1O
      (by norm_num) g h
    have key : ∀ i : Fin 3, ∃ w : FieldFourˣ, w • ![d₁, d₂, d₃] i =
        linL hb hzz hLz l (![c₁, c₂, c₃] i) := by
      intro i
      have hli := congrArg Subtype.val (hl i)
      rw [ptPerm_apply, ptAct_coe] at hli
      have hg : ((g i : ↥P) : Submodule FieldFour (Fin 3 → FieldFour)) =
          (FieldFour ∙ ![c₁, c₂, c₃] i) := by fin_cases i <;> rfl
      have hh : ((h i : ↥P) : Submodule FieldFour (Fin 3 → FieldFour)) =
          (FieldFour ∙ ![d₁, d₂, d₃] i) := by fin_cases i <;> rfl
      rw [hg, hh, map_span_singleton] at hli
      exact (span_eq_iff).1 hli
    choose w hw using key
    apply hdep
    have h1 := hind.units_smul w
    have h2 : (w • ![d₁, d₂, d₃]) = (linL hb hzz hLz l) ∘ ![c₁, c₂, c₃] := by
      funext i
      exact hw i
    rw [h2] at h1
    exact h1.of_comp
  have hc₁ := ne_zero_of_mem_okSet hb O h1O h₁
  have hc₂ := ne_zero_of_mem_okSet hb O h1O h₂
  have hpair := pair_indep hc₁ hc₂ h12
  have hB : ∀ d ∈ okSet hb O, d ∈ Submodule.span FieldFour {c₁, c₂} := by
    intro d hd
    by_cases hd1 : (FieldFour ∙ d) = (FieldFour ∙ c₁)
    · obtain ⟨k, hk⟩ := (span_eq_iff).1 hd1
      rw [← hk]
      exact Submodule.smul_of_tower_mem _ k (Submodule.subset_span (Set.mem_insert _ _))
    by_cases hd2 : (FieldFour ∙ d) = (FieldFour ∙ c₂)
    · obtain ⟨k, hk⟩ := (span_eq_iff).1 hd2
      rw [← hk]
      exact Submodule.smul_of_tower_mem _ k
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    have hdep' := hA c₁ c₂ d h₁ h₂ hd h12 (Ne.symm hd1) (Ne.symm hd2)
    rw [vec3_eq_snoc, linearIndependent_finSnoc] at hdep'
    by_contra hnot
    apply hdep'
    refine ⟨hpair, fun hmem => hnot (Submodule.span_mono ?_ hmem)⟩
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp
  have hne : O.Nonempty := by
    have h0 : 0 < Nat.card ↥O := by rw [hOcard]; norm_num
    obtain ⟨⟨v, hv⟩⟩ := (Nat.card_pos_iff.1 h0).1
    exact ⟨v, hv⟩
  have htop := closure_eq_top hO hirr hne h1O
  have hle : Subgroup.closure O ≤ subOf hb (Submodule.span FieldFour {c₁, c₂}) := by
    rw [Subgroup.closure_le]
    intro v hv
    rw [SetLike.mem_coe, mem_subOf]
    refine hB _ ?_
    rw [mem_okSet, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    exact hv
  rw [htop] at hle
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_top, card_subOf, hV] at h1
  have h2 := card_span_pair_le c₁ c₂
  omega


include hb hzz hLz hO hirr hV hOcard h1O hzL hcen e in
theorem mem_of_preserves {x : MulAut V} (hx : ∀ w, x (z w) = z (x w))
    (hxO : ∀ v ∈ O, x v ∈ O) : x ∈ L := by
  classical
  set T := linOf hb hzz hx with hTdef
  have hTO : ∀ c ∈ okSet hb O, T c ∈ okSet hb O := by
    intro c hc
    rw [mem_okSet, hTdef, coordEquiv_linOf]
    exact hxO _ ((mem_okSet hb O).1 hc)
  have hTinj : Function.Injective T := by
    intro c c' hcc'
    have h1 := congrArg (fun d => coordEquiv hb (Multiplicative.ofAdd d)) hcc'
    simp only [hTdef, coordEquiv_linOf] at h1
    exact Multiplicative.ofAdd.injective ((coordEquiv hb).injective (x.injective h1))
  have hc6 : Nat.card ↥(pts hb O) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_pts_eq hb hzz hO hzL hOcard h1O]
  obtain ⟨g⟩ : Nonempty (Fin 4 ↪ ↥(pts hb O)) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin, Fintype.card_coe, card_pts_eq hb hzz hO hzL hOcard h1O]; norm_num)
  have hrep : ∀ p : ↥(pts hb O), ∃ c ∈ okSet hb O, (FieldFour ∙ c) = (p : Submodule _ _) :=
    fun p => (mem_pts hb O).1 p.2
  choose c hcO hcp using hrep
  let h' : Fin 4 ↪ ↥(pts hb O) :=
    ⟨fun i => ⟨FieldFour ∙ T (c (g i)), (mem_pts hb O).2 ⟨_, hTO _ (hcO _), rfl⟩⟩, by
      intro i j hij
      have h1 : (FieldFour ∙ T (c (g i))) = (FieldFour ∙ T (c (g j))) := congrArg Subtype.val hij
      obtain ⟨k, hk⟩ := (span_eq_iff).1 h1
      have h2 : (k : FieldFour) • c (g j) = c (g i) := by
        apply hTinj
        rw [map_smul]
        exact hk
      have h3 : (FieldFour ∙ c (g i)) = (FieldFour ∙ c (g j)) := (span_eq_iff).2 ⟨k, h2⟩
      rw [hcp, hcp] at h3
      exact g.injective (Subtype.ext h3)⟩
  obtain ⟨l, hl⟩ := exists_ptPerm_eq hb hzz hLz hO hirr hV hzL hcen e hOcard h1O le_rfl h' g
  have key : ∀ i : Fin 4, ∃ w : FieldFourˣ,
      w • c (g i) = linL hb hzz hLz l (T (c (g i))) := by
    intro i
    have hli := congrArg Subtype.val (hl i)
    rw [ptPerm_apply, ptAct_coe] at hli
    change (FieldFour ∙ T (c (g i))).map (linL hb hzz hLz l) = (g i : Submodule _ _) at hli
    rw [map_span_singleton, ← hcp] at hli
    exact (span_eq_iff).1 hli
  choose w hw using key
  have hy : ∀ v, ((l : MulAut V) * x) (z v) = z (((l : MulAut V) * x) v) := fun v => by
    rw [MulAut.mul_apply, MulAut.mul_apply, hx, hLz _ l.2]
  have hTy : linOf hb hzz hy = (linL hb hzz hLz l).comp T :=
    linOf_mul hb hzz (hLz _ l.2) hx hy
  have hfix : ∀ i, linOf hb hzz hy (c (g i)) = (w i : FieldFour) • c (g i) := by
    intro i
    rw [hTy, LinearMap.comp_apply, ← hw i, Units.smul_def]
  have hd : ∀ i j : Fin 4, i ≠ j → (FieldFour ∙ c (g i)) ≠ (FieldFour ∙ c (g j)) := by
    intro i j hij h
    rw [hcp, hcp] at h
    exact hij (g.injective (Subtype.ext h))
  have hind : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      LinearIndependent FieldFour ![c (g i), c (g j), c (g k)] := fun i j k hij hik hjk =>
    indep_of_three hb hzz hLz hO hirr hV hzL hcen e hOcard h1O (hcO _) (hcO _) (hcO _)
      (hd i j hij) (hd i k hik) (hd j k hjk)
  have hfr := eq_smul_of_frame (hind 0 1 2 (by decide) (by decide) (by decide))
    (hind 0 1 3 (by decide) (by decide) (by decide))
    (hind 0 2 3 (by decide) (by decide) (by decide))
    (hind 1 2 3 (by decide) (by decide) (by decide)) _ (hfix 0) (hfix 1) (hfix 2) (hfix 3)
  have hzLmem : z ∈ L := hzL ▸ zL.2
  have hyL : (l : MulAut V) * x ∈ L := by
    have hz1 : ∀ v, (1 : MulAut V) (z v) = z ((1 : MulAut V) v) := fun v => rfl
    have hzz' : ∀ v, z (z v) = z (z v) := fun v => rfl
    have hz2 : ∀ v, (z * z) (z v) = z ((z * z) v) := fun v => rfl
    rcases ff_unit_cases (w 3) with h | h | h <;> rw [h] at hfr
    · rw [one_smul, ← linOf_one hb hzz hz1] at hfr
      rw [eq_of_linOf_eq hb hzz hy hz1 hfr]
      exact L.one_mem
    · rw [← linOf_z hb hzz hzz'] at hfr
      rw [eq_of_linOf_eq hb hzz hy hzz' hfr]
      exact hzLmem
    · have hzz2 : linOf hb hzz hz2 = FieldFour.ω₂ • LinearMap.id := by
        rw [linOf_mul hb hzz hzz' hzz' hz2, linOf_z hb hzz hzz']
        have e2 : FieldFour.ω₂ = FieldFour.ω * FieldFour.ω := by decide
        rw [e2, mul_smul]
        exact LinearMap.ext fun v => by simp
      rw [← hzz2] at hfr
      rw [eq_of_linOf_eq hb hzz hy hz2 hfr]
      exact L.mul_mem hzLmem hzLmem
  have : x = (l : MulAut V)⁻¹ * ((l : MulAut V) * x) := by group
  rw [this]
  exact L.mul_mem (L.inv_mem l.2) hyL

end Alt


section Normalizer

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_orbitIn_map {L : Subgroup (MulAut V)} {x : MulAut V}
    (hxN : ∀ l, l ∈ L ↔ x * l * x⁻¹ ∈ L) (v : V) :
    Nat.card (H13.Orbit.orbitIn L (x v)) = Nat.card (H13.Orbit.orbitIn L v) := by
  refine Nat.card_congr
    { toFun := fun w => ⟨x⁻¹ w, ?_⟩
      invFun := fun w => ⟨x w, ?_⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  · obtain ⟨l, hl, hlw⟩ := w.2
    refine ⟨x⁻¹ * l * x, ?_, ?_⟩
    · have := (hxN (x⁻¹ * l * x)).2 (by simpa [mul_assoc] using hl)
      exact this
    · rw [← hlw]
      rfl
  · obtain ⟨l, hl, hlw⟩ := w.2
    refine ⟨x * l * x⁻¹, (hxN l).1 hl, ?_⟩
    rw [← hlw]
    simp [MulAut.mul_apply]

theorem mem_of_normalizes (hsq2 : ∀ v : V, v ^ 2 = 1) (hV : Nat.card V = 2 ^ 6)
    {L : Subgroup (MulAut V)} (hperf : Group.IsPerfect ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {x : MulAut V} (hxN : ∀ l, l ∈ L ↔ x * l * x⁻¹ ∈ L)
    (hxz : ∀ k ∈ Subgroup.center ↥L, x * (k : MulAut V) = (k : MulAut V) * x) : x ∈ L := by
  obtain ⟨zL, hcen, h3, hfp⟩ := exists_center_fpf hsq2 hV hperf hZ e
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hsq2 v
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hzz : ∀ w, z (z w) = w * z w := fun w =>
    H13.zz_eq_of_fpf hsq2 h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  obtain ⟨u, hb⟩ := exists_coord hsq hV h3 hfp
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hLz : ∀ l ∈ L, ∀ w, l (z w) = z (l w) := by
    intro l hl w
    have h1 := Subgroup.mem_center_iff.1 hzc ⟨l, hl⟩
    exact congrArg (fun y : ↥L => (y : MulAut V) w) h1
  have hx : ∀ w, x (z w) = z (x w) := fun w =>
    congrArg (fun y : MulAut V => y w) (hxz zL hzc)
  have hperf' : commutator ↥L = ⊤ := Group.isPerfect_def.1 hperf
  have hfpf : ∀ k ∈ Subgroup.center ↥L, k ≠ 1 → ∀ v : V, (k : MulAut V) v = v → v = 1 := by
    intro k hk hk1 v hv
    rw [hcen] at hk
    obtain ⟨n, hn0⟩ := (mem_powers_iff_mem_zpowers).2 hk
    have hn0' : zL ^ n = k := hn0
    rw [← hn0'] at hk1 hv
    have hz3 : zL ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
    have hn : zL ^ n = zL ^ (n % 3) := by
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hz3, one_pow, one_mul]
    rw [hn] at hk1 hv
    have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 3)
    · exact absurd (pow_zero zL) hk1
    · exact hfp v (by simpa using hv)
    · apply hfp v
      have h2 : z (z v) = v := by simpa [pow_two, MulAut.mul_apply] using hv
      calc z v = z (z (z v)) := by rw [h2]
        _ = v := by
          have := congrArg (fun y : MulAut V => y v) h3
          simpa [pow_succ, MulAut.mul_apply] using this
  obtain ⟨f, hf1, hf⟩ := H13.Orbit.hatA6_orbits hV hperf' hZ e hfpf
  set O := H13.Orbit.orbitIn L f with hOdef
  have hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O := by
    rintro l hl _ ⟨m, hm, rfl⟩
    exact ⟨l * m, L.mul_mem hl hm, rfl⟩
  have hfO : f ∈ O := ⟨1, L.one_mem, rfl⟩
  have hOcard : Nat.card O = 18 := (hf f hf1).1 hfO
  have h1O : (1 : V) ∉ O := by
    rintro ⟨m, -, hm⟩
    apply hf1
    have := congrArg (fun w => m⁻¹ w) hm
    simpa using this
  have hxO : ∀ v ∈ O, x v ∈ O := by
    intro v hv
    have hv1 : v ≠ 1 := fun h => h1O (h ▸ hv)
    have hxv1 : x v ≠ 1 := fun h => hv1 (x.injective (h.trans (map_one x).symm))
    have hvO : H13.Orbit.orbitIn L v = O := by
      obtain ⟨m, hm, rfl⟩ := hv
      ext w
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n * m, L.mul_mem hn hm, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        refine ⟨n * m⁻¹, L.mul_mem hn (L.inv_mem hm), ?_⟩
        simp [MulAut.mul_apply]
    by_contra hcon
    have h18 : Nat.card (H13.Orbit.orbitIn L (x v)) = 18 := by
      rw [card_orbitIn_map hxN v, hvO, hOcard]
    have h45 := (hf (x v) hxv1).2 hcon
    omega
  exact mem_of_preserves hb hzz hLz hO hirr hV rfl hcen e hOcard h1O hx hxO

end Normalizer

end CFSG.Quasithin.HatA6
