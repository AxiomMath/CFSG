module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Sylow

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace SzPS8

namespace L28

open Matrix

abbrev F4 : Type := GaloisField 2 2

abbrev Pr : Type := SL(2, F4) × SL(2, F4)

@[expose] noncomputable def act (g : Pr) (X : Matrix (Fin 2) (Fin 2) F4) :
    Matrix (Fin 2) (Fin 2) F4 :=
  (g.1 : Matrix (Fin 2) (Fin 2) F4) * X * ((g.2⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4)

@[expose] noncomputable def UU : Subgroup Pr := (U F4).prod (U F4)

@[expose] noncomputable def BB : Subgroup Pr := Subgroup.normalizer ((UU : Subgroup Pr) : Set Pr)

section Action

theorem act_mul (g h : Pr) (X : Matrix (Fin 2) (Fin 2) F4) :
    act (g * h) X = act g (act h X) := by
  unfold act
  simp only [Prod.fst_mul, Prod.snd_mul, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_assoc]

theorem act_one (X : Matrix (Fin 2) (Fin 2) F4) : act 1 X = X := by
  unfold act
  simp

theorem act_add (g : Pr) (X Y : Matrix (Fin 2) (Fin 2) F4) : act g (X + Y) = act g X + act g Y := by
  unfold act
  rw [Matrix.mul_add, Matrix.add_mul]

theorem act_up (a b : F4) (X : Matrix (Fin 2) (Fin 2) F4) :
    act (up a, up b) X = !![X 0 0 + a * X 1 0, X 0 1 + a * X 1 1 - b * (X 0 0 + a * X 1 0);
      X 1 0, X 1 1 - b * X 1 0] := by
  have hb : ((up b)⁻¹ : SL(2, F4)) = ⟨!![1, -b; 0, 1], by simp [Matrix.det_fin_two_of]⟩ := by
    apply sl2_ext <;> simp [sl2_inv_00, sl2_inv_01, sl2_inv_10, sl2_inv_11]
  have hu : ((up a : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) = !![1, a; 0, 1] := rfl
  unfold act
  simp only [hb, hu]
  conv_lhs => rw [Matrix.eta_fin_two X]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end Action

section Spaces

@[expose] noncomputable def Fsp : Set (Matrix (Fin 2) (Fin 2) F4) :=
  {X | ∀ s ∈ UU, act s X = X}

@[expose] noncomputable def Vone : Set (Matrix (Fin 2) (Fin 2) F4) :=
  {X | ∀ s ∈ UU, act s X - X ∈ Fsp}

theorem mem_UU_iff {g : Pr} : g ∈ UU ↔ g.1 ∈ U F4 ∧ g.2 ∈ U F4 := Subgroup.mem_prod

theorem mem_Fsp_iff {X : Matrix (Fin 2) (Fin 2) F4} :
    X ∈ Fsp ↔ X 0 0 = 0 ∧ X 1 0 = 0 ∧ X 1 1 = 0 := by
  constructor
  · intro h
    have h1 := h (up 1, up 0) (mem_UU_iff.mpr ⟨up_mem_U _, up_mem_U _⟩)
    have h2 := h (up 0, up 1) (mem_UU_iff.mpr ⟨up_mem_U _, up_mem_U _⟩)
    rw [act_up] at h1 h2
    have e1 := congrFun (congrFun h1 0) 0
    have e2 := congrFun (congrFun h1 0) 1
    have e3 := congrFun (congrFun h2 0) 1
    simp at e1 e2 e3
    exact ⟨e3, e1, e2⟩
  · rintro ⟨h0, h1, h2⟩ s hs
    obtain ⟨hs1, hs2⟩ := mem_UU_iff.mp hs
    have hs' : s = (up (s.1 0 1), up (s.2 0 1)) :=
      Prod.ext (eq_up_of_mem_U hs1) (eq_up_of_mem_U hs2)
    rw [hs', act_up]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

theorem mem_Vone_iff {X : Matrix (Fin 2) (Fin 2) F4} : X ∈ Vone ↔ X 1 0 = 0 := by
  constructor
  · intro h
    have h1 := (mem_Fsp_iff.mp (h (up 1, up 1) (mem_UU_iff.mpr ⟨up_mem_U _, up_mem_U _⟩))).1
    rw [act_up] at h1
    simpa using h1
  · intro h s hs
    obtain ⟨hs1, hs2⟩ := mem_UU_iff.mp hs
    have hs' : s = (up (s.1 0 1), up (s.2 0 1)) :=
      Prod.ext (eq_up_of_mem_U hs1) (eq_up_of_mem_U hs2)
    rw [hs', act_up]
    refine mem_Fsp_iff.mpr ⟨?_, ?_, ?_⟩ <;> simp [h]

end Spaces

section Borel

theorem UU_le_BB : UU ≤ BB := Subgroup.le_normalizer

theorem mem_BB_iff {g : Pr} : g ∈ BB ↔ g.1 1 0 = 0 ∧ g.2 1 0 = 0 := by
  constructor
  · intro hg
    have hn := Subgroup.mem_normalizer_iff.mp hg
    have h1 : g.1 ∈ Subgroup.normalizer ((U F4 : Subgroup SL(2, F4)) : Set SL(2, F4)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := hn (h, 1)
      rw [mem_UU_iff, mem_UU_iff] at this
      simpa using this
    have h2 : g.2 ∈ Subgroup.normalizer ((U F4 : Subgroup SL(2, F4)) : Set SL(2, F4)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := hn (1, h)
      rw [mem_UU_iff, mem_UU_iff] at this
      simpa using this
    exact ⟨entry10_of_mem_normalizer h1, entry10_of_mem_normalizer h2⟩
  · rintro ⟨h1, h2⟩
    have n1 := Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_entry10 h1)
    have n2 := Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_entry10 h2)
    show g ∈ Subgroup.normalizer ((UU : Subgroup Pr) : Set Pr)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [mem_UU_iff, mem_UU_iff]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    rw [n1 h.1, n2 h.2]

theorem coe_inv_sl2 (g : SL(2, F4)) :
    ((g⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact sl2_inv_00 g
  · exact sl2_inv_01 g
  · exact sl2_inv_10 g
  · exact sl2_inv_11 g

theorem act_BB {b : Pr} (hb : b ∈ BB) (X : Matrix (Fin 2) (Fin 2) F4) :
    act b X = !![(b.1 0 0 * X 0 0 + b.1 0 1 * X 1 0) * b.2 1 1,
        -((b.1 0 0 * X 0 0 + b.1 0 1 * X 1 0) * b.2 0 1) +
          (b.1 0 0 * X 0 1 + b.1 0 1 * X 1 1) * b.2 0 0;
        b.1 1 1 * X 1 0 * b.2 1 1,
        -(b.1 1 1 * X 1 0 * b.2 0 1) + b.1 1 1 * X 1 1 * b.2 0 0] := by
  obtain ⟨hb1, hb2⟩ := mem_BB_iff.mp hb
  unfold act
  rw [coe_inv_sl2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb1, hb2]

theorem act_BB_00 {b : Pr} (hb : b ∈ BB) (X : Matrix (Fin 2) (Fin 2) F4) :
    act b X 0 0 = (b.1 0 0 * X 0 0 + b.1 0 1 * X 1 0) * b.2 1 1 := by
  rw [act_BB hb]
  rfl

theorem act_BB_01 {b : Pr} (hb : b ∈ BB) (X : Matrix (Fin 2) (Fin 2) F4) :
    act b X 0 1 = -((b.1 0 0 * X 0 0 + b.1 0 1 * X 1 0) * b.2 0 1) +
      (b.1 0 0 * X 0 1 + b.1 0 1 * X 1 1) * b.2 0 0 := by
  rw [act_BB hb]
  rfl

theorem act_BB_10 {b : Pr} (hb : b ∈ BB) (X : Matrix (Fin 2) (Fin 2) F4) :
    act b X 1 0 = b.1 1 1 * X 1 0 * b.2 1 1 := by
  rw [act_BB hb]
  rfl

theorem act_BB_11 {b : Pr} (hb : b ∈ BB) (X : Matrix (Fin 2) (Fin 2) F4) :
    act b X 1 1 = -(b.1 1 1 * X 1 0 * b.2 0 1) + b.1 1 1 * X 1 1 * b.2 0 0 := by
  rw [act_BB hb]
  rfl

end Borel

section Diag

@[expose] noncomputable def diagFst : ↥BB →* F4ˣ where
  toFun b := Units.mk0 ((b : Pr).1 0 0) (fun h0 => by
    have := sl2_diag_mul (mem_BB_iff.mp b.2).1
    rw [h0, zero_mul] at this
    exact zero_ne_one this)
  map_one' := by
    ext
    simp
  map_mul' b b' := by
    ext
    simp [sl2_mul_00, (mem_BB_iff.mp b'.2).1]

@[expose] noncomputable def diagSnd : ↥BB →* F4ˣ where
  toFun b := Units.mk0 ((b : Pr).2 0 0) (fun h0 => by
    have := sl2_diag_mul (mem_BB_iff.mp b.2).2
    rw [h0, zero_mul] at this
    exact zero_ne_one this)
  map_one' := by
    ext
    simp
  map_mul' b b' := by
    ext
    simp [sl2_mul_00, (mem_BB_iff.mp b'.2).2]

@[expose] noncomputable def diagPair : ↥BB →* F4ˣ × F4ˣ := diagFst.prod diagSnd

theorem diagPair_fst (b : ↥BB) : (((diagPair b).1 : F4ˣ) : F4) = (b : Pr).1 0 0 := rfl

theorem diagPair_snd (b : ↥BB) : (((diagPair b).2 : F4ˣ) : F4) = (b : Pr).2 0 0 := rfl

theorem ker_diagPair : diagPair.ker = UU.subgroupOf BB := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_UU_iff, mem_U_iff, mem_U_iff]
  obtain ⟨h1, h2⟩ := mem_BB_iff.mp b.2
  have d1 := sl2_diag_mul h1
  have d2 := sl2_diag_mul h2
  constructor
  · intro h
    have e1 : (b : Pr).1 0 0 = 1 := by
      have := congrArg (fun q : F4ˣ × F4ˣ => ((q.1 : F4ˣ) : F4)) h
      rw [← diagPair_fst]
      simpa using this
    have e2 : (b : Pr).2 0 0 = 1 := by
      have := congrArg (fun q : F4ˣ × F4ˣ => ((q.2 : F4ˣ) : F4)) h
      rw [← diagPair_snd]
      simpa using this
    refine ⟨⟨e1, h1, ?_⟩, ⟨e2, h2, ?_⟩⟩
    · rw [e1, one_mul] at d1
      exact d1
    · rw [e2, one_mul] at d2
      exact d2
  · rintro ⟨⟨e1, -, -⟩, ⟨e2, -, -⟩⟩
    exact Prod.ext (Units.ext (by rw [diagPair_fst]; exact e1))
      (Units.ext (by rw [diagPair_snd]; exact e2))

theorem diagPair_surjective : Function.Surjective diagPair := fun q =>
  ⟨⟨(dg (q.1 : F4) q.1.ne_zero, dg (q.2 : F4) q.2.ne_zero), mem_BB_iff.mpr ⟨rfl, rfl⟩⟩,
    Prod.ext (Units.ext (by rw [diagPair_fst]; rfl)) (Units.ext (by rw [diagPair_snd]; rfl))⟩

end Diag

section Lines

theorem exists_unit_sq (δ : F4ˣ) : ∃ c : F4ˣ, c ^ 2 = δ := by
  have : Fintype F4 := Fintype.ofFinite F4
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F4 2) (δ : F4)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr, sq])⟩

@[expose] noncomputable def q1hom : F4ˣ →* F4ˣ × F4ˣ := (MonoidHom.id F4ˣ).prod invMonoidHom

@[expose] noncomputable def q2hom : F4ˣ →* F4ˣ × F4ˣ := (MonoidHom.id F4ˣ).prod (MonoidHom.id F4ˣ)

@[expose] noncomputable def Q1 : Subgroup (F4ˣ × F4ˣ) := q1hom.range

@[expose] noncomputable def Q2 : Subgroup (F4ˣ × F4ˣ) := q2hom.range

theorem card_units_f4 : Nat.card F4ˣ = 3 := by
  rw [Nat.card_units, GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem q1hom_injective : Function.Injective q1hom := fun _ _ h => congrArg Prod.fst h

theorem q2hom_injective : Function.Injective q2hom := fun _ _ h => congrArg Prod.fst h

theorem card_Q1 : Nat.card Q1 = 3 := by
  rw [Q1, ← card_units_f4]
  exact (Nat.card_congr (MonoidHom.ofInjective q1hom_injective).toEquiv).symm

theorem card_Q2 : Nat.card Q2 = 3 := by
  rw [Q2, ← card_units_f4]
  exact (Nat.card_congr (MonoidHom.ofInjective q2hom_injective).toEquiv).symm

theorem Q1_sup_Q2 : Q1 ⊔ Q2 = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, c⟩ -
  obtain ⟨a₂, ha₂⟩ := exists_unit_sq (a * c)
  have e : (a, c) = (a * a₂⁻¹, (a * a₂⁻¹)⁻¹) * (a₂, a₂) := by
    refine Prod.ext (by simp) ?_
    show c = (a * a₂⁻¹)⁻¹ * a₂
    calc c = a⁻¹ * (a * c) := by group
      _ = a⁻¹ * (a₂ * a₂) := by rw [← sq, ha₂]
      _ = (a * a₂⁻¹)⁻¹ * a₂ := by
        rw [_root_.mul_inv_rev, inv_inv, mul_comm a₂ a⁻¹, mul_assoc]
  rw [e]
  exact Subgroup.mul_mem_sup ⟨a * a₂⁻¹, rfl⟩ ⟨a₂, rfl⟩

theorem mem_Q1_iff {q : F4ˣ × F4ˣ} : q ∈ Q1 ↔ q.1 * q.2 = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [q1hom]
  · intro h
    refine ⟨q.1, Prod.ext rfl ?_⟩
    show q.1⁻¹ = q.2
    exact inv_eq_of_mul_eq_one_right h

theorem mem_Q2_iff {q : F4ˣ × F4ˣ} : q ∈ Q2 ↔ q.1 = q.2 := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro h
    exact ⟨q.1, Prod.ext rfl h⟩

@[expose] noncomputable def Y1' : Subgroup ↥BB := Q1.comap diagPair

@[expose] noncomputable def Y2' : Subgroup ↥BB := Q2.comap diagPair

theorem UU_le_Y1' : UU.subgroupOf BB ≤ Y1' := by
  rw [← ker_diagPair]
  exact MonoidHom.ker_le_comap _ _

theorem UU_le_Y2' : UU.subgroupOf BB ≤ Y2' := by
  rw [← ker_diagPair]
  exact MonoidHom.ker_le_comap _ _

theorem relIndex_Y1' : (UU.subgroupOf BB).relIndex Y1' = 3 := by
  rw [relIndex_eq_relIndex_map diagPair UU_le_Y1' (fun k hk h1 => by
      rw [← ker_diagPair]
      exact h1)]
  have h1 : (UU.subgroupOf BB).map diagPair = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (le_of_eq ker_diagPair.symm)
  have h2 : Y1'.map diagPair = Q1 :=
    Subgroup.map_comap_eq_self_of_surjective diagPair_surjective Q1
  rw [h1, h2, Subgroup.relIndex_bot_left, card_Q1]

theorem relIndex_Y2' : (UU.subgroupOf BB).relIndex Y2' = 3 := by
  rw [relIndex_eq_relIndex_map diagPair UU_le_Y2' (fun k hk h1 => by
      rw [← ker_diagPair]
      exact h1)]
  have h1 : (UU.subgroupOf BB).map diagPair = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (le_of_eq ker_diagPair.symm)
  have h2 : Y2'.map diagPair = Q2 :=
    Subgroup.map_comap_eq_self_of_surjective diagPair_surjective Q2
  rw [h1, h2, Subgroup.relIndex_bot_left, card_Q2]

theorem Y1'_sup_Y2' : Y1' ⊔ Y2' = ⊤ := by
  have hker : diagPair.ker ≤ Y1' ⊔ Y2' := by
    rw [ker_diagPair]
    exact UU_le_Y1'.trans le_sup_left
  have hmap : Q1 ⊔ Q2 ≤ (Y1' ⊔ Y2').map diagPair := by
    refine sup_le ?_ ?_
    · rw [← Subgroup.map_comap_eq_self_of_surjective diagPair_surjective Q1]
      exact Subgroup.map_mono le_sup_left
    · rw [← Subgroup.map_comap_eq_self_of_surjective diagPair_surjective Q2]
      exact Subgroup.map_mono le_sup_right
  have h2 : ((Y1' ⊔ Y2').map diagPair).comap diagPair = (Y1' ⊔ Y2') ⊔ diagPair.ker :=
    Subgroup.comap_map_eq _ _
  have hmap' : (Y1' ⊔ Y2').map diagPair = ⊤ := by
    rw [eq_top_iff, ← Q1_sup_Q2]
    exact hmap
  rw [hmap', Subgroup.comap_top, sup_eq_left.mpr hker] at h2
  exact h2.symm

@[expose] noncomputable def Y1 : Subgroup Pr := Y1'.map BB.subtype

@[expose] noncomputable def Y2 : Subgroup Pr := Y2'.map BB.subtype

theorem UU_le_Y1 : UU ≤ Y1 := by
  have := Subgroup.map_mono (f := BB.subtype) UU_le_Y1'
  rwa [Subgroup.map_subgroupOf_eq_of_le UU_le_BB] at this

theorem UU_le_Y2 : UU ≤ Y2 := by
  have := Subgroup.map_mono (f := BB.subtype) UU_le_Y2'
  rwa [Subgroup.map_subgroupOf_eq_of_le UU_le_BB] at this

theorem Y1_le_BB : Y1 ≤ BB := by
  rintro _ ⟨b, -, rfl⟩
  exact b.2

theorem Y2_le_BB : Y2 ≤ BB := by
  rintro _ ⟨b, -, rfl⟩
  exact b.2

theorem relIndex_Y1 : UU.relIndex Y1 = 3 := by
  have h := Subgroup.relIndex_map_map_of_injective (UU.subgroupOf BB) Y1' BB.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le UU_le_BB] at h
  rw [Y1, h, relIndex_Y1']

theorem relIndex_Y2 : UU.relIndex Y2 = 3 := by
  have h := Subgroup.relIndex_map_map_of_injective (UU.subgroupOf BB) Y2' BB.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le UU_le_BB] at h
  rw [Y2, h, relIndex_Y2']

theorem BB_le_sup : BB ≤ Y1 ⊔ Y2 := by
  have h : (Y1' ⊔ Y2').map BB.subtype = Y1 ⊔ Y2 := Subgroup.map_sup _ _ _
  rw [← h, Y1'_sup_Y2', Subgroup.map_top, Subgroup.range_subtype]

theorem mem_Y1_iff {b : Pr} : b ∈ Y1 ↔ b ∈ BB ∧ b.1 0 0 * b.2 0 0 = 1 := by
  constructor
  · rintro ⟨b', hb', rfl⟩
    refine ⟨b'.2, ?_⟩
    have h := (mem_Q1_iff.mp (Subgroup.mem_comap.mp hb'))
    have := congrArg (fun u : F4ˣ => (u : F4)) h
    simpa [diagPair_fst, diagPair_snd] using this
  · rintro ⟨hb, h⟩
    refine ⟨⟨b, hb⟩, Subgroup.mem_comap.mpr (mem_Q1_iff.mpr (Units.ext ?_)), rfl⟩
    simpa [diagPair_fst, diagPair_snd] using h

theorem mem_Y2_iff {b : Pr} : b ∈ Y2 ↔ b ∈ BB ∧ b.1 0 0 = b.2 0 0 := by
  constructor
  · rintro ⟨b', hb', rfl⟩
    refine ⟨b'.2, ?_⟩
    have h := (mem_Q2_iff.mp (Subgroup.mem_comap.mp hb'))
    have := congrArg (fun u : F4ˣ => (u : F4)) h
    simpa [diagPair_fst, diagPair_snd] using this
  · rintro ⟨hb, h⟩
    refine ⟨⟨b, hb⟩, Subgroup.mem_comap.mpr (mem_Q2_iff.mpr (Units.ext ?_)), rfl⟩
    simpa [diagPair_fst, diagPair_snd] using h

theorem mem_Y1_iff_act {b : Pr} (hb : b ∈ BB) : b ∈ Y1 ↔ ∀ y ∈ Fsp, act b y = y := by
  rw [mem_Y1_iff]
  constructor
  · rintro ⟨-, hac⟩ y hy
    obtain ⟨hy0, hy1, hy2⟩ := mem_Fsp_iff.mp hy
    ext i j
    fin_cases i <;> fin_cases j
    · show act b y 0 0 = y 0 0
      rw [act_BB_00 hb, hy0, hy1]
      ring
    · show act b y 0 1 = y 0 1
      rw [act_BB_01 hb, hy0, hy1, hy2]
      linear_combination (y 0 1) * hac
    · show act b y 1 0 = y 1 0
      rw [act_BB_10 hb, hy1]
      ring
    · show act b y 1 1 = y 1 1
      rw [act_BB_11 hb, hy1, hy2]
      ring
  · intro h
    refine ⟨hb, ?_⟩
    have hy : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F4) ∈ Fsp :=
      mem_Fsp_iff.mpr ⟨by simp, by simp, by simp⟩
    have h1 := congrFun (congrFun (h _ hy) 0) 1
    rw [act_BB_01 hb] at h1
    simpa using h1

theorem mem_Y2_iff_act {b : Pr} (hb : b ∈ BB) :
    b ∈ Y2 ↔ ∀ X ∈ Vone, act b X - X ∈ Fsp := by
  rw [mem_Y2_iff]
  obtain ⟨hb1, hb2⟩ := mem_BB_iff.mp hb
  have d1 := sl2_diag_mul hb1
  have d2 := sl2_diag_mul hb2
  constructor
  · rintro ⟨-, hac⟩ X hX
    have hX1 := mem_Vone_iff.mp hX
    refine mem_Fsp_iff.mpr ⟨?_, ?_, ?_⟩
    · rw [Matrix.sub_apply, act_BB_00 hb, hX1]
      linear_combination (X 0 0) * d2 + (X 0 0 * b.2 1 1) * hac
    · rw [Matrix.sub_apply, act_BB_10 hb, hX1]
      ring
    · rw [Matrix.sub_apply, act_BB_11 hb, hX1]
      linear_combination (X 1 1) * d1 - (X 1 1 * b.1 1 1) * hac
  · intro h
    refine ⟨hb, ?_⟩
    have hX : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F4) ∈ Vone :=
      mem_Vone_iff.mpr (by simp)
    have h0 := (mem_Fsp_iff.mp (h _ hX)).1
    rw [Matrix.sub_apply, act_BB_00 hb] at h0
    have e : b.1 0 0 * b.2 1 1 = 1 := by
      simp at h0
      linear_combination h0
    calc b.1 0 0 = b.1 0 0 * (b.2 0 0 * b.2 1 1) := by rw [d2, mul_one]
      _ = (b.1 0 0 * b.2 1 1) * b.2 0 0 := by ring
      _ = b.2 0 0 := by rw [e, one_mul]

end Lines

end L28

end SzPS8

end CFSG.Quasithin
