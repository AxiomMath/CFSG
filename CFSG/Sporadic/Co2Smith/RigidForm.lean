module

public import CFSG.Sporadic.Co2Smith.RigidFrame

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u

@[expose] def J7 (a b : Fin 8) : ZMod 2 := if a.val + b.val = 7 then 1 else 0

namespace LocalConfig

variable (c : LocalConfig.{u})

theorem exists_zE :
    ∃ z ∈ Subgroup.center c.E, z ≠ 1 ∧
    ∀ e ∈ Subgroup.center c.E, e = 1 ∨ e = z := by
  obtain ⟨⟨z, hz⟩, hne, huniq⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.center c.E)).mp c.center_structure.1
  refine ⟨z, hz, fun h => hne (Subtype.ext h), fun e he => ?_⟩
  by_cases h1 : e = 1
  · exact Or.inl h1
  · exact Or.inr (congrArg Subtype.val (huniq ⟨e, he⟩ fun h => h1 (congrArg Subtype.val h)))

@[expose] noncomputable def zE :
    c.E := c.exists_zE.choose

theorem zE_ne_one :
    c.zE ≠ 1 := c.exists_zE.choose_spec.2.1

theorem zE_mem_center :
    c.zE ∈ Subgroup.center c.E := c.exists_zE.choose_spec.1

theorem mem_center_iff
    (e : c.E) : e ∈ Subgroup.center c.E ↔ e = 1 ∨ e = c.zE := by
  refine ⟨c.exists_zE.choose_spec.2.2 e, ?_⟩
  rintro (rfl | rfl)
  · exact Subgroup.one_mem _
  · exact c.zE_mem_center

theorem zE_comm
    (e : c.E) : e * c.zE = c.zE * e :=
  (Subgroup.mem_center_iff.mp c.zE_mem_center e)

theorem zE_sq :
    c.zE * c.zE = 1 := by
  have h2 : (⟨c.zE, c.zE_mem_center⟩ : Subgroup.center c.E) ^ 2 = 1 := by
    rw [← c.center_structure.1]
    exact pow_card_eq_one'
  have := congrArg Subtype.val h2
  rwa [Subgroup.coe_pow, sq] at this

theorem cE_zE
    (h : c.H) : c.cE h c.zE = c.zE := by
  have hmem : c.cE h c.zE ∈ Subgroup.center c.E := char_mem _ (c.cE h) c.zE_mem_center
  rcases (c.mem_center_iff _).mp hmem with h1 | h1
  · exact absurd ((c.cE h).injective (h1.trans (map_one _).symm)) c.zE_ne_one
  · exact h1

theorem zpow_val_mul
    (a b : ZMod 2) : c.zE ^ (a + b).val = c.zE ^ a.val * c.zE ^ b.val :=
  pow_val_add c.zE_sq a b

theorem zpow_val_inj
    {a b : ZMod 2} (h : c.zE ^ a.val = c.zE ^ b.val) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [ZMod.val_zero, val_one_two, pow_zero, pow_one] at h
    exact absurd h.symm c.zE_ne_one
  · rw [ZMod.val_zero, val_one_two, pow_zero, pow_one] at h
    exact absurd h c.zE_ne_one
  · rfl

open scoped Classical in
@[expose] noncomputable def cf (e e' : c.E) : ZMod 2 := if e * e' = e' * e then 0 else 1

theorem comm_eq
    (e e' : c.E) : e * e' = e' * e * c.zE ^ (c.cf e e').val := by
  unfold cf
  split_ifs with h
  · rw [ZMod.val_zero, pow_zero, mul_one, h]
  · have hc := c.center_structure.2.1 e e'
    rcases (c.mem_center_iff _).mp hc with h1 | h1
    · exact absurd (by rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1; exact h1) h
    · rw [val_one_two, pow_one, c.zE_comm (e' * e), ← h1]
      group

theorem cf_eq_of
    {e e' : c.E} {a : ZMod 2} (h : e * e' = e' * e * c.zE ^ a.val) :
    c.cf e e' = a :=
  c.zpow_val_inj (mul_left_cancel ((c.comm_eq e e').symm.trans h))

theorem zpow_comm
    (a : ZMod 2) (e : c.E) : e * c.zE ^ a.val = c.zE ^ a.val * e :=
  (Commute.pow_right (c.zE_comm e) _).eq

theorem cf_mul_left
    (e₁ e₂ e' : c.E) : c.cf (e₁ * e₂) e' = c.cf e₁ e' + c.cf e₂ e' := by
  apply c.cf_eq_of
  rw [c.zpow_val_mul]
  have h2 := c.comm_eq e₂ e'
  have h1 := c.comm_eq e₁ e'
  have hz := c.zpow_comm (c.cf e₁ e') e₂
  calc e₁ * e₂ * e' = e₁ * (e₂ * e') := mul_assoc _ _ _
    _ = e₁ * (e' * e₂ * c.zE ^ (c.cf e₂ e').val) := by rw [h2]
    _ = (e₁ * e') * e₂ * c.zE ^ (c.cf e₂ e').val := by simp only [mul_assoc]
    _ = (e' * e₁ * c.zE ^ (c.cf e₁ e').val) * e₂ * c.zE ^ (c.cf e₂ e').val := by rw [h1]
    _ = e' * e₁ * (c.zE ^ (c.cf e₁ e').val * e₂) * c.zE ^ (c.cf e₂ e').val := by
        simp only [mul_assoc]
    _ = e' * e₁ * (e₂ * c.zE ^ (c.cf e₁ e').val) * c.zE ^ (c.cf e₂ e').val := by rw [hz]
    _ = e' * (e₁ * e₂) * (c.zE ^ (c.cf e₁ e').val * c.zE ^ (c.cf e₂ e').val) := by
        simp only [mul_assoc]

theorem cf_symm
    (e e' : c.E) : c.cf e e' = c.cf e' e := by
  unfold cf
  by_cases h : e * e' = e' * e
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

theorem cf_z_left
    (e : c.E) : c.cf c.zE e = 0 := by
  unfold cf
  rw [ite_eq_left (c.zE_comm e).symm]

theorem cf_cE
    (h : c.H) (e e' : c.E) : c.cf (c.cE h e) (c.cE h e') = c.cf e e' := by
  unfold cf
  by_cases hc : e * e' = e' * e
  · rw [ite_eq_left hc, ite_eq_left (by rw [← map_mul, hc, map_mul])]
  · rw [ite_eq_right hc,
      ite_eq_right fun h' => hc ((c.cE h).injective (by rw [map_mul, map_mul, h']))]

theorem cf_of_center
    {e e₁ : c.E} (he : e₁ ∈ Subgroup.center c.E) (e' : c.E) :
    c.cf (e * e₁) e' = c.cf e e' := by
  rcases (c.mem_center_iff _).mp he with rfl | rfl
  · rw [mul_one]
  · rw [c.cf_mul_left, c.cf_z_left, add_zero]

@[expose] noncomputable def lift (m : c.M) : c.E := Quotient.out m

theorem piM_lift
    (m : c.M) : c.piM (c.lift m) = m := Quotient.out_eq m

theorem lift_piM
    (e : c.E) : ∃ k ∈ Subgroup.center c.E, c.lift (c.piM e) = e * k := by
  refine ⟨e⁻¹ * c.lift (c.piM e), ?_, by group⟩
  rw [← QuotientGroup.eq]
  exact (c.piM_lift (c.piM e)).symm

@[expose] noncomputable def Bm (m m' : c.M) : ZMod 2 := c.cf (c.lift m) (c.lift m')

theorem Bm_piM
    (e e' : c.E) : c.Bm (c.piM e) (c.piM e') = c.cf e e' := by
  obtain ⟨k, hk, hke⟩ := c.lift_piM e
  obtain ⟨k', hk', hke'⟩ := c.lift_piM e'
  rw [Bm, hke, hke', c.cf_of_center hk, c.cf_symm, c.cf_of_center hk', c.cf_symm]

theorem Bm_mul_left
    (m₁ m₂ m' : c.M) : c.Bm (m₁ * m₂) m' = c.Bm m₁ m' + c.Bm m₂ m' := by
  obtain ⟨e₁, rfl⟩ := c.piM_surjective m₁
  obtain ⟨e₂, rfl⟩ := c.piM_surjective m₂
  obtain ⟨e', rfl⟩ := c.piM_surjective m'
  rw [← map_mul, c.Bm_piM, c.Bm_piM, c.Bm_piM, c.cf_mul_left]

theorem Bm_symm
    (m m' : c.M) : c.Bm m m' = c.Bm m' m := by
  rw [Bm, Bm, c.cf_symm]

theorem Bm_mul_right
    (m m₁ m₂ : c.M) : c.Bm m (m₁ * m₂) = c.Bm m m₁ + c.Bm m m₂ := by
  rw [c.Bm_symm, c.Bm_mul_left, c.Bm_symm m₁, c.Bm_symm m₂]

theorem Bm_mA
    (g : S0) (m m' : c.M) : c.Bm (c.mA g m) (c.mA g m') = c.Bm m m' := by
  obtain ⟨e, rfl⟩ := c.piM_surjective m
  obtain ⟨e', rfl⟩ := c.piM_surjective m'
  rw [c.mA_piM, c.mA_piM, c.Bm_piM, c.Bm_piM, c.cf_cE]

theorem Bm_y_left
    {k : ℕ} (hk : k = 0 ∨ k = 2 ∨ k = 4) (m m' : c.M) :
    c.Bm (c.mA (frS k) m) m' = c.Bm m (c.mA (frS k) (c.mA (frS k) m')) := by
  conv_lhs => rw [← c.mA_y3 k hk m']
  rw [c.Bm_mA]

theorem add_eq_self {x y : ZMod 2} (h : x + y = y) : x = 0 := by
  rcases zmod_two_cases x with rfl | rfl <;> rcases zmod_two_cases y with rfl | rfl <;>
    first | rfl | exact absurd h (by decide)

theorem F1_0
    (a1 a2 c1 c2 : Bool) : c.Bm (c.vv false a1 a2) (c.vv false c1 c2) = 0 := by
  have h := c.Bm_mA (frS 1) (c.vv true a1 a2) (c.vv false c1 c2)
  rw [c.s1_vv, c.s1_vv] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [c.Bm_mul_left] at h
  exact add_eq_self h

theorem F1_1
    (a0 a2 c0 c2 : Bool) : c.Bm (c.vv a0 false a2) (c.vv c0 false c2) = 0 := by
  have h := c.Bm_mA (frS 3) (c.vv a0 true a2) (c.vv c0 false c2)
  rw [c.s2_vv, c.s2_vv] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [c.Bm_mul_left] at h
  exact add_eq_self h

theorem F1_2
    (a0 a1 c0 c1 : Bool) : c.Bm (c.vv a0 a1 false) (c.vv c0 c1 false) = 0 := by
  have h := c.Bm_mA (frS 5) (c.vv a0 a1 true) (c.vv c0 c1 false)
  rw [c.s3_vv, c.s3_vv] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [c.Bm_mul_left] at h
  exact add_eq_self h

theorem F2_0
    (a1 a2 c1 c2 : Bool) : c.Bm (c.vv true a1 a2) (c.vv true c1 c2) = 0 := by
  have h := c.Bm_mA (frS 0) (c.vv false a1 a2) (c.vv false c1 c2)
  rw [c.y1_vv, c.y1_vv] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [h, c.F1_0]

theorem F2_1
    (a0 a2 c0 c2 : Bool) : c.Bm (c.vv a0 true a2) (c.vv c0 true c2) = 0 := by
  have h := c.Bm_mA (frS 2) (c.vv a0 false a2) (c.vv c0 false c2)
  rw [c.y2_vv, c.y2_vv] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [h, c.F1_1]

theorem F2_2
    (a0 a1 c0 c1 : Bool) : c.Bm (c.vv a0 a1 true) (c.vv c0 c1 true) = 0 := by
  have h := c.Bm_mA (frS 4) (c.vv a0 a1 false) (c.vv c0 c1 false)
  rw [c.y3_vv, c.y3_vv] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  rw [h, c.F1_2]

theorem F4_0
    (a1 a2 c1 c2 : Bool) :
    c.Bm (c.vv true a1 a2) (c.vv false c1 c2) = c.Bm (c.vv false a1 a2) (c.vv true c1 c2) := by
  have h1 : c.vv true a1 a2 = c.mA (frS 0) (c.vv false a1 a2) := rfl
  have h2 : c.mA (frS 0) (c.mA (frS 0) (c.vv false c1 c2)) =
      c.vv false c1 c2 * c.vv true c1 c2 := c.yy0 _
  rw [h1, c.Bm_y_left (Or.inl rfl), h2, c.Bm_mul_right, c.F1_0, zero_add]

theorem F4_1
    (a0 a2 c0 c2 : Bool) :
    c.Bm (c.vv a0 true a2) (c.vv c0 false c2) = c.Bm (c.vv a0 false a2) (c.vv c0 true c2) := by
  have h1 : c.vv a0 true a2 = c.mA (frS 2) (c.vv a0 false a2) := by
    rw [c.y2_vv]
    rfl
  have h2 : c.mA (frS 2) (c.mA (frS 2) (c.vv c0 false c2)) =
      c.vv c0 false c2 * c.vv c0 true c2 := by
    have := c.y2_vv c0 false c2
    simp only [↓reduceIte, Bool.false_eq_true] at this
    rw [this, c.y2_vv]
    rfl
  rw [h1, c.Bm_y_left (Or.inr (Or.inl rfl)), h2, c.Bm_mul_right, c.F1_1, zero_add]

theorem F4_2
    (a0 a1 c0 c1 : Bool) :
    c.Bm (c.vv a0 a1 true) (c.vv c0 c1 false) = c.Bm (c.vv a0 a1 false) (c.vv c0 c1 true) := by
  have h1 : c.vv a0 a1 true = c.mA (frS 4) (c.vv a0 a1 false) := by
    rw [c.y3_vv]
    rfl
  have h2 : c.mA (frS 4) (c.mA (frS 4) (c.vv c0 c1 false)) =
      c.vv c0 c1 false * c.vv c0 c1 true := by
    have := c.y3_vv c0 c1 false
    simp only [↓reduceIte, Bool.false_eq_true] at this
    rw [this, c.y3_vv]
    rfl
  rw [h1, c.Bm_y_left (Or.inr (Or.inr rfl)), h2, c.Bm_mul_right, c.F1_2, zero_add]

@[expose] noncomputable def β0 :
    ZMod 2 := c.Bm (c.vv false false false) (c.vv true true true)

theorem Bm_vv
    (e0 e1 e2 f0 f1 f2 : Bool) : c.Bm (c.vv e0 e1 e2) (c.vv f0 f1 f2) =
    if e0 ≠ f0 ∧ e1 ≠ f1 ∧ e2 ≠ f2 then c.β0 else 0 := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases f0 <;> cases f1 <;> cases f2 <;>
    simp [β0, c.F1_0, c.F1_1, c.F1_2, c.F2_0, c.F2_1, c.F2_2, c.F4_0, c.F4_1, c.F4_2]

end LocalConfig

end CFSG.Sporadic.Co2Smith
