module

public import CFSG.RankThree.GF2n.SzExplicit
import CFSG.RankThree.S4Free.StellmacherSzSylow
import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
import CFSG.LieType.Ree.SuzukiOrder

public section

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit Matrix Subgroup

namespace CFSG.RankThree.S4Free.SzNatural

variable (n : ℕ)

private theorem rootMat_eq_transpose (u v : F n) :
    rootMat n u v = (CFSG.Blueprint.suzukiS n u v)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMat, CFSG.Blueprint.suzukiS, CFSG.Blueprint.suzukiN, add_comm, pow_add]

theorem card_F : Nat.card (F n) = 2 ^ (2 * n + 1) :=
  GaloisField.card 2 (2 * n + 1) (by omega)

theorem rootMat_mul (u v c d : F n) :
    rootMat n u v * rootMat n c d = rootMat n (u + c) (v + d + c ^ 2 ^ (n + 1) * u) := by
  rw [rootMat_eq_transpose, rootMat_eq_transpose, rootMat_eq_transpose, ← transpose_mul,
    (CFSG.LieType.Ree.suzuki_unipotent_product n (card_F n)).1 c d u v]
  congr 2
  · ring
  · ring

theorem rootMat_zero_zero : rootMat n 0 0 = 1 := by
  rw [rootMat_eq_transpose, (CFSG.LieType.Ree.suzuki_unipotent_product n (card_F n)).2.2.2.2.1,
    transpose_one]

theorem rootMat_inj {u v c d : F n} : rootMat n u v = rootMat n c d ↔ u = c ∧ v = d := by
  rw [rootMat_eq_transpose, rootMat_eq_transpose, transpose_inj]
  exact (CFSG.LieType.Ree.suzuki_unipotent_product n (card_F n)).2.2.2.2.2 u v c d

@[expose] noncomputable def rootElt (u v : F n) : Sz n := ⟨rootGL n u v, rootGL_mem n u v⟩

theorem coe_rootElt (u v : F n) :
    (((rootElt n u v : Sz n) : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) = rootMat n u v :=
  rfl

theorem rootElt_ext {g h : Sz n}
    (e : ((g : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) =
      ((h : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n))) : g = h :=
  Subtype.ext (Units.ext e)

theorem rootElt_mul (u v c d : F n) :
    rootElt n u v * rootElt n c d = rootElt n (u + c) (v + d + c ^ 2 ^ (n + 1) * u) :=
  rootElt_ext n (rootMat_mul n u v c d)

theorem rootElt_zero_zero : rootElt n 0 0 = 1 :=
  rootElt_ext n (rootMat_zero_zero n)

theorem rootElt_inj {u v c d : F n} : rootElt n u v = rootElt n c d ↔ u = c ∧ v = d := by
  refine ⟨fun h => (rootMat_inj n).mp ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have := congrArg (fun g : Sz n => ((g : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n))) h
  simpa only [coe_rootElt] using this

theorem rootElt_inv (u v : F n) : (rootElt n u v)⁻¹ = rootElt n u (v + u ^ (2 ^ (n + 1) + 1)) := by
  have h2 : (2 : F n) = 0 := by
    have : CharP (F n) 2 := inferInstance
    exact_mod_cast CharP.cast_eq_zero (F n) 2
  rw [inv_eq_iff_mul_eq_one, rootElt_mul, ← rootElt_zero_zero, rootElt_inj]
  constructor
  · linear_combination u * h2
  · rw [pow_succ]
    linear_combination (v + u ^ 2 ^ (n + 1) * u) * h2

@[expose] noncomputable def rootSub : Subgroup (Sz n) where
  carrier := Set.range fun p : F n × F n => rootElt n p.1 p.2
  mul_mem' := by
    rintro _ _ ⟨⟨u, v⟩, rfl⟩ ⟨⟨c, d⟩, rfl⟩
    exact ⟨(u + c, v + d + c ^ 2 ^ (n + 1) * u), (rootElt_mul n u v c d).symm⟩
  one_mem' := ⟨(0, 0), rootElt_zero_zero n⟩
  inv_mem' := by
    rintro _ ⟨⟨u, v⟩, rfl⟩
    exact ⟨(u, v + u ^ (2 ^ (n + 1) + 1)), (rootElt_inv n u v).symm⟩

theorem mem_rootSub {g : Sz n} : g ∈ rootSub n ↔ ∃ u v : F n, rootElt n u v = g := by
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨u, v, rfl⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨(u, v), rfl⟩

theorem card_rootSub : Nat.card (rootSub n) = (2 ^ (2 * n + 1)) ^ 2 := by
  rw [← SetLike.coe_sort_coe, show ((rootSub n : Subgroup (Sz n)) : Set (Sz n)) =
    Set.range fun p : F n × F n => rootElt n p.1 p.2 from rfl,
    Nat.card_range_of_injective fun p p' h => Prod.ext ((rootElt_inj n).mp h).1
      ((rootElt_inj n).mp h).2, Nat.card_prod, card_F, sq]

@[expose] noncomputable def act (g : Sz n) : (Fin 4 → F n) →+ (Fin 4 → F n) where
  toFun v := ((g : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) *ᵥ v
  map_zero' := mulVec_zero _
  map_add' v w := mulVec_add _ v w

theorem act_apply (g : Sz n) (v : Fin 4 → F n) :
    act n g v = ((g : GL (Fin 4) (F n)) : Matrix (Fin 4) (Fin 4) (F n)) *ᵥ v := rfl

theorem act_mul (g h : Sz n) (v : Fin 4 → F n) : act n (g * h) v = act n g (act n h v) := by
  simp only [act_apply, Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]

theorem act_one (v : Fin 4 → F n) : act n 1 v = v := by
  simp only [act_apply, Subgroup.coe_one, Units.val_one, one_mulVec]

theorem act_inv_act (g : Sz n) (v : Fin 4 → F n) : act n g⁻¹ (act n g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : Sz n) (v : Fin 4 → F n) : act n g (act n g⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

@[expose] noncomputable def fix (T : Subgroup (Sz n)) : AddSubgroup (Fin 4 → F n) where
  carrier := {v | ∀ g ∈ T, act n g v = v}
  add_mem' hv hw g hg := by rw [map_add, hv g hg, hw g hg]
  zero_mem' g _ := map_zero _
  neg_mem' hv g hg := by rw [map_neg, hv g hg]

theorem mem_fix {T : Subgroup (Sz n)} {v : Fin 4 → F n} : v ∈ fix n T ↔ ∀ g ∈ T, act n g v = v :=
  Iff.rfl

@[expose] noncomputable def fixElt (g : Sz n) : AddSubgroup (Fin 4 → F n) :=
  (act n g - AddMonoidHom.id _).ker

theorem mem_fixElt {g : Sz n} {v : Fin 4 → F n} : v ∈ fixElt n g ↔ act n g v = v := by
  rw [fixElt, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]

@[expose] noncomputable def comm (T : Subgroup (Sz n)) (X : AddSubgroup (Fin 4 → F n)) :
    AddSubgroup (Fin 4 → F n) :=
  AddSubgroup.closure {w | ∃ g ∈ T, ∃ v ∈ X, act n g v - v = w}

@[expose] noncomputable def commElt (g : Sz n) (X : AddSubgroup (Fin 4 → F n)) :
    AddSubgroup (Fin 4 → F n) :=
  X.map (act n g - AddMonoidHom.id _)

theorem mem_commElt {g : Sz n} {X : AddSubgroup (Fin 4 → F n)} {w : Fin 4 → F n} :
    w ∈ commElt n g X ↔ ∃ v ∈ X, act n g v - v = w := by
  simp [commElt, AddSubgroup.mem_map]

@[expose] noncomputable def flag (i : ℕ) : AddSubgroup (Fin 4 → F n) where
  carrier := {v | ∀ j : Fin 4, i ≤ j.val → v j = 0}
  add_mem' hv hw j hj := by rw [Pi.add_apply, hv j hj, hw j hj, add_zero]
  zero_mem' _ _ := rfl
  neg_mem' hv j hj := by rw [Pi.neg_apply, hv j hj, neg_zero]

theorem mem_flag {i : ℕ} {v : Fin 4 → F n} : v ∈ flag n i ↔ ∀ j : Fin 4, i ≤ j.val → v j = 0 :=
  Iff.rfl

theorem mem_flag_one {v : Fin 4 → F n} : v ∈ flag n 1 ↔ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
  rw [mem_flag]
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩
  · rintro ⟨h1, h2, h3⟩ j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact h1
    · exact h2
    · exact h3

theorem mem_flag_two {v : Fin 4 → F n} : v ∈ flag n 2 ↔ v 2 = 0 ∧ v 3 = 0 := by
  rw [mem_flag]
  constructor
  · intro h
    exact ⟨h 2 (by decide), h 3 (by decide)⟩
  · rintro ⟨h2, h3⟩ j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact h2
    · exact h3

theorem mem_flag_three {v : Fin 4 → F n} : v ∈ flag n 3 ↔ v 3 = 0 := by
  rw [mem_flag]
  constructor
  · intro h
    exact h 3 (by decide)
  · rintro h3 j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact h3

theorem flag_four : flag n 4 = ⊤ := by
  rw [eq_top_iff]
  intro v _ j hj
  exact absurd hj (by omega)

theorem flag_zero : flag n 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [AddSubgroup.mem_bot]
  ext j
  exact hv j (Nat.zero_le _)

theorem act_rootElt (u w : F n) (x : Fin 4 → F n) :
    act n (rootElt n u w) x =
      ![x 0 + u * x 1 + w * x 2 + (u ^ (2 + 2 ^ (n + 1)) + u * w + w ^ (2 ^ (n + 1))) * x 3,
        x 1 + u ^ (2 ^ (n + 1)) * x 2 + (u ^ (1 + 2 ^ (n + 1)) + w) * x 3, x 2 + u * x 3, x 3] := by
  rw [act_apply, coe_rootElt, rootMat_mulVec]

theorem two_eq_zero : (2 : F n) = 0 := by
  have : CharP (F n) 2 := inferInstance
  exact_mod_cast CharP.cast_eq_zero (F n) 2

theorem zero_pow_theta : (0 : F n) ^ 2 ^ (n + 1) = 0 := zero_pow (pow_ne_zero _ two_ne_zero)

theorem fix_rootSub : fix n (rootSub n) = flag n 1 := by
  have h2 := two_eq_zero n
  ext x
  rw [mem_fix, mem_flag_one]
  constructor
  · intro h
    have h1 := h _ ((mem_rootSub n).mpr ⟨1, 0, rfl⟩)
    rw [act_rootElt] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    have e2 := congrFun h1 2
    simp [zero_pow_theta] at e0 e1 e2
    have h3 : x 3 = 0 := e2
    rw [h3, add_zero] at e1 e0
    exact ⟨by linear_combination e0, by linear_combination e1, h3⟩
  · rintro ⟨h1, h2', h3⟩ g hg
    obtain ⟨u, w, rfl⟩ := (mem_rootSub n).mp hg
    rw [act_rootElt]
    ext j
    fin_cases j <;> simp [h1, h2', h3]

@[expose] noncomputable def rootCenter : Subgroup (Sz n) where
  carrier := Set.range fun w : F n => rootElt n 0 w
  mul_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    refine ⟨w + w', ?_⟩
    rw [rootElt_mul, add_zero, mul_zero, add_zero]
  one_mem' := ⟨0, rootElt_zero_zero n⟩
  inv_mem' := by
    rintro _ ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    rw [rootElt_inv, zero_pow (by positivity), add_zero]

theorem mem_rootCenter {g : Sz n} : g ∈ rootCenter n ↔ ∃ w : F n, rootElt n 0 w = g :=
  Iff.rfl

theorem rootCenter_le : rootCenter n ≤ rootSub n := by
  rintro _ ⟨w, rfl⟩
  exact (mem_rootSub n).mpr ⟨0, w, rfl⟩

theorem fix_rootCenter : fix n (rootCenter n) = flag n 2 := by
  have h2 := two_eq_zero n
  ext x
  rw [mem_fix, mem_flag_two]
  constructor
  · intro h
    have h1 := h _ ((mem_rootCenter n).mpr ⟨1, rfl⟩)
    rw [act_rootElt] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    simp [zero_pow_theta] at e0 e1
    have h3 : x 3 = 0 := e1
    rw [h3, add_zero] at e0
    exact ⟨by linear_combination e0, h3⟩
  · rintro ⟨h2', h3⟩ g hg
    obtain ⟨w, rfl⟩ := (mem_rootCenter n).mp hg
    rw [act_rootElt]
    ext j
    fin_cases j <;> simp [h2', h3]

theorem fixElt_rootElt {u : F n} (hu : u ≠ 0) (w : F n) : fixElt n (rootElt n u w) = flag n 1 := by
  ext x
  rw [mem_fixElt, mem_flag_one]
  constructor
  · intro h1
    rw [act_rootElt] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    have e2 := congrFun h1 2
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at e0 e1 e2
    have h3 : x 3 = 0 := by
      have : u * x 3 = 0 := by linear_combination e2
      exact (mul_eq_zero.mp this).resolve_left hu
    rw [h3, mul_zero, add_zero] at e1 e0
    have h2' : x 2 = 0 := by
      have : u ^ 2 ^ (n + 1) * x 2 = 0 := by linear_combination e1
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu)
    rw [h2', mul_zero, add_zero] at e0
    have h1' : x 1 = 0 := by
      have : u * x 1 = 0 := by linear_combination e0
      exact (mul_eq_zero.mp this).resolve_left hu
    exact ⟨h1', h2', h3⟩
  · rintro ⟨h1, h2', h3⟩
    rw [act_rootElt]
    ext j
    fin_cases j <;> simp [h1, h2', h3]

theorem fixElt_rootElt_zero {w : F n} (hw : w ≠ 0) : fixElt n (rootElt n 0 w) = flag n 2 := by
  ext x
  rw [mem_fixElt, mem_flag_two]
  constructor
  · intro h1
    rw [act_rootElt] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    simp [zero_pow_theta] at e0 e1
    have h3 : x 3 = 0 := by
      rcases e1 with h | h
      · exact absurd h hw
      · exact h
    rw [h3, mul_zero, add_zero] at e0
    have h2' : x 2 = 0 := by
      rcases mul_eq_zero.mp (by linear_combination e0 : w * x 2 = 0) with h | h
      · exact absurd h hw
      · exact h
    exact ⟨h2', h3⟩
  · rintro ⟨h2', h3⟩
    rw [act_rootElt]
    ext j
    fin_cases j <;> simp [h2', h3]

theorem exists_pow_theta_eq (y : F n) : ∃ x : F n, x ^ 2 ^ (n + 1) = y := by
  obtain ⟨-, ⟨φ, hφ⟩, -⟩ := CFSG.LieType.Ree.suzuki_frobenius_exponents n (F n) (card_F n)
  exact ⟨φ.symm y, by rw [← hφ, RingEquiv.apply_symm_apply]⟩

theorem comm_le {T : Subgroup (Sz n)} {X Y : AddSubgroup (Fin 4 → F n)}
    (h : ∀ g ∈ T, ∀ v ∈ X, act n g v - v ∈ Y) : comm n T X ≤ Y := by
  rw [comm, AddSubgroup.closure_le]
  rintro _ ⟨g, hg, v, hv, rfl⟩
  exact h g hg v hv

theorem sub_mem_comm {T : Subgroup (Sz n)} {X : AddSubgroup (Fin 4 → F n)} {g : Sz n}
    (hg : g ∈ T) {v : Fin 4 → F n} (hv : v ∈ X) : act n g v - v ∈ comm n T X :=
  AddSubgroup.subset_closure ⟨g, hg, v, hv, rfl⟩

theorem comm_rootSub_top : comm n (rootSub n) ⊤ = flag n 3 := by
  have h2 := two_eq_zero n
  apply le_antisymm
  · refine comm_le n fun g hg v _ => ?_
    obtain ⟨u, w, rfl⟩ := (mem_rootSub n).mp hg
    rw [mem_flag_three, act_rootElt]
    simp
  · intro y hy
    rw [mem_flag_three] at hy
    have key : ∀ a b c : F n, act n (rootElt n a b) ![0, 0, 0, 1] - ![0, 0, 0, 1] +
        (act n (rootElt n c 0) ![0, 1, 0, 0] - ![0, 1, 0, 0]) =
        ![a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ 2 ^ (n + 1) + c,
          a ^ (1 + 2 ^ (n + 1)) + b, a, 0] := by
      intro a b c
      rw [act_rootElt, act_rootElt]
      ext j
      fin_cases j <;> simp [zero_pow_theta]
    set a := y 2 with ha
    set b := y 1 - a ^ (1 + 2 ^ (n + 1)) with hb
    set c := y 0 - (a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ 2 ^ (n + 1)) with hc
    have hy' : y = act n (rootElt n a b) ![0, 0, 0, 1] - ![0, 0, 0, 1] +
        (act n (rootElt n c 0) ![0, 1, 0, 0] - ![0, 1, 0, 0]) := by
      rw [key a b c]
      ext j
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, hc]
        ring
      · simp [hb]
      · simp [ha]
      · simp [hy]
    rw [hy']
    exact AddSubgroup.add_mem _ (sub_mem_comm n ((mem_rootSub n).mpr ⟨a, b, rfl⟩) trivial)
      (sub_mem_comm n ((mem_rootSub n).mpr ⟨c, 0, rfl⟩) trivial)

theorem comm_rootSub_flag_three : comm n (rootSub n) (flag n 3) = flag n 2 := by
  apply le_antisymm
  · refine comm_le n fun g hg v hv => ?_
    obtain ⟨u, w, rfl⟩ := (mem_rootSub n).mp hg
    rw [mem_flag_three] at hv
    rw [mem_flag_two, act_rootElt]
    simp [hv]
  · intro y hy
    rw [mem_flag_two] at hy
    obtain ⟨a, ha⟩ := exists_pow_theta_eq n (y 1)
    have hy' : y = act n (rootElt n a (y 0)) ![0, 0, 1, 0] - ![0, 0, 1, 0] := by
      rw [act_rootElt]
      ext j
      fin_cases j <;> simp [hy.1, hy.2, ha]
    rw [hy']
    exact sub_mem_comm n ((mem_rootSub n).mpr ⟨a, y 0, rfl⟩) ((mem_flag_three n).mpr rfl)

theorem comm_rootSub_flag_two : comm n (rootSub n) (flag n 2) = flag n 1 := by
  apply le_antisymm
  · refine comm_le n fun g hg v hv => ?_
    obtain ⟨u, w, rfl⟩ := (mem_rootSub n).mp hg
    rw [mem_flag_two] at hv
    rw [mem_flag_one, act_rootElt]
    simp [hv.1, hv.2]
  · intro y hy
    rw [mem_flag_one] at hy
    have hy' : y = act n (rootElt n (y 0) 0) ![0, 1, 0, 0] - ![0, 1, 0, 0] := by
      rw [act_rootElt]
      ext j
      fin_cases j <;> simp [hy.1, hy.2.1, hy.2.2]
    rw [hy']
    exact sub_mem_comm n ((mem_rootSub n).mpr ⟨y 0, 0, rfl⟩) ((mem_flag_two n).mpr ⟨rfl, rfl⟩)

theorem comm_rootSub_flag_one : comm n (rootSub n) (flag n 1) = ⊥ := by
  rw [eq_bot_iff]
  refine comm_le n fun g hg v hv => ?_
  rw [← fix_rootSub] at hv
  rw [hv g hg, sub_self]
  exact zero_mem _

theorem commElt_rootElt {u : F n} (hu : u ≠ 0) (w : F n) :
    commElt n (rootElt n u w) (flag n 2) = flag n 1 := by
  ext y
  rw [mem_commElt, mem_flag_one]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_flag_two] at hv
    rw [act_rootElt]
    simp [hv.1, hv.2]
  · rintro ⟨h1, h2', h3⟩
    refine ⟨![0, y 0 / u, 0, 0], (mem_flag_two n).mpr ⟨rfl, rfl⟩, ?_⟩
    rw [act_rootElt]
    ext j
    fin_cases j <;> simp [h1, h2', h3, mul_div_cancel₀ _ hu]

theorem commElt_rootElt_zero {w : F n} (hw : w ≠ 0) :
    commElt n (rootElt n 0 w) ⊤ = flag n 2 := by
  ext y
  rw [mem_commElt, mem_flag_two]
  constructor
  · rintro ⟨v, -, rfl⟩
    rw [act_rootElt]
    simp
  · rintro ⟨h2', h3⟩
    refine ⟨![0, 0, (y 0 - w ^ 2 ^ (n + 1) * (y 1 / w)) / w, y 1 / w], trivial, ?_⟩
    rw [act_rootElt]
    ext j
    fin_cases j <;> simp [h2', h3, zero_pow_theta, mul_div_cancel₀ _ hw]

theorem card_rootCenter : Nat.card (rootCenter n) = 2 ^ (2 * n + 1) := by
  rw [← SetLike.coe_sort_coe, show ((rootCenter n : Subgroup (Sz n)) : Set (Sz n)) =
    Set.range fun w : F n => rootElt n 0 w from rfl,
    Nat.card_range_of_injective fun w w' h => ((rootElt_inj n).mp h).2, card_F]

theorem rootCenter_le_centralizer : rootCenter n ≤ centralizer (rootSub n : Set (Sz n)) := by
  rintro _ ⟨w, rfl⟩
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨u, v, rfl⟩ := (mem_rootSub n).mp hg
  rw [rootElt_mul, rootElt_mul, rootElt_inj, zero_pow_theta]
  constructor <;> ring

theorem card_flag_one : Nat.card (flag n 1) = 2 ^ (2 * n + 1) := by
  have h : ((flag n 1 : AddSubgroup (Fin 4 → F n)) : Set (Fin 4 → F n)) =
      Set.range fun c : F n => (![c, 0, 0, 0] : Fin 4 → F n) := by
    ext v
    rw [SetLike.mem_coe, mem_flag_one]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨v 0, ?_⟩
      ext j
      fin_cases j <;> simp [h1, h2, h3]
    · rintro ⟨c, rfl⟩
      simp
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective, card_F]
  intro c c' hc
  simpa using congrFun hc 0

theorem card_flag_two : Nat.card (flag n 2) = (2 ^ (2 * n + 1)) ^ 2 := by
  have h : ((flag n 2 : AddSubgroup (Fin 4 → F n)) : Set (Fin 4 → F n)) =
      Set.range fun p : F n × F n => (![p.1, p.2, 0, 0] : Fin 4 → F n) := by
    ext v
    rw [SetLike.mem_coe, mem_flag_two]
    constructor
    · rintro ⟨h2, h3⟩
      refine ⟨(v 0, v 1), ?_⟩
      ext j
      fin_cases j <;> simp [h2, h3]
    · rintro ⟨p, rfl⟩
      simp
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective, Nat.card_prod, card_F, sq]
  intro p p' hp
  exact Prod.ext (by simpa using congrFun hp 0) (by simpa using congrFun hp 1)

theorem card_flag_three : Nat.card (flag n 3) = (2 ^ (2 * n + 1)) ^ 3 := by
  have h : ((flag n 3 : AddSubgroup (Fin 4 → F n)) : Set (Fin 4 → F n)) =
      Set.range fun p : F n × F n × F n => (![p.1, p.2.1, p.2.2, 0] : Fin 4 → F n) := by
    ext v
    rw [SetLike.mem_coe, mem_flag_three]
    constructor
    · rintro h3
      refine ⟨(v 0, v 1, v 2), ?_⟩
      ext j
      fin_cases j <;> simp [h3]
    · rintro ⟨p, rfl⟩
      simp
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective, Nat.card_prod, Nat.card_prod,
    card_F]
  · ring
  intro p p' hp
  exact Prod.ext (by simpa using congrFun hp 0)
    (Prod.ext (by simpa using congrFun hp 1) (by simpa using congrFun hp 2))

theorem card_top : Nat.card (⊤ : AddSubgroup (Fin 4 → F n)) = (2 ^ (2 * n + 1)) ^ 4 := by
  rw [AddSubgroup.card_top, Nat.card_fun, Nat.card_fin, card_F]

theorem flag_eq_top {i : ℕ} (hi : 4 ≤ i) : flag n i = ⊤ := by
  rw [eq_top_iff]
  intro v _ j hj
  exact absurd hj (by omega)

theorem flag_mono {i j : ℕ} (hij : i ≤ j) : flag n i ≤ flag n j :=
  fun _ hv k hk => hv k (hij.trans hk)

theorem card_flag {i : ℕ} (hi : i ≤ 4) : Nat.card (flag n i) = (2 ^ (2 * n + 1)) ^ i := by
  interval_cases i
  · rw [flag_zero, AddSubgroup.card_bot, pow_zero]
  · rw [card_flag_one, pow_one]
  · exact card_flag_two n
  · exact card_flag_three n
  · rw [flag_four, card_top]

theorem comm_rootSub_flag {k : ℕ} (hk : k < 4) :
    comm n (rootSub n) (flag n (k + 1)) = flag n k := by
  interval_cases k
  · rw [comm_rootSub_flag_one, flag_zero]
  · exact comm_rootSub_flag_two n
  · exact comm_rootSub_flag_three n
  · rw [flag_four, comm_rootSub_top]

theorem act_injective (g : Sz n) : Function.Injective (act n g) := fun v w h => by
  have := congrArg (act n g⁻¹) h
  rwa [act_inv_act, act_inv_act] at this

theorem act_surjective (g : Sz n) : Function.Surjective (act n g) :=
  fun v => ⟨act n g⁻¹ v, act_act_inv n g v⟩

theorem mem_map_act {g : Sz n} {X : AddSubgroup (Fin 4 → F n)} {v : Fin 4 → F n} :
    v ∈ X.map (act n g) ↔ act n g⁻¹ v ∈ X := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [act_inv_act]
  · intro hv
    exact ⟨_, hv, act_act_inv n g v⟩

theorem card_map_act (g : Sz n) (X : AddSubgroup (Fin 4 → F n)) :
    Nat.card (X.map (act n g)) = Nat.card X :=
  AddSubgroup.card_map_of_injective (act_injective n g)

theorem map_act_top (g : Sz n) : (⊤ : AddSubgroup (Fin 4 → F n)).map (act n g) = ⊤ :=
  AddSubgroup.map_top_of_surjective _ (act_surjective n g)

theorem fix_conj {T T' : Subgroup (Sz n)} (g : Sz n) (hT : ∀ h, h ∈ T' ↔ g⁻¹ * h * g ∈ T) :
    fix n T' = (fix n T).map (act n g) := by
  ext v
  rw [mem_map_act, mem_fix, mem_fix]
  constructor
  · intro hv t ht
    have h1 := hv (g * t * g⁻¹) ((hT _).mpr (by simpa [mul_assoc] using ht))
    rw [act_mul, act_mul] at h1
    have := congrArg (act n g⁻¹) h1
    rwa [act_inv_act] at this
  · intro hv h hh
    have h1 := hv _ ((hT h).mp hh)
    rw [act_mul, act_mul, act_act_inv] at h1
    have := congrArg (act n g) h1
    rwa [act_act_inv, act_act_inv] at this

theorem comm_conj {T T' : Subgroup (Sz n)} (g : Sz n) (hT : ∀ h, h ∈ T' ↔ g⁻¹ * h * g ∈ T)
    (X : AddSubgroup (Fin 4 → F n)) :
    comm n T' (X.map (act n g)) = (comm n T X).map (act n g) := by
  rw [comm, comm, AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨h, hh, v, hv, rfl⟩
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hv
    refine ⟨act n (g⁻¹ * h * g) x - x, ⟨_, (hT h).mp hh, x, hx, rfl⟩, ?_⟩
    rw [map_sub, act_mul, act_mul, act_act_inv]
  · rintro ⟨_, ⟨t, ht, x, hx, rfl⟩, rfl⟩
    refine ⟨g * t * g⁻¹, (hT _).mpr (by simpa [mul_assoc] using ht), act n g x,
      AddSubgroup.mem_map_of_mem _ hx, ?_⟩
    rw [map_sub, act_mul, act_mul, act_inv_act]

theorem inf_centralizer_conj {T T' : Subgroup (Sz n)} (g : Sz n)
    (hT : ∀ h, h ∈ T' ↔ g⁻¹ * h * g ∈ T) (h : Sz n) :
    h ∈ T' ⊓ centralizer (T' : Set (Sz n)) ↔
      g⁻¹ * h * g ∈ T ⊓ centralizer (T : Set (Sz n)) := by
  rw [mem_inf, mem_inf, ← hT, mem_centralizer_iff, mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun hc t ht => ?_, fun hc t' ht' => ?_⟩
  · have h1 := hc (g * t * g⁻¹) ((hT _).mpr (by simpa [mul_assoc] using ht))
    have := congrArg (fun x => g⁻¹ * x * g) h1
    simpa [mul_assoc] using this
  · have h1 := hc _ ((hT t').mp ht')
    have := congrArg (fun x => g * x * g⁻¹) h1
    simpa [mul_assoc] using this

theorem fixElt_conj (g s : Sz n) : fixElt n (g * s * g⁻¹) = (fixElt n s).map (act n g) := by
  ext v
  rw [mem_map_act, mem_fixElt, mem_fixElt, act_mul, act_mul]
  constructor
  · intro h
    have := congrArg (act n g⁻¹) h
    rwa [act_inv_act] at this
  · intro h
    rw [h, act_act_inv]

theorem commElt_conj (g s : Sz n) (X : AddSubgroup (Fin 4 → F n)) :
    commElt n (g * s * g⁻¹) (X.map (act n g)) = (commElt n s X).map (act n g) := by
  rw [commElt, commElt, AddSubgroup.map_map, AddSubgroup.map_map]
  congr 1
  refine AddMonoidHom.ext fun v => ?_
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub,
    act_mul, act_inv_act]

@[expose] noncomputable def series (S : Subgroup (Sz n)) : ℕ → AddSubgroup (Fin 4 → F n)
  | 0 => ⊥
  | 1 => fix n S
  | 2 => fix n (S ⊓ centralizer (S : Set (Sz n)))
  | 3 => comm n S ⊤
  | _ + 4 => ⊤

theorem series_two (S : Subgroup (Sz n)) :
    series n S 2 = fix n (S ⊓ centralizer (S : Set (Sz n))) := rfl

theorem series_conj {T T' : Subgroup (Sz n)} (g : Sz n) (hT : ∀ h, h ∈ T' ↔ g⁻¹ * h * g ∈ T) :
    ∀ i, series n T' i = (series n T i).map (act n g)
  | 0 => (AddSubgroup.map_bot _).symm
  | 1 => fix_conj n g hT
  | 2 => fix_conj n g (inf_centralizer_conj n g hT)
  | 3 => by
      show comm n T' ⊤ = (comm n T ⊤).map (act n g)
      rw [← comm_conj n g hT, map_act_top]
  | _ + 4 => (map_act_top n g).symm

private theorem nonempty_mulEquiv : Nonempty (Sz n ≃* CFSG.Blueprint.suzukiGroup n (F n)) :=
  CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup n

theorem card_sz : Nat.card (Sz n) =
    (2 ^ (2 * n + 1)) ^ 2 * (2 ^ (2 * n + 1) - 1) * ((2 ^ (2 * n + 1)) ^ 2 + 1) := by
  obtain ⟨e⟩ := nonempty_mulEquiv n
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.LieType.Ree.suzuki_order (card_F n)

theorem isPGroup_rootSub : IsPGroup 2 (rootSub n) :=
  IsPGroup.of_card (n := 2 * (2 * n + 1)) (by rw [card_rootSub, ← pow_mul, mul_comm])

theorem not_two_dvd_index_rootSub : ¬ 2 ∣ (rootSub n).index := by
  have h := (rootSub n).card_mul_index
  rw [card_rootSub, card_sz, mul_assoc] at h
  have hq : 0 < (2 ^ (2 * n + 1)) ^ 2 := by positivity
  have h' := Nat.eq_of_mul_eq_mul_left hq h
  rw [h']
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h1 | h1
  · have : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
    have h3 : 2 ∣ 2 ^ (2 * n + 1) := dvd_pow_self 2 (by omega)
    omega
  · have h3 : 2 ∣ (2 ^ (2 * n + 1)) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    omega

@[expose] noncomputable def rootSylow : Sylow 2 (Sz n) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (isPGroup_rootSub n).toSylow (not_two_dvd_index_rootSub n)

theorem coe_rootSylow : (rootSylow n : Subgroup (Sz n)) = rootSub n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.toSylow_coe _ _

theorem rootSub_inf_centralizer (hn : 1 ≤ n) :
    rootSub n ⊓ centralizer (rootSub n : Set (Sz n)) = rootCenter n := by
  obtain ⟨e⟩ := nonempty_mulEquiv n
  have h := (CFSG.RankThree.S4Free.Suzuki.card_sylow_and_center hn (card_F n) e
    (rootSylow n)).2.1
  rw [coe_rootSylow] at h
  symm
  exact eq_of_le_of_card_ge (le_inf (rootCenter_le n) (rootCenter_le_centralizer n))
    (by rw [h, card_rootCenter])

theorem exists_conj_rootSub (S : Sylow 2 (Sz n)) :
    ∃ g : Sz n, ∀ h, h ∈ (S : Subgroup (Sz n)) ↔ g⁻¹ * h * g ∈ rootSub n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Sz n) (rootSylow n) S
  refine ⟨g, fun h => ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply, coe_rootSylow]

theorem series_rootSub (hn : 1 ≤ n) : ∀ i, series n (rootSub n) i = flag n i
  | 0 => (flag_zero n).symm
  | 1 => fix_rootSub n
  | 2 => by
      show fix n (rootSub n ⊓ centralizer (rootSub n : Set (Sz n))) = flag n 2
      rw [rootSub_inf_centralizer n hn, fix_rootCenter]
  | 3 => comm_rootSub_top n
  | _ + 4 => (flag_eq_top n (by omega)).symm

variable {n}

theorem exists_series_eq (hn : 1 ≤ n) (S : Sylow 2 (Sz n)) :
    ∃ g : Sz n, (∀ h, h ∈ (S : Subgroup (Sz n)) ↔ g⁻¹ * h * g ∈ rootSub n) ∧
      ∀ i, series n S i = (flag n i).map (act n g) := by
  obtain ⟨g, hg⟩ := exists_conj_rootSub n S
  exact ⟨g, hg, fun i => by rw [series_conj n g hg, series_rootSub n hn]⟩

theorem series_mono (hn : 1 ≤ n) (S : Sylow 2 (Sz n)) {i j : ℕ} (hij : i ≤ j) :
    series n S i ≤ series n S j := by
  obtain ⟨g, -, hs⟩ := exists_series_eq hn S
  rw [hs, hs]
  exact AddSubgroup.map_mono (flag_mono n hij)

theorem card_series (hn : 1 ≤ n) (S : Sylow 2 (Sz n)) {i : ℕ} (hi : i ≤ 4) :
    Nat.card (series n S i) = (2 ^ (2 * n + 1)) ^ i := by
  obtain ⟨g, -, hs⟩ := exists_series_eq hn S
  rw [hs, card_map_act, card_flag n hi]

theorem comm_series (hn : 1 ≤ n) (S : Sylow 2 (Sz n)) {k : ℕ} (hk : k < 4) :
    comm n S (series n S (k + 1)) = series n S k := by
  obtain ⟨g, hg, hs⟩ := exists_series_eq hn S
  rw [hs, hs, comm_conj n g hg, comm_rootSub_flag n hk]

theorem fixElt_eq_series_one (hn : 1 ≤ n) (S : Sylow 2 (Sz n)) {s : Sz n}
    (hs : s ∈ (S : Subgroup (Sz n)))
    (hs' : s ∉ centralizer ((S : Subgroup (Sz n)) : Set (Sz n))) :
    fixElt n s = series n S 1 ∧ commElt n s (series n S 2) = series n S 1 := by
  obtain ⟨g, hg, hser⟩ := exists_series_eq hn S
  obtain ⟨u, w, hu⟩ := (mem_rootSub n).mp ((hg s).mp hs)
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hs'
    have : g⁻¹ * s * g ∈ rootSub n ⊓ centralizer (rootSub n : Set (Sz n)) := by
      rw [rootSub_inf_centralizer n hn, ← hu]
      exact ⟨w, rfl⟩
    exact ((inf_centralizer_conj n g hg s).mpr this).2
  have hs_eq : s = g * rootElt n u w * g⁻¹ := by
    rw [hu]
    group
  rw [hser, hser, hs_eq, fixElt_conj, commElt_conj, fixElt_rootElt n hu0,
    commElt_rootElt n hu0]
  exact ⟨rfl, rfl⟩

theorem fixElt_eq_series_two (hn : 1 ≤ n) (S : Sylow 2 (Sz n)) {z : Sz n}
    (hz : z ∈ (S : Subgroup (Sz n)) ⊓ centralizer ((S : Subgroup (Sz n)) : Set (Sz n)))
    (hz1 : z ≠ 1) :
    fixElt n z = series n S 2 ∧ commElt n z ⊤ = series n S 2 := by
  obtain ⟨g, hg, hser⟩ := exists_series_eq hn S
  have hz0 := (inf_centralizer_conj n g hg z).mp hz
  rw [rootSub_inf_centralizer n hn] at hz0
  obtain ⟨w, hw⟩ := (mem_rootCenter n).mp hz0
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [rootElt_zero_zero] at hw
    exact hz1 (by simpa [mul_assoc] using (congrArg (fun x => g * x * g⁻¹) hw).symm)
  have hz_eq : z = g * rootElt n 0 w * g⁻¹ := by
    rw [hw]
    group
  rw [hser, hz_eq, fixElt_conj, ← map_act_top n g, commElt_conj, fixElt_rootElt_zero n hw0,
    commElt_rootElt_zero n hw0]
  exact ⟨rfl, rfl⟩

end CFSG.RankThree.S4Free.SzNatural
