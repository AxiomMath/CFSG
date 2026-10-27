module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartOne.SEITZQ1

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K' : Type} [Field K']

theorem q1_exists_omega (h : UnitaryFieldData 2 f K') (hf : Odd f) :
    ∃ ω : K', ω ^ 2 + ω + 1 = 0 ∧ h.bar ω = ω + 1 := by
  have hfin := h.finite
  have hchar : CharP K' 2 := h.charP
  have hcard : Nat.card K'ˣ = 4 ^ f - 1 := by
    rw [Nat.card_units, h.card, pow_mul]
    norm_num
  have h3 : 3 ∣ Nat.card K'ˣ := by
    rw [hcard]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  have hω3 : (ζ : K') ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hω1 : (ζ : K') ≠ 1 := fun h1 => hζ1 (Units.ext h1)
  have hroot : (ζ : K') ^ 2 + (ζ : K') + 1 = 0 := by
    have : ((ζ : K') - 1) * ((ζ : K') ^ 2 + (ζ : K') + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  have h2 : (2 : K') = 0 := by exact_mod_cast CharP.cast_eq_zero K' 2
  have hsq : (ζ : K') ^ 2 = (ζ : K') + 1 := by linear_combination hroot - ((ζ : K') + 1) * h2
  refine ⟨ζ, hroot, ?_⟩
  rw [h.bar_apply]
  obtain ⟨k, hk⟩ := hf
  have hmod : 2 ^ f % 3 = 2 := by
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : (ζ : K') ^ 2 ^ f = (ζ : K') ^ 2 := by
    rw [← Nat.div_add_mod (2 ^ f) 3, hmod, pow_add, pow_mul, hω3, one_pow, one_mul]
  rw [this, hsq]

@[expose] noncomputable def q1DiagGL : (Fin 3 → K'ˣ) →* GL (Fin 3) K' :=
  (Units.map (Matrix.diagonalRingHom (Fin 3) K').toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin 3 => K')).symm.toMonoidHom

theorem coe_q1DiagGL (a : Fin 3 → K'ˣ) :
    (q1DiagGL a : Matrix (Fin 3) (Fin 3) K') = Matrix.diagonal (fun i => ((a i : K'ˣ) : K')) :=
  rfl

theorem q1DiagGL_injective : Function.Injective (q1DiagGL : (Fin 3 → K'ˣ) → GL (Fin 3) K') := by
  intro a b hab
  funext i
  apply Units.ext
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K' => (g : Matrix (Fin 3) (Fin 3) K'))
    hab) i) i
  simpa [coe_q1DiagGL] using this

@[expose] def q1DiagVec : K'ˣ × K'ˣ →* (Fin 3 → K'ˣ) where
  toFun u := ![u.1, u.1⁻¹ * u.2, u.2⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' u v := by
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem q1DiagVec_apply (u : K'ˣ × K'ˣ) :
    (q1DiagVec u : Fin 3 → K'ˣ) = ![u.1, u.1⁻¹ * u.2, u.2⁻¹] :=
  rfl

theorem q1DiagVec_injective :
    Function.Injective (q1DiagVec : K'ˣ × K'ˣ →* (Fin 3 → K'ˣ)) := by
  intro u v h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  exact Prod.ext (by simpa [q1DiagVec_apply] using h0) (by simpa [q1DiagVec_apply] using h2)

@[expose] noncomputable def q1DiagTorus : K'ˣ × K'ˣ →* GL (Fin 3) K' :=
  q1DiagGL.comp q1DiagVec

theorem coe_q1DiagTorus (u : K'ˣ × K'ˣ) :
    (q1DiagTorus u : Matrix (Fin 3) (Fin 3) K') =
      Matrix.diagonal ![(u.1 : K'), (u.1 : K')⁻¹ * u.2, (u.2 : K')⁻¹] := by
  rw [q1DiagTorus, MonoidHom.comp_apply, coe_q1DiagGL]
  congr 1
  funext i
  fin_cases i <;> simp [q1DiagVec_apply]

theorem q1DiagTorus_injective :
    Function.Injective (q1DiagTorus : K'ˣ × K'ˣ →* GL (Fin 3) K') :=
  q1DiagGL_injective.comp q1DiagVec_injective

theorem q1DiagTorus_mem_unitarySU (h : UnitaryFieldData 2 f K') {u : K'ˣ × K'ˣ}
    (hu : u ^ (2 ^ f + 1) = 1) : q1DiagTorus u ∈ unitarySU 2 f K' 3 := by
  have hv : ∀ i, (q1DiagVec u i) ^ (2 ^ f + 1) = 1 := by
    intro i
    have : (q1DiagVec u) ^ (2 ^ f + 1) = 1 := by rw [← map_pow, hu, map_one]
    simpa using congrFun this i
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [q1DiagTorus, MonoidHom.comp_apply, coe_q1DiagGL, Matrix.det_diagonal,
      Fin.prod_univ_three, ← Units.val_mul, ← Units.val_mul]
    have : q1DiagVec u 0 * q1DiagVec u 1 * q1DiagVec u 2 = 1 := by simp [q1DiagVec_apply]
    rw [this, Units.val_one]
  · rw [q1DiagTorus, MonoidHom.comp_apply, coe_q1DiagGL, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hv i, Units.val_one]

theorem q1_plane (h : UnitaryFieldData 2 f K') {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (_hp3 : p ≠ 3) (hpq : p ∣ 2 ^ f + 1) :
    ∃ E : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K' 3),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ 2 ∧
      (∀ x ∈ E, ∀ i j : Fin 3, i ≠ j →
        ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0) ∧
      ∃ x₀ ∈ E, x₀ ≠ 1 ∧ ∃ z : K', z ≠ 0 ∧
        ((x₀ : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = Matrix.diagonal ![z, 1, z⁻¹] := by
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card K'ˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [Nat.card_units, h.card, pow_mul']
    exact h1
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p (hcard ▸ Dvd.dvd.mul_right hpq _)
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  set S := Subgroup.zpowers ζ with hS
  have hSp : ∀ s ∈ S, s ^ p = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]))
  have hSq : ∀ s ∈ S, s ^ (2 ^ f + 1) = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]; exact hpq))
  let E₀ : Subgroup (GL (Fin 3) K') := (S.prod S).map q1DiagTorus
  have hE₀G : E₀ ≤ unitarySU 2 f K' 3 := by
    rintro _ ⟨u, hu, rfl⟩
    exact q1DiagTorus_mem_unitarySU h (Prod.ext (hSq _ hu.1) (hSq _ hu.2))
  refine ⟨E₀.subgroupOf (unitarySU 2 f K' 3), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨v, hv, hyv⟩ := Subgroup.mem_subgroupOf.mp hy
    apply Subtype.ext
    show (x : GL (Fin 3) K') * y = y * x
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, mul_comm u v]
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    have hup : u ^ p = 1 := Prod.ext (hSp _ hu.1) (hSp _ hu.2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hxu, ← map_pow, hup, map_one]
    rfl
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀G).toEquiv,
      Subgroup.card_map_of_injective q1DiagTorus_injective,
      Nat.card_congr (Subgroup.prodEquiv S S).toEquiv, Nat.card_prod, hS, Nat.card_zpowers, hζ,
      sq]
  · intro x hx i j hij
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    rw [← hxu, coe_q1DiagTorus]
    exact Matrix.diagonal_apply_ne _ hij
  · have hζS : ζ ∈ S := Subgroup.mem_zpowers ζ
    refine ⟨⟨q1DiagTorus (ζ, ζ), hE₀G ⟨(ζ, ζ), ⟨hζS, hζS⟩, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨(ζ, ζ), ⟨hζS, hζS⟩, rfl⟩, ?_, (ζ : K'), ζ.ne_zero, ?_⟩
    · intro h1
      have h2 : q1DiagTorus (ζ, ζ) = q1DiagTorus 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      exact hζ1 (congrArg Prod.fst (q1DiagTorus_injective h2))
    · show (q1DiagTorus (ζ, ζ) : Matrix (Fin 3) (Fin 3) K') = _
      rw [coe_q1DiagTorus]
      congr 1
      funext i
      fin_cases i <;> simp

end CFSG.RankThree.PartOne.SEITZQ1
