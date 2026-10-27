module

public import CFSG.LocalAnalysis.StandardType.GGF4A3ReflectionPairData
public import CFSG.LocalAnalysis.StandardType.GGF4OrigRep

public section

namespace CFSG.StandardType.F4Model

variable {W : Type} [Group W]

def stdA1_0 (R : F4Rep W) : W := R.wd [0, 1, 0]
def stdA1_1 (R : F4Rep W) : W := R.s 1
def stdA1_2 (R : F4Rep W) : W := R.wd [0, 2, 1, 0, 2]
def stdA1set (R : F4Rep W) : Set W := {stdA1_0 R, stdA1_1 R, stdA1_2 R}

def stdA2_0 (R : F4Rep W) : W := R.wd [2, 3, 2]
def stdA2_1 (R : F4Rep W) : W := R.s 2
def stdA2_2 (R : F4Rep W) : W := R.wd [1, 2, 3, 2, 1]
def stdA2set (R : F4Rep W) : Set W := {stdA2_0 R, stdA2_1 R, stdA2_2 R}

theorem rho_stdA1_0 (R : F4Rep W) : R.ρ (stdA1_0 R) = (Rm 5).toMat := by
  unfold stdA1_0
  rw [R.rho_wd, evalW_stdA1_0]

theorem rho_stdA1_1 (R : F4Rep W) : R.ρ (stdA1_1 R) = (Rm 16).toMat := by
  unfold stdA1_1
  rw [R.hs 1, Sm_one_eq]

theorem rho_stdA1_2 (R : F4Rep W) : R.ρ (stdA1_2 R) = (Rm 6).toMat := by
  unfold stdA1_2
  rw [R.rho_wd, evalW_stdA1_2]

theorem rho_stdA2_0 (R : F4Rep W) : R.ρ (stdA2_0 R) = (Rm 15).toMat := by
  unfold stdA2_0
  rw [R.rho_wd, evalW_stdA2_0]

theorem rho_stdA2_1 (R : F4Rep W) : R.ρ (stdA2_1 R) = (Rm 14).toMat := by
  unfold stdA2_1
  rw [R.hs 2, Sm_two_eq]

theorem rho_stdA2_2 (R : F4Rep W) : R.ρ (stdA2_2 R) = (Rm 20).toMat := by
  unfold stdA2_2
  rw [R.rho_wd, evalW_stdA2_2]

theorem relA_of_orders {R : F4Rep W} {a0 a1 a2 : W} {x0 x1 x2 : M4}
    (h0 : R.ρ a0 = x0.toMat) (h1 : R.ρ a1 = x1.toMat) (h2 : R.ρ a2 = x2.toMat)
    (o01 : orderOf (a0 * a1) = 3) (o12 : orderOf (a1 * a2) = 3)
    (o02 : orderOf (a0 * a2) = 2) : relA x0 x1 x2 := by
  rw [relA_iff]
  have ord01 : orderOf ((x0.mul x1).toMat) = 3 := by
    rw [← R.rho_mul h0 h1, orderOf_injective R.ρ R.inj, o01]
  have ord12 : orderOf ((x1.mul x2).toMat) = 3 := by
    rw [← R.rho_mul h1 h2, orderOf_injective R.ρ R.inj, o12]
  have ord02 : orderOf ((x0.mul x2).toMat) = 2 := by
    rw [← R.rho_mul h0 h2, orderOf_injective R.ρ R.inj, o02]
  have hne : ∀ (z : M4) (n : Nat), orderOf z.toMat = n → n ≠ 1 → z ≠ M4.one := by
    intro z n hz hn hzo
    rw [hzo, M4.toMat_one, orderOf_one] at hz
    exact hn hz.symm
  refine ⟨?_, hne _ 3 ord01 (by norm_num), ?_, hne _ 3 ord12 (by norm_num),
    ?_, hne _ 2 ord02 (by norm_num)⟩
  · apply M4.toMat_injective
    rw [M4.toMat_pw3, M4.toMat_one, ← pow_three]
    have h := pow_orderOf_eq_one ((x0.mul x1).toMat)
    rwa [ord01] at h
  · apply M4.toMat_injective
    rw [M4.toMat_pw3, M4.toMat_one, ← pow_three]
    have h := pow_orderOf_eq_one ((x1.mul x2).toMat)
    rwa [ord12] at h
  · apply M4.toMat_injective
    rw [M4.toMat_pw2, M4.toMat_one, ← pow_two]
    have h := pow_orderOf_eq_one ((x0.mul x2).toMat)
    rwa [ord02] at h

theorem stage2A1_conj {R : F4Rep W} {a0 a2 : W} (h0 : R.IsRefl a0) (h2 : R.IsRefl a2)
    (o01 : orderOf (a0 * R.s 1) = 3) (o12 : orderOf (R.s 1 * a2) = 3)
    (o02 : orderOf (a0 * a2) = 2) :
    ∃ g : W, g * a0 * g⁻¹ = stdA1_0 R ∧ g * R.s 1 * g⁻¹ = R.s 1 ∧
      g * a2 * g⁻¹ = stdA1_2 R := by
  obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep h0
  obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep h2
  have hrel : relA (Rm x0) (Sm 1) (Rm x2) := relA_of_orders (R := R) ρ0 (R.hs 1) ρ2 o01 o12 o02
  obtain ⟨h0', h2', h1'⟩ := stage2A1 x0 hx0 x2 hx2 hrel
  exact ⟨R.wd (W2A1 (x0 * 24 + x2)),
    R.conj_wd_eq ρ0 (rho_stdA1_0 R) h0',
    R.conj_wd_eq (R.hs 1) (R.hs 1) h1',
    R.conj_wd_eq ρ2 (rho_stdA1_2 R) h2'⟩

theorem stage2A2_conj {R : F4Rep W} {a0 a2 : W} (h0 : R.IsRefl a0) (h2 : R.IsRefl a2)
    (o01 : orderOf (a0 * R.s 2) = 3) (o12 : orderOf (R.s 2 * a2) = 3)
    (o02 : orderOf (a0 * a2) = 2) :
    ∃ g : W, g * a0 * g⁻¹ = stdA2_0 R ∧ g * R.s 2 * g⁻¹ = R.s 2 ∧
      g * a2 * g⁻¹ = stdA2_2 R := by
  obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep h0
  obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep h2
  have hrel : relA (Rm x0) (Sm 2) (Rm x2) := relA_of_orders (R := R) ρ0 (R.hs 2) ρ2 o01 o12 o02
  obtain ⟨h0', h2', h1'⟩ := stage2A2 x0 hx0 x2 hx2 hrel
  exact ⟨R.wd (W2A2 (x0 * 24 + x2)),
    R.conj_wd_eq ρ0 (rho_stdA2_0 R) h0',
    R.conj_wd_eq (R.hs 2) (R.hs 2) h1',
    R.conj_wd_eq ρ2 (rho_stdA2_2 R) h2'⟩

theorem classifyA3 {R : F4Rep W} {a : Fin 3 → W} (ha : ∀ i, R.IsRefl (a i))
    (o01 : orderOf (a 0 * a 1) = 3) (o12 : orderOf (a 1 * a 2) = 3)
    (o02 : orderOf (a 0 * a 2) = 2) :
    (∃ g : W, g * a 0 * g⁻¹ = stdA1_0 R ∧ g * a 1 * g⁻¹ = stdA1_1 R ∧
      g * a 2 * g⁻¹ = stdA1_2 R) ∨
    (∃ g : W, g * a 0 * g⁻¹ = stdA2_0 R ∧ g * a 1 * g⁻¹ = stdA2_1 R ∧
      g * a 2 * g⁻¹ = stdA2_2 R) := by
  obtain ⟨g1, T, hT, e1⟩ := R.stage1_conj (ha 1)
  have o01' : orderOf (g1 * a 0 * g1⁻¹ * R.s T) = 3 := by
    rw [← e1, show g1 * a 0 * g1⁻¹ * (g1 * a 1 * g1⁻¹) = g1 * (a 0 * a 1) * g1⁻¹ by
      group, F4Rep.orderOf_conj_eq, o01]
  have o12' : orderOf (R.s T * (g1 * a 2 * g1⁻¹)) = 3 := by
    rw [← e1, show g1 * a 1 * g1⁻¹ * (g1 * a 2 * g1⁻¹) = g1 * (a 1 * a 2) * g1⁻¹ by
      group, F4Rep.orderOf_conj_eq, o12]
  have o02' : orderOf (g1 * a 0 * g1⁻¹ * (g1 * a 2 * g1⁻¹)) = 2 := by
    rw [show g1 * a 0 * g1⁻¹ * (g1 * a 2 * g1⁻¹) = g1 * (a 0 * a 2) * g1⁻¹ by
      group, F4Rep.orderOf_conj_eq, o02]
  rcases hT with rfl | rfl
  · obtain ⟨g2, c0, c1, c2⟩ :=
      stage2A1_conj (R := R) (ha 0 |>.conj g1) (ha 2 |>.conj g1) o01' o12' o02'
    refine Or.inl ⟨g2 * g1, ?_, ?_, ?_⟩
    · rw [show g2 * g1 * a 0 * (g2 * g1)⁻¹ = g2 * (g1 * a 0 * g1⁻¹) * g2⁻¹ by group]
      exact c0
    · rw [show g2 * g1 * a 1 * (g2 * g1)⁻¹ = g2 * (g1 * a 1 * g1⁻¹) * g2⁻¹ by group, e1]
      simpa [stdA1_1] using c1
    · rw [show g2 * g1 * a 2 * (g2 * g1)⁻¹ = g2 * (g1 * a 2 * g1⁻¹) * g2⁻¹ by group]
      exact c2
  · obtain ⟨g2, c0, c1, c2⟩ :=
      stage2A2_conj (R := R) (ha 0 |>.conj g1) (ha 2 |>.conj g1) o01' o12' o02'
    refine Or.inr ⟨g2 * g1, ?_, ?_, ?_⟩
    · rw [show g2 * g1 * a 0 * (g2 * g1)⁻¹ = g2 * (g1 * a 0 * g1⁻¹) * g2⁻¹ by group]
      exact c0
    · rw [show g2 * g1 * a 1 * (g2 * g1)⁻¹ = g2 * (g1 * a 1 * g1⁻¹) * g2⁻¹ by group, e1]
      simpa [stdA2_1] using c1
    · rw [show g2 * g1 * a 2 * (g2 * g1)⁻¹ = g2 * (g1 * a 2 * g1⁻¹) * g2⁻¹ by group]
      exact c2

def tA1 (R : F4Rep W) : W := R.s 2
def uA1 (R : F4Rep W) : W := R.wd [0, 1, 2, 1, 0]
def tA2 (R : F4Rep W) : W := R.wd [3, 2, 1, 2, 3]
def uA2 (R : F4Rep W) : W := R.s 1

theorem rho_tA1 (R : F4Rep W) : R.ρ (tA1 R) = (Rm 14).toMat := by
  unfold tA1
  rw [R.hs 2, Sm_two_eq]

theorem rho_uA1 (R : F4Rep W) : R.ρ (uA1 R) = (Rm 1).toMat := by
  unfold uA1
  rw [R.rho_wd, evalW_uA1]

theorem rho_tA2 (R : F4Rep W) : R.ρ (tA2 R) = (Rm 18).toMat := by
  unfold tA2
  rw [R.rho_wd, evalW_uA2]

theorem rho_uA2 (R : F4Rep W) : R.ρ (uA2 R) = (Rm 16).toMat := by
  unfold uA2
  rw [R.hs 1, Sm_one_eq]

theorem uA1_eq_conj (R : F4Rep W) :
    uA1 R = R.wd [0, 1] * R.s 2 * (R.wd [0, 1])⁻¹ := by
  apply R.inj
  rw [rho_uA1 R, R.rho_conj_wd [0, 1] (R.hs 2)]
  have h : conjW [0, 1] (Sm 2) = Rm 1 := by decide +kernel
  rw [h]

theorem tA2_eq_conj (R : F4Rep W) :
    tA2 R = R.wd [3, 2] * R.s 1 * (R.wd [3, 2])⁻¹ := by
  apply R.inj
  rw [rho_tA2 R, R.rho_conj_wd [3, 2] (R.hs 1)]
  have h : conjW [3, 2] (Sm 1) = Rm 18 := by decide +kernel
  rw [h]

theorem isRefl_tA1 (R : F4Rep W) : R.IsRefl (tA1 R) := ⟨1, 2, by simp [tA1]⟩

theorem isRefl_uA1 (R : F4Rep W) : R.IsRefl (uA1 R) :=
  ⟨R.wd [0, 1], 2, uA1_eq_conj R⟩

theorem isRefl_tA2 (R : F4Rep W) : R.IsRefl (tA2 R) :=
  ⟨R.wd [3, 2], 1, tA2_eq_conj R⟩

theorem isRefl_uA2 (R : F4Rep W) : R.IsRefl (uA2 R) := ⟨1, 1, by simp [uA2]⟩

theorem sq_eq_one_of_rho {R : F4Rep W} {t : W} {x : M4}
    (h : R.ρ t = x.toMat) (hx : x.mul x = M4.one) : t * t = 1 := by
  apply R.inj
  rw [R.rho_mul h h, hx, M4.toMat_one, map_one]

theorem tA1_comm_uA1 (R : F4Rep W) : tA1 R * uA1 R = uA1 R * tA1 R := by
  apply R.inj
  rw [R.rho_mul (rho_tA1 R) (rho_uA1 R), R.rho_mul (rho_uA1 R) (rho_tA1 R)]
  have h : (Rm 14).mul (Rm 1) = (Rm 1).mul (Rm 14) := by decide +kernel
  rw [h]

theorem tA1_mul_uA1 (R : F4Rep W) : tA1 R * uA1 R = stdA1_0 R * stdA1_2 R := by
  apply R.inj
  rw [R.rho_mul (rho_tA1 R) (rho_uA1 R),
    R.rho_mul (rho_stdA1_0 R) (rho_stdA1_2 R)]
  have h : (Rm 14).mul (Rm 1) = (Rm 5).mul (Rm 6) := by decide +kernel
  rw [h]

theorem tA1_ne_uA1 (R : F4Rep W) : tA1 R ≠ uA1 R := by
  intro h
  have h' : Rm 14 = Rm 1 :=
    M4.toMat_injective (by rw [← rho_tA1 R, ← rho_uA1 R, h])
  exact absurd h' (by decide +kernel)

theorem tA2_comm_uA2 (R : F4Rep W) : tA2 R * uA2 R = uA2 R * tA2 R := by
  apply R.inj
  rw [R.rho_mul (rho_tA2 R) (rho_uA2 R), R.rho_mul (rho_uA2 R) (rho_tA2 R)]
  have h : (Rm 18).mul (Rm 16) = (Rm 16).mul (Rm 18) := by decide +kernel
  rw [h]

theorem tA2_mul_uA2 (R : F4Rep W) : tA2 R * uA2 R = stdA2_0 R * stdA2_2 R := by
  apply R.inj
  rw [R.rho_mul (rho_tA2 R) (rho_uA2 R),
    R.rho_mul (rho_stdA2_0 R) (rho_stdA2_2 R)]
  have h : (Rm 18).mul (Rm 16) = (Rm 15).mul (Rm 20) := by decide +kernel
  rw [h]

theorem tA2_ne_uA2 (R : F4Rep W) : tA2 R ≠ uA2 R := by
  intro h
  have h' : Rm 18 = Rm 16 :=
    M4.toMat_injective (by rw [← rho_tA2 R, ← rho_uA2 R, h])
  exact absurd h' (by decide +kernel)

theorem mem_matrix_family_of_closure {R : F4Rep W} {n : Nat} {H : Fin n → M4}
    {S : Set W}
    (hone : ∃ k : Fin n, H k = M4.one)
    (hmul : ∀ i j : Fin n, ∃ k : Fin n, H k = (H i).mul (H j))
    (hgen : ∀ x ∈ S, ∃ k : Fin n, R.ρ x = (H k).toMat)
    (hsq : ∀ x ∈ S, x * x = 1)
    {w : W} (hw : w ∈ Subgroup.closure S) :
    ∃ k : Fin n, R.ρ w = (H k).toMat := by
  let Q : W → Prop := fun u =>
    (∃ k : Fin n, R.ρ u = (H k).toMat) ∧
      (∃ k : Fin n, R.ρ u⁻¹ = (H k).toMat)
  have hQw : Q w := by
    refine Subgroup.closure_induction (p := fun u _ => Q u) ?_ ?_ ?_ ?_ hw
    · intro x hx
      refine ⟨hgen x hx, ?_⟩
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
      rw [hxinv]
      exact hgen x hx
    · refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := hone
        refine ⟨k, ?_⟩
        rw [map_one, hk, M4.toMat_one]
      · obtain ⟨k, hk⟩ := hone
        refine ⟨k, ?_⟩
        rw [inv_one, map_one, hk, M4.toMat_one]
    · intro x y hx hy hQx hQy
      obtain ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩ := hQx
      obtain ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩ := hQy
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := hmul i j
        refine ⟨k, ?_⟩
        rw [map_mul, hi, hj, ← M4.toMat_mul, hk]
      · obtain ⟨k, hk⟩ := hmul j' i'
        refine ⟨k, ?_⟩
        rw [mul_inv_rev, map_mul, hj', hi', ← M4.toMat_mul, hk]
    · intro x hx hQx
      exact ⟨hQx.2, by simpa using hQx.1⟩
  exact hQw.1

theorem not_mem_closure_of_matrix_notMem {R : F4Rep W} {n : Nat} {H : Fin n → M4}
    {S : Set W}
    (hone : ∃ k : Fin n, H k = M4.one)
    (hmul : ∀ i j : Fin n, ∃ k : Fin n, H k = (H i).mul (H j))
    (hgen : ∀ x ∈ S, ∃ k : Fin n, R.ρ x = (H k).toMat)
    (hsq : ∀ x ∈ S, x * x = 1)
    {y : Nat} (hy : ∀ k : Fin n, H k ≠ Rm y) {t : W}
    (ht : R.ρ t = (Rm y).toMat) : t ∉ Subgroup.closure S := by
  intro hmem
  obtain ⟨k, hk⟩ := mem_matrix_family_of_closure hone hmul hgen hsq hmem
  exact hy k (M4.toMat_injective (hk.symm.trans ht))

theorem stdA1_t_not_mem (R : F4Rep W) :
    tA1 R ∉ Subgroup.closure (stdA1set R) := by
  refine not_mem_closure_of_matrix_notMem (R := R) (H := H1) H1_one H1_mul ?_ ?_
    H1_not_t (rho_tA1 R)
  · intro x hx
    simp only [stdA1set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨k, hk⟩ := H1_gen0
      exact ⟨k, by rw [rho_stdA1_0 R, hk]⟩
    · obtain ⟨k, hk⟩ := H1_gen1
      exact ⟨k, by rw [rho_stdA1_1 R, hk]⟩
    · obtain ⟨k, hk⟩ := H1_gen2
      exact ⟨k, by rw [rho_stdA1_2 R, hk]⟩
  · intro x hx
    simp only [stdA1set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact sq_eq_one_of_rho (rho_stdA1_0 R) (by decide +kernel)
    · exact sq_eq_one_of_rho (rho_stdA1_1 R) (by decide +kernel)
    · exact sq_eq_one_of_rho (rho_stdA1_2 R) (by decide +kernel)

theorem stdA2_t_not_mem (R : F4Rep W) :
    tA2 R ∉ Subgroup.closure (stdA2set R) := by
  refine not_mem_closure_of_matrix_notMem (R := R) (H := H2) H2_one H2_mul ?_ ?_
    H2_not_t (rho_tA2 R)
  · intro x hx
    simp only [stdA2set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨k, hk⟩ := H2_gen0
      exact ⟨k, by rw [rho_stdA2_0 R, hk]⟩
    · obtain ⟨k, hk⟩ := H2_gen1
      exact ⟨k, by rw [rho_stdA2_1 R, hk]⟩
    · obtain ⟨k, hk⟩ := H2_gen2
      exact ⟨k, by rw [rho_stdA2_2 R, hk]⟩
  · intro x hx
    simp only [stdA2set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact sq_eq_one_of_rho (rho_stdA2_0 R) (by decide +kernel)
    · exact sq_eq_one_of_rho (rho_stdA2_1 R) (by decide +kernel)
    · exact sq_eq_one_of_rho (rho_stdA2_2 R) (by decide +kernel)

theorem exists_a3_reflection_pair (cs : CoxeterSystem CoxeterMatrix.F₄ W)
    (a : Fin 3 → W) (ha : ∀ i, cs.IsReflection (a i))
    (o01 : orderOf (a 0 * a 1) = 3) (o12 : orderOf (a 1 * a 2) = 3)
    (o02 : orderOf (a 0 * a 2) = 2) :
    ∃ t u : W, cs.IsReflection t ∧ cs.IsReflection u ∧ t ≠ u ∧ t * u = u * t ∧
      t * u ∈ Subgroup.closure (Set.range a) ∧
      t ∉ Subgroup.closure (Set.range a) := by
  obtain ⟨R, hRs⟩ := exists_f4Rep cs
  have haR : ∀ i, R.IsRefl (a i) := fun i => (F4Rep.isRefl_iff (R := R) hRs).2 (ha i)
  rcases classifyA3 (R := R) haR o01 o12 o02 with
    ⟨g, hg0, hg1, hg2⟩ | ⟨g, hg0, hg1, hg2⟩
  ·
    have htR : R.IsRefl (tA1 R) := isRefl_tA1 R
    have huR : R.IsRefl (uA1 R) := isRefl_uA1 R
    have htcs : cs.IsReflection (tA1 R) := (F4Rep.isRefl_iff (R := R) hRs).1 htR
    have hucs : cs.IsReflection (uA1 R) := (F4Rep.isRefl_iff (R := R) hRs).1 huR
    refine ⟨g⁻¹ * tA1 R * g, g⁻¹ * uA1 R * g, by simpa using htcs.conj g⁻¹, by simpa using hucs.conj g⁻¹,
      ?_, ?_, ?_, ?_⟩
    · intro h
      apply tA1_ne_uA1 R
      calc tA1 R = g * (g⁻¹ * tA1 R * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * uA1 R * g) * g⁻¹ := by rw [h]
        _ = uA1 R := by group
    · calc (g⁻¹ * tA1 R * g) * (g⁻¹ * uA1 R * g)
          = g⁻¹ * (tA1 R * uA1 R) * g := by group
        _ = g⁻¹ * (uA1 R * tA1 R) * g := by rw [tA1_comm_uA1 R]
        _ = (g⁻¹ * uA1 R * g) * (g⁻¹ * tA1 R * g) := by group
    · have ha0 : g⁻¹ * stdA1_0 R * g = a 0 := by rw [← hg0]; group
      have ha2 : g⁻¹ * stdA1_2 R * g = a 2 := by rw [← hg2]; group
      have htu : (g⁻¹ * tA1 R * g) * (g⁻¹ * uA1 R * g) = a 0 * a 2 := by
        calc (g⁻¹ * tA1 R * g) * (g⁻¹ * uA1 R * g)
            = g⁻¹ * (tA1 R * uA1 R) * g := by group
          _ = g⁻¹ * (stdA1_0 R * stdA1_2 R) * g := by rw [tA1_mul_uA1 R]
          _ = (g⁻¹ * stdA1_0 R * g) * (g⁻¹ * stdA1_2 R * g) := by group
          _ = a 0 * a 2 := by rw [ha0, ha2]
      rw [htu]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_range_self 0))
        (Subgroup.subset_closure (Set.mem_range_self 2))
    · intro hmem
      have hconj : g * (g⁻¹ * tA1 R * g) * g⁻¹ ∈ Subgroup.closure (stdA1set R) := by
        refine Subgroup.closure_induction
          (p := fun w _ => g * w * g⁻¹ ∈ Subgroup.closure (stdA1set R)) ?_ ?_ ?_ ?_ hmem
        · intro x hx
          obtain ⟨i, rfl⟩ := hx
          fin_cases i
          · change g * a 0 * g⁻¹ ∈ Subgroup.closure (stdA1set R)
            rw [hg0]
            exact Subgroup.subset_closure (by simp [stdA1set])
          · change g * a 1 * g⁻¹ ∈ Subgroup.closure (stdA1set R)
            rw [hg1]
            exact Subgroup.subset_closure (by simp [stdA1set])
          · change g * a 2 * g⁻¹ ∈ Subgroup.closure (stdA1set R)
            rw [hg2]
            exact Subgroup.subset_closure (by simp [stdA1set])
        · simp [stdA1set]
        · intro x y hx hy ihx ihy
          rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
          exact Subgroup.mul_mem _ ihx ihy
        · intro x hx ih
          rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ ih
      have hgt : g * (g⁻¹ * tA1 R * g) * g⁻¹ = tA1 R := by group
      rw [hgt] at hconj
      exact stdA1_t_not_mem R hconj
  ·
    have htR : R.IsRefl (tA2 R) := isRefl_tA2 R
    have huR : R.IsRefl (uA2 R) := isRefl_uA2 R
    have htcs : cs.IsReflection (tA2 R) := (F4Rep.isRefl_iff (R := R) hRs).1 htR
    have hucs : cs.IsReflection (uA2 R) := (F4Rep.isRefl_iff (R := R) hRs).1 huR
    refine ⟨g⁻¹ * tA2 R * g, g⁻¹ * uA2 R * g, by simpa using htcs.conj g⁻¹, by simpa using hucs.conj g⁻¹,
      ?_, ?_, ?_, ?_⟩
    · intro h
      apply tA2_ne_uA2 R
      calc tA2 R = g * (g⁻¹ * tA2 R * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * uA2 R * g) * g⁻¹ := by rw [h]
        _ = uA2 R := by group
    · calc (g⁻¹ * tA2 R * g) * (g⁻¹ * uA2 R * g)
          = g⁻¹ * (tA2 R * uA2 R) * g := by group
        _ = g⁻¹ * (uA2 R * tA2 R) * g := by rw [tA2_comm_uA2 R]
        _ = (g⁻¹ * uA2 R * g) * (g⁻¹ * tA2 R * g) := by group
    · have ha0 : g⁻¹ * stdA2_0 R * g = a 0 := by rw [← hg0]; group
      have ha2 : g⁻¹ * stdA2_2 R * g = a 2 := by rw [← hg2]; group
      have htu : (g⁻¹ * tA2 R * g) * (g⁻¹ * uA2 R * g) = a 0 * a 2 := by
        calc (g⁻¹ * tA2 R * g) * (g⁻¹ * uA2 R * g)
            = g⁻¹ * (tA2 R * uA2 R) * g := by group
          _ = g⁻¹ * (stdA2_0 R * stdA2_2 R) * g := by rw [tA2_mul_uA2 R]
          _ = (g⁻¹ * stdA2_0 R * g) * (g⁻¹ * stdA2_2 R * g) := by group
          _ = a 0 * a 2 := by rw [ha0, ha2]
      rw [htu]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_range_self 0))
        (Subgroup.subset_closure (Set.mem_range_self 2))
    · intro hmem
      have hconj : g * (g⁻¹ * tA2 R * g) * g⁻¹ ∈ Subgroup.closure (stdA2set R) := by
        refine Subgroup.closure_induction
          (p := fun w _ => g * w * g⁻¹ ∈ Subgroup.closure (stdA2set R)) ?_ ?_ ?_ ?_ hmem
        · intro x hx
          obtain ⟨i, rfl⟩ := hx
          fin_cases i
          · change g * a 0 * g⁻¹ ∈ Subgroup.closure (stdA2set R)
            rw [hg0]
            exact Subgroup.subset_closure (by simp [stdA2set])
          · change g * a 1 * g⁻¹ ∈ Subgroup.closure (stdA2set R)
            rw [hg1]
            exact Subgroup.subset_closure (by simp [stdA2set])
          · change g * a 2 * g⁻¹ ∈ Subgroup.closure (stdA2set R)
            rw [hg2]
            exact Subgroup.subset_closure (by simp [stdA2set])
        · simp [stdA2set]
        · intro x y hx hy ihx ihy
          rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
          exact Subgroup.mul_mem _ ihx ihy
        · intro x hx ih
          rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ ih
      have hgt : g * (g⁻¹ * tA2 R * g) * g⁻¹ = tA2 R := by group
      rw [hgt] at hconj
      exact stdA2_t_not_mem R hconj

end CFSG.StandardType.F4Model

end
