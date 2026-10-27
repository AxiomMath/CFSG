module

public import CFSG.Monster.B.Short.Rootless
public import CFSG.Monster.B.Short.AxisOrbit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.SpinLattice Matrix

abbrev LL : Type := codeLatticeSubgroup allOnes_mem_C

instance : Module.Free ℤ LL :=
  Module.Free.of_basis
    (nonempty_basis_codeLattice allOnes_mem_C weight_mod_four' mem_C_iff_forall_dotProduct).some

@[expose] def hL : LL →+ LL →+ ℤ where
  toFun x :=
    { toFun := fun y => hInt (x : Fin 24 → ℤ) y
      map_zero' := by simp [hInt]
      map_add' := fun y y' => by
        change hInt (x : Fin 24 → ℤ) ((y : Fin 24 → ℤ) + y') = hInt x y + hInt x y'
        rw [hInt_comm, hInt_add_left allOnes_mem_C weight_mod_four' y.2 y'.2 x.2,
          hInt_comm (y : Fin 24 → ℤ), hInt_comm (y' : Fin 24 → ℤ)] }
  map_zero' := AddMonoidHom.ext fun y => by
    change hInt (0 : Fin 24 → ℤ) y = 0
    simp [hInt]
  map_add' x x' := AddMonoidHom.ext fun y =>
    hInt_add_left allOnes_mem_C weight_mod_four' x.2 x'.2 y.2

theorem hL_apply (x y : LL) : hL x y = hInt (x : Fin 24 → ℤ) y := rfl

theorem hL_symm (x y : LL) : hL x y = hL y x := hInt_comm _ _

theorem hL_self_ge {x : LL} (hx : x ≠ 0) : 4 ≤ hL x x := by
  have hx0 : (x : Fin 24 → ℤ) ≠ 0 := fun h => hx (Subtype.ext h)
  have h := normSq_ge x.2 hx0
  rw [hL_apply]
  unfold hInt
  unfold normSq at h
  omega

theorem hL_self_pos {x : LL} (hx : x ≠ 0) : 0 < hL x x := by
  have := hL_self_ge hx
  omega

theorem hL_latHom (g : latticeO) (x y : LL) : hL (latHom g x) (latHom g y) = hL x y := by
  apply Int.cast_injective (α := ℚ)
  rw [hL_apply, hL_apply,
    hInt_eq_codeForm allOnes_mem_C weight_mod_four' (latHom g x).2 (latHom g y).2,
    hInt_eq_codeForm allOnes_mem_C weight_mod_four' x.2 y.2]
  change codeForm (ScalarKernel.ratVec (latHom g x)) (ScalarKernel.ratVec (latHom g y)) =
    codeForm (ScalarKernel.ratVec x) (ScalarKernel.ratVec y)
  rw [ratVec_latHom, ratVec_latHom, codeForm_vecMul_vecMul (mat_mul_transpose g)]

@[expose] def uL : LL := ⟨vMinus 0 1, vMinus_zero_one_mem.1⟩

theorem hL_uL_uL : hL uL uL = 4 := by
  rw [hL_apply]
  decide +kernel

@[expose] def wO : Fin 24 → ℤ := fun i => if (i : ℕ) < 8 then 2 else 0

@[expose] def wIdx (k : Fin 24) : Fin 24 → ℤ :=
  if k = 0 then vMinus 2 3 else if k = 1 then vPlus 0 1 else if k = 2 then wO else vPlus 2 k

theorem wO_eq : (fun i => 2 * bitLift ((g 0 + g 1) i)) = wO := by decide +kernel

theorem wO_mem : wO ∈ codeLattice C :=
  wO_eq ▸ two_bitLift_mem weight_mod_four' (C.add_mem (g_mem_C 0) (g_mem_C 1))

theorem wIdx_mem (k : Fin 24) : wIdx k ∈ codeLattice C := by
  unfold wIdx
  split_ifs with h0 h1 h2
  · exact (vMinus_mem (by decide : (2 : Fin 24) < 3)).1
  · exact (vPlus_mem (by decide : (0 : Fin 24) < 1)).1
  · exact wO_mem
  · refine (vPlus_mem ?_).1
    have h3 : 3 ≤ (k : ℕ) := by
      have hk0 : (k : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      have hk1 : (k : ℕ) ≠ 1 := fun h => h1 (Fin.ext h)
      have hk2 : (k : ℕ) ≠ 2 := fun h => h2 (Fin.ext h)
      omega
    exact Fin.lt_def.2 (by simp only [Fin.val_two]; omega)

@[expose] def wL (k : Fin 24) : LL := ⟨wIdx k, wIdx_mem k⟩

@[expose] def WL : Finset LL := Finset.univ.image wL

theorem mem_WL {w : LL} : w ∈ WL ↔ ∃ k, wL k = w := by
  simp [WL]

theorem hIdx_self : ∀ k : Fin 24, hInt (wIdx k) (wIdx k) = 4 := by decide +kernel

theorem hIdx_u : ∀ k : Fin 24, hInt (vMinus 0 1) (wIdx k) = 0 := by decide +kernel

theorem hIdx_three : ∀ k : Fin 24, 4 ≤ (k : ℕ) → hInt (wIdx 3) (wIdx k) = 2 := by decide +kernel

theorem hIdx_extra : hInt (wIdx 0) (wIdx 4) = 2 ∧ hInt (wIdx 1) (wIdx 2) = 2 ∧
    hInt (wIdx 3) (wIdx 2) = 2 := by decide +kernel

theorem wIdx_injective : Function.Injective wIdx := by
  intro a b h
  have : ∀ a b : Fin 24, wIdx a = wIdx b → a = b := by decide +kernel
  exact this a b h

theorem hW4 : ∀ w ∈ WL, hL w w = 4 := by
  intro w hw
  obtain ⟨k, rfl⟩ := mem_WL.1 hw
  exact hIdx_self k

theorem hWu : ∀ w ∈ WL, hL uL w = 0 := by
  intro w hw
  obtain ⟨k, rfl⟩ := mem_WL.1 hw
  exact hIdx_u k

theorem WL_nonempty : WL.Nonempty := ⟨wL 0, mem_WL.2 ⟨0, rfl⟩⟩

theorem eight_e2_eq : (8 : ℤ) • eℤ 2 = wIdx 3 + wIdx 0 := by decide +kernel

theorem eight_e_eq : ∀ i : Fin 24, 3 ≤ (i : ℕ) →
    (8 : ℤ) • eℤ i = (2 : ℤ) • wIdx i - wIdx 3 - wIdx 0 := by decide +kernel

theorem eight_e01_eq : (8 : ℤ) • (eℤ 0 + eℤ 1) = (2 : ℤ) • wIdx 1 := by decide +kernel

theorem wL_mem_closure (k : Fin 24) : wL k ∈ AddSubgroup.closure (WL : Set LL) :=
  AddSubgroup.subset_closure (mem_WL.2 ⟨k, rfl⟩)

theorem eight_e_mem (i : Fin 24) (hi : 2 ≤ (i : ℕ)) :
    (⟨(8 : ℤ) • eℤ i, smul_eight_mem_codeLattice _⟩ : LL) ∈ AddSubgroup.closure (WL : Set LL) := by
  by_cases h2 : (i : ℕ) = 2
  · have hi2 : i = 2 := Fin.ext h2
    have e : (⟨(8 : ℤ) • eℤ i, smul_eight_mem_codeLattice _⟩ : LL) = wL 3 + wL 0 :=
      Subtype.ext (by rw [hi2]; exact eight_e2_eq)
    rw [e]
    exact add_mem (wL_mem_closure 3) (wL_mem_closure 0)
  · have e : (⟨(8 : ℤ) • eℤ i, smul_eight_mem_codeLattice _⟩ : LL) =
        (2 : ℤ) • wL i - wL 3 - wL 0 := Subtype.ext (eight_e_eq i (by omega))
    rw [e]
    exact sub_mem (sub_mem (zsmul_mem (wL_mem_closure i) 2) (wL_mem_closure 3)) (wL_mem_closure 0)

theorem eight_e01_mem :
    (⟨(8 : ℤ) • (eℤ 0 + eℤ 1), smul_eight_mem_codeLattice _⟩ : LL) ∈
      AddSubgroup.closure (WL : Set LL) := by
  have e : (⟨(8 : ℤ) • (eℤ 0 + eℤ 1), smul_eight_mem_codeLattice _⟩ : LL) = (2 : ℤ) • wL 1 :=
    Subtype.ext eight_e01_eq
  rw [e]
  exact zsmul_mem (wL_mem_closure 1) 2

theorem sum_vMinus_mul (x : Fin 24 → ℤ) : ∑ i, vMinus 0 1 i * x i = 4 * x 0 - 4 * x 1 := by
  simp only [vMinus, eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem coord_eq_of_hL_uL {x : LL} (hx : hL uL x = 0) : (x : Fin 24 → ℤ) 0 = (x : Fin 24 → ℤ) 1 := by
  have h8 := eight_mul_hInt allOnes_mem_C weight_mod_four' uL.2 x.2
  rw [← hL_apply, hx] at h8
  change 8 * 0 = ∑ i, vMinus 0 1 i * (x : Fin 24 → ℤ) i at h8
  rw [sum_vMinus_mul] at h8
  omega

theorem eight_smul_eq (x : Fin 24 → ℤ) (h : x 0 = x 1) :
    (8 : ℤ) • x = x 0 • ((8 : ℤ) • (eℤ 0 + eℤ 1)) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin 24 => 2 ≤ (i : ℕ)), x i • ((8 : ℤ) • eℤ i) := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, eℤ, Pi.single_apply]
  by_cases hj : 2 ≤ (j : ℕ)
  · have hj0 : j ≠ 0 := fun e => by rw [e] at hj; exact absurd hj (by decide)
    have hj1 : j ≠ 1 := fun e => by rw [e] at hj; exact absurd hj (by decide)
    rw [Finset.sum_eq_single_of_mem j (by simpa using hj)]
    · simp [hj0, hj1, mul_comm]
    · intro b _ hb
      simp [Ne.symm hb]
  · have hsum : ∑ i ∈ Finset.univ.filter (fun i : Fin 24 => 2 ≤ (i : ℕ)),
        x i * (8 * if j = i then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : 2 ≤ (i : ℕ) := (Finset.mem_filter.1 hi).2
      have hji : j ≠ i := fun e => hj (e ▸ hi')
      simp [hji]
    rw [hsum, add_zero]
    have hj01 : j = 0 ∨ j = 1 := by
      have : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
      rcases this with h0 | h1
      · exact .inl (Fin.ext h0)
      · exact .inr (Fin.ext h1)
    rcases hj01 with rfl | rfl
    · simp [mul_comm]
    · simp [h, mul_comm]

theorem exists_smul_mem_closure_WL (x : LL) (hx : hL uL x = 0) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ AddSubgroup.closure (WL : Set LL) := by
  refine ⟨8, by norm_num, ?_⟩
  have e : (8 : ℤ) • x = (x : Fin 24 → ℤ) 0 • (⟨(8 : ℤ) • (eℤ 0 + eℤ 1),
      smul_eight_mem_codeLattice _⟩ : LL) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin 24 => 2 ≤ (i : ℕ)),
        (x : Fin 24 → ℤ) i • (⟨(8 : ℤ) • eℤ i, smul_eight_mem_codeLattice _⟩ : LL) := by
    apply Subtype.ext
    rw [AddSubgroup.coe_add, AddSubgroup.val_finsetSum]
    exact eight_smul_eq x (coord_eq_of_hL_uL hx)
  rw [e]
  refine add_mem (zsmul_mem eight_e01_mem _) (sum_mem fun i hi => zsmul_mem (eight_e_mem i ?_) _)
  exact (Finset.mem_filter.1 hi).2

abbrev graphWL : SimpleGraph WL := SimpleGraph.fromRel fun a b : WL => hL a b ≠ 0

@[expose] def vW (k : Fin 24) : WL := ⟨wL k, mem_WL.2 ⟨k, rfl⟩⟩

theorem vW_ne {a b : Fin 24} (h : a ≠ b) : vW a ≠ vW b := fun e =>
  h (wIdx_injective (congrArg (fun w : WL => ((w : LL) : Fin 24 → ℤ)) e))

theorem adj_vW {a b : Fin 24} (h : a ≠ b) (hab : hInt (wIdx a) (wIdx b) = 2) :
    graphWL.Adj (vW a) (vW b) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨vW_ne h, .inl ?_⟩
  change hInt (wIdx a) (wIdx b) ≠ 0
  rw [hab]
  norm_num

theorem reachable_vW (k : Fin 24) : graphWL.Reachable (vW 3) (vW k) := by
  by_cases h3 : k = 3
  · rw [h3]
  by_cases h4 : 4 ≤ (k : ℕ)
  · exact (adj_vW (Ne.symm h3) (hIdx_three k h4)).reachable
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by
    have hk3 : (k : ℕ) ≠ 3 := fun h => h3 (Fin.ext h)
    have : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 := by omega
    rcases this with h | h | h
    · exact .inl (Fin.ext h)
    · exact .inr (.inl (Fin.ext h))
    · exact .inr (.inr (Fin.ext h))
  have r2 : graphWL.Reachable (vW 3) (vW 2) :=
    (adj_vW (by decide) hIdx_extra.2.2).reachable
  rcases hk with rfl | rfl | rfl
  · have r4 : graphWL.Reachable (vW 3) (vW 4) := (adj_vW (by decide) (hIdx_three 4 (by decide))).reachable
    have h04 : hInt (wIdx 4) (wIdx 0) = 2 := by rw [hInt_comm]; exact hIdx_extra.1
    exact r4.trans (adj_vW (by decide) h04).reachable
  · have h21 : hInt (wIdx 2) (wIdx 1) = 2 := by rw [hInt_comm]; exact hIdx_extra.2.1
    exact r2.trans (adj_vW (by decide) h21).reachable
  · exact r2

theorem connected_graphWL : graphWL.Connected := by
  have : Nonempty WL := ⟨vW 0⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨⟨wa, hwa⟩, rfl⟩ : ∃ k, vW k = a := by
    obtain ⟨k, hk⟩ := mem_WL.1 a.2
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨⟨wb, hwb⟩, rfl⟩ : ∃ k, vW k = b := by
    obtain ⟨k, hk⟩ := mem_WL.1 b.2
    exact ⟨k, Subtype.ext hk⟩
  exact (reachable_vW _).symm.trans (reachable_vW _)

@[expose] def yL : LL := ⟨oddMin 2 (g 0), (minFamily₃_subset ⟨2, g 0, g_mem_C 0, rfl⟩).1⟩

theorem hL_uL_yL : hL uL yL = 1 := by
  rw [hL_apply]
  decide +kernel

theorem odd_hL_uL_yL : Odd (hL uL yL) := ⟨0, by rw [hL_uL_yL]; rfl⟩

theorem single_vecMul' (M : Matrix (Fin 24) (Fin 24) ℚ) (i : Fin 24) (c : ℚ) :
    Pi.single i c ᵥ* M = c • M i := by
  ext j
  simp [vecMul, dotProduct, Pi.single_apply]

theorem eq_one_of_latHom_eq (g : latticeO) (h : ∀ x : LL, latHom g x = x) : g = 1 := by
  apply mat_injective
  rw [mat_one]
  ext i j
  have hx := congrArg ScalarKernel.ratVec
    (congrArg Subtype.val (h ⟨(8 : ℤ) • eℤ i, smul_eight_mem_codeLattice _⟩))
  rw [show ScalarKernel.ratVec ((latHom g ⟨(8 : ℤ) • eℤ i, smul_eight_mem_codeLattice _⟩ : LL) :
      Fin 24 → ℤ) = ScalarKernel.ratVec ((8 : ℤ) • eℤ i) ᵥ* mat g from
      ratVec_latHom g ⟨(8 : ℤ) • eℤ i, smul_eight_mem_codeLattice _⟩] at hx
  have he : ScalarKernel.ratVec ((8 : ℤ) • eℤ i) = Pi.single i (8 : ℚ) := by
    funext k
    simp only [ScalarKernel.ratVec, eℤ, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> norm_num
  rw [he, single_vecMul'] at hx
  have hij := congrFun hx j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hij
  rw [Matrix.one_apply]
  by_cases hji : i = j
  · subst hji
    simp only [ite_true] at hij ⊢
    linarith
  · rw [ite_eq_right (Ne.symm hji)] at hij
    rw [ite_eq_right hji]
    linarith

theorem eq_one_of_trivial_mod_two_uL (g : latticeO) (hgu : latHom g uL = uL)
    (htriv : ∀ x : LL, Even (hL uL x) → ∃ m : ℤ, ∃ t : LL, latHom g x = x + m • uL + (2 : ℤ) • t) :
    g = 1 :=
  eq_one_of_latHom_eq g (eq_id_of_trivial_mod_two hL hL_symm (fun _ hx => hL_self_pos hx)
    (fun _ hx => hL_self_ge hx) hL_uL_uL WL WL_nonempty hW4 hWu exists_smul_mem_closure_WL
    connected_graphWL odd_hL_uL_yL (latHom g) (hL_latHom g) hgu htriv)

end CFSG.Monster.B.Short
