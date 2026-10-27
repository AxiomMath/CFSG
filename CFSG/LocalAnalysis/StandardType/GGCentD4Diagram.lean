module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTable
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.RankThree.Chevalley.SteinbergBID4Restrict
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.RankThree.PartOne.KD4T.Normal
public import CFSG.RankThree.PartOne.KE6.E6LRes

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Chevalley

private def d3b_ok0 (b : Fin Tag.E6.rank → ℤ) : Bool :=
  ([1, 2, 3, 4] : List (Fin Tag.E6.rank)).all fun j =>
    iform b (Pi.single j 1) == iform (Pi.single 0 1) (Pi.single j 1)

private def d3b_ok5 (b : Fin Tag.E6.rank → ℤ) : Bool :=
  ([1, 2, 3, 4] : List (Fin Tag.E6.rank)).all fun j =>
    iform b (Pi.single j 1) == iform (Pi.single 5 1) (Pi.single j 1)

private def d3b_beta0 : Fin Tag.E6.rank → ℤ := ![-1, -1, -2, -2, -1, 0]

private def d3b_beta5 : Fin Tag.E6.rank → ℤ := ![0, -1, -1, -2, -2, -1]

private theorem d3b_search0 :
    e6RootList.all (fun b => !d3b_ok0 b || b == Pi.single 0 1 || b == d3b_beta0) = true := by
  decide +kernel

private theorem d3b_search5 :
    e6RootList.all (fun b => !d3b_ok5 b || b == Pi.single 5 1 || b == d3b_beta5) = true := by
  decide +kernel

private theorem d3b_root0
    {b : Fin Tag.E6.rank → ℤ} (hb : IsRoot Tag.E6 b)
    (h : ∀ j ∈ d4Nodes Tag.E6, iform b (Pi.single j 1) = iform (Pi.single 0 1) (Pi.single j 1)) :
    b = Pi.single 0 1 ∨ b = d3b_beta0 := by
  have hall := List.all_eq_true.mp d3b_search0 b ((isRoot_iff_mem_e6RootList b).1 hb)
  have hok : d3b_ok0 b = true := by
    unfold d3b_ok0
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    refine ⟨h 1 ?_, h 2 ?_, h 3 ?_, h 4 ?_⟩ <;> (rw [d4Nodes, Set.mem_setOf_eq]; decide)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hall
  rcases hall with (hno | h0) | h5
  · rw [hok] at hno
    exact absurd hno (by decide)
  · exact Or.inl h0
  · exact Or.inr h5

private theorem d3b_root5
    {b : Fin Tag.E6.rank → ℤ} (hb : IsRoot Tag.E6 b)
    (h : ∀ j ∈ d4Nodes Tag.E6, iform b (Pi.single j 1) = iform (Pi.single 5 1) (Pi.single j 1)) :
    b = Pi.single 5 1 ∨ b = d3b_beta5 := by
  have hall := List.all_eq_true.mp d3b_search5 b ((isRoot_iff_mem_e6RootList b).1 hb)
  have hok : d3b_ok5 b = true := by
    unfold d3b_ok5
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    refine ⟨h 1 ?_, h 2 ?_, h 3 ?_, h 4 ?_⟩ <;> (rw [d4Nodes, Set.mem_setOf_eq]; decide)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hall
  rcases hall with (hno | h0) | h5
  · rw [hok] at hno
    exact absurd hno (by decide)
  · exact Or.inl h0
  · exact Or.inr h5

private theorem d3b_chi {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (v : WeylGroup Tag.E6)
    (hc : ∀ j : Fin Tag.E6.rank, 1 ≤ j.val → j.val ≤ 4 →
      rootChar a (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1)
    (x : Fin Tag.E6.rank → ℤ) :
    rootChar a (v • x) = rootChar a (v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) ^ x 0 *
      rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ^ x 5 := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hvx : v • x = ∑ i, x i • (v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm v (x i) _
  rw [hvx, rootChar_sum]
  simp only [rootChar_zsmul]
  refine Finset.prod_eq_mul (0 : Fin Tag.E6.rank) 5 (by decide) (fun i _ hi => ?_)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)
  have h0 : i.val ≠ 0 := fun h => hi.1 (Fin.ext h)
  have h5 : i.val ≠ 5 := fun h => hi.2 (Fin.ext h)
  have hlt : i.val < 6 := i.isLt
  rw [hc i (by omega) (by omega), one_zpow]

private theorem d3b_cube {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (x : Fin Tag.E6.rank → ℤ) : rootChar a x ^ 3 = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast (a i ^ x i) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3 i, one_zpow]

private theorem d3b_sq {L : Type} [Field L] (c : Lˣ) (h3 : c ^ 3 = 1) (hinv : c⁻¹ = c) :
    c = 1 := by
  have h2 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel c
  calc c = c * (c * c) := by rw [h2, mul_one]
    _ = c ^ 3 := (pow_three c).symm
    _ = 1 := h3

private theorem d3b_pointwise
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (v : WeylGroup Tag.E6)
    (hv : rootCharKernel a = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (y : WeylGroup Tag.E6) (hy : v * y * v⁻¹ ∈ rootCharStabilizerSubgroup a)
    (hfix : ∀ j ∈ d4Nodes Tag.E6,
      y • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1) : y = 1 := by
  classical
  have hsingle : ∀ j ∈ d4Nodes Tag.E6,
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro j hj
    refine ⟨isRoot_single Tag.E6 j, fun i hi => ?_⟩
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    exact Pi.single_eq_of_ne hij 1
  have hχ : ∀ x : Fin Tag.E6.rank → ℤ, rootChar a (v • (y • x)) = rootChar a (v • x) := by
    intro x
    have h := (mem_rootCharStabilizerSubgroup.1 hy) (v • x)
    rwa [mul_smul, mul_smul, inv_smul_smul] at h
  have hcJ : ∀ j : Fin Tag.E6.rank, 1 ≤ j.val → j.val ≤ 4 →
      rootChar a (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1 := by
    intro j h1 h4
    have hj : j ∈ d4Nodes Tag.E6 := by
      rw [d4Nodes, Set.mem_setOf_eq]
      exact ⟨h1, h4⟩
    have hk : v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel a := by
      rw [hv]
      exact ⟨_, hsingle j hj, rfl⟩
    exact hk.2
  have hne : ∀ i : Fin Tag.E6.rank, i.val = 0 ∨ i.val = 5 →
      rootChar a (v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ≠ 1 := by
    intro i hi h1
    have hk : v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel a :=
      ⟨IsRoot.smul (isRoot_single Tag.E6 i) v, h1⟩
    rw [hv] at hk
    obtain ⟨α, hα, hαe⟩ := hk
    have hαi : α = Pi.single i 1 := smul_left_cancel v hαe
    have h0 := hα.2 i (by
      rw [d4Nodes, Set.mem_setOf_eq]
      omega)
    rw [hαi, Pi.single_eq_same] at h0
    exact one_ne_zero h0
  have hpair : ∀ i : Fin Tag.E6.rank, ∀ j ∈ d4Nodes Tag.E6,
      iform (y • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) (Pi.single j 1) =
        iform (Pi.single i 1) (Pi.single j 1) := by
    intro i j hj
    have h := iform_smul y (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1)
    rw [hfix j hj] at h
    exact h
  have hbeta0 : rootChar a (v • d3b_beta0) =
      (rootChar a (v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)))⁻¹ := by
    rw [d3b_chi a v hcJ d3b_beta0]
    have e0 : d3b_beta0 0 = -1 := by decide
    have e5 : d3b_beta0 5 = 0 := by decide
    rw [e0, e5]
    simp
  have hbeta5 : rootChar a (v • d3b_beta5) =
      (rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)))⁻¹ := by
    rw [d3b_chi a v hcJ d3b_beta5]
    have e0 : d3b_beta5 0 = 0 := by decide
    have e5 : d3b_beta5 5 = -1 := by decide
    rw [e0, e5]
    simp
  have h0 : y • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 := by
    rcases d3b_root0 (IsRoot.smul (isRoot_single Tag.E6 0) y) (hpair 0) with h | h
    · exact h
    · exfalso
      have h1 := hχ (Pi.single 0 1)
      rw [h, hbeta0] at h1
      exact hne 0 (Or.inl rfl) (d3b_sq _ (d3b_cube a ha3 _) h1)
  have h5 : y • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1 := by
    rcases d3b_root5 (IsRoot.smul (isRoot_single Tag.E6 5) y) (hpair 5) with h | h
    · exact h
    · exfalso
      have h1 := hχ (Pi.single 5 1)
      rw [h, hbeta5] at h1
      exact hne 5 (Or.inr rfl) (d3b_sq _ (d3b_cube a ha3 _) h1)
  refine eq_one_of_forall_height_pos fun i => ?_
  have hi : i = 0 ∨ i = 5 ∨ i ∈ d4Nodes Tag.E6 := by
    by_cases h0' : i.val = 0
    · exact Or.inl (Fin.ext h0')
    by_cases h5' : i.val = 5
    · exact Or.inr (Or.inl (Fin.ext h5'))
    refine Or.inr (Or.inr ?_)
    rw [d4Nodes, Set.mem_setOf_eq]
    have hlt : i.val < 6 := i.isLt
    omega
  rcases hi with rfl | rfl | hi
  · rw [h0, CFSG.LieType.Chevalley.height_single]
    exact one_pos
  · rw [h5, CFSG.LieType.Chevalley.height_single]
    exact one_pos
  · rw [hfix i hi, CFSG.LieType.Chevalley.height_single]
    exact one_pos

private theorem d3b_core
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (ha3 : ∀ i, a i ^ 3 = 1)
    (v : WeylGroup Tag.E6)
    (hv : rootCharKernel a = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (w : WeylGroup Tag.E6) (hw : w ∈ rootCharStabilizerSubgroup a)
    (hw' : w ∉ kernelReflectionGroup a) :
    ∃ (u : WeylGroup Tag.E6) (ε : ℕ), u ∈ kernelReflectionGroup a ∧ (ε = 1 ∨ ε = 2) ∧
      ∀ k : Fin Tag.D4.rank,
        (u * w) • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
          v • (Pi.single (d4Idx (((CFSG.HardMathSupport.Lang.D4Three.d4Rho) ^ ε) k)) 1 :
            Fin Tag.E6.rank → ℤ) := by
  classical
  have hsingle : ∀ j ∈ d4Nodes Tag.E6,
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro j hj
    refine ⟨isRoot_single Tag.E6 j, fun i hi => ?_⟩
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    exact Pi.single_eq_of_ne hij 1
  have ha1 : a ≠ 1 := by
    intro h1
    have hk : v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel a := by
      refine ⟨IsRoot.smul (isRoot_single Tag.E6 0) v, ?_⟩
      rw [h1]
      simp [rootChar]
    rw [hv] at hk
    obtain ⟨α, hα, hαe⟩ := hk
    have hαi : α = Pi.single 0 1 := smul_left_cancel v hαe
    have h0 := hα.2 0 (by
      rw [d4Nodes, Set.mem_setOf_eq]
      decide)
    rw [hαi, Pi.single_eq_same] at h0
    exact one_ne_zero h0
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) (v⁻¹ * w * v) := by
    intro α hα
    have hα' : α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := hα
    have h1 : v • α ∈ rootCharKernel a := by
      rw [hv]
      exact ⟨α, hα', rfl⟩
    have h2 : w • v • α ∈ rootCharKernel a := by
      rw [← image_rootCharKernel (mem_rootCharStabilizerSubgroup.1 hw)]
      exact ⟨_, h1, rfl⟩
    rw [hv] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    have hβe' : v • β = w • v • α := hβe
    have h3 : (v⁻¹ * w * v) • α = β := by
      rw [mul_smul, mul_smul, ← hβe', inv_smul_smul]
    rw [h3]
    exact hβ
  obtain ⟨u', hu', w₀, hzw, π, hπ, hπact⟩ := exists_d4_action d4Base_E6 hmaps
  have hconj : ∀ x ∈ parabolicWeylGroup Tag.E6 (d4Set Tag.E6),
      v * x * v⁻¹ ∈ kernelReflectionGroup a := by
    intro x hx
    unfold parabolicWeylGroup at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨v, j, ?_, rfl⟩
      rw [hv]
      exact ⟨_, hsingle j hj, rfl⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have e : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  have hw₀ : w₀ = u'⁻¹ * (v⁻¹ * w * v) := by
    rw [hzw]
    group
  have hxmem : v * w₀ * v⁻¹ ∈ rootCharStabilizerSubgroup a := by
    have e : v * w₀ * v⁻¹ = (v * u'⁻¹ * v⁻¹) * w := by
      rw [hw₀]
      group
    rw [e]
    exact mul_mem (kernelReflectionGroup_le a (hconj _ (inv_mem hu'))) hw
  have hπ2 : π * π ≠ 1 := by
    intro hππ
    have hfixy : ∀ j ∈ d4Nodes Tag.E6,
        (w₀ * w₀) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
      intro j hj
      have hj' : j ∈ d4Set Tag.E6 := hj
      rw [mul_smul, hπact j hj', hπact (π j) (hπ.mem_d4Set hj'), ← Equiv.Perm.mul_apply, hππ]
      rfl
    have hy : v * (w₀ * w₀) * v⁻¹ ∈ rootCharStabilizerSubgroup a := by
      have e : v * (w₀ * w₀) * v⁻¹ = (v * w₀ * v⁻¹) * (v * w₀ * v⁻¹) := by group
      rw [e]
      exact mul_mem hxmem hxmem
    have h1 : w₀ * w₀ = 1 := d3b_pointwise a ha3 v hv (w₀ * w₀) hy hfixy
    have hx2 : (v * w₀ * v⁻¹) * (v * w₀ * v⁻¹) = 1 := by
      have e : (v * w₀ * v⁻¹) * (v * w₀ * v⁻¹) = v * (w₀ * w₀) * v⁻¹ := by group
      rw [e, h1]
      group
    rcases e6_three_class_table a ha3 ha1 with hEq | ⟨-, hidx⟩
    · exact hw' (by rw [hEq]; exact hw)
    · set N := (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) with hN
      haveI : N.Normal := kernelReflectionGroup_normal a
      have hcard : Nat.card (↥(rootCharStabilizerSubgroup a) ⧸ N) = 3 := hidx
      let xW : ↥(rootCharStabilizerSubgroup a) := ⟨v * w₀ * v⁻¹, hxmem⟩
      have h2 : xW * xW = 1 := Subtype.ext hx2
      have hbar2 : (QuotientGroup.mk xW : ↥(rootCharStabilizerSubgroup a) ⧸ N) ^ 2 = 1 := by
        rw [pow_two, ← QuotientGroup.mk_mul, h2, QuotientGroup.mk_one]
      have hord3 : orderOf (QuotientGroup.mk xW : ↥(rootCharStabilizerSubgroup a) ⧸ N) ∣ 3 := by
        rw [← hcard]
        exact orderOf_dvd_natCard _
      have hord2 : orderOf (QuotientGroup.mk xW : ↥(rootCharStabilizerSubgroup a) ⧸ N) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hbar2
      have hord1 : orderOf (QuotientGroup.mk xW : ↥(rootCharStabilizerSubgroup a) ⧸ N) = 1 := by
        have h := Nat.dvd_gcd hord3 hord2
        simpa using h
      have hbar1 : (QuotientGroup.mk xW : ↥(rootCharStabilizerSubgroup a) ⧸ N) = 1 :=
        orderOf_eq_one_iff.1 hord1
      have hxN : xW ∈ N := (QuotientGroup.eq_one_iff xW).1 hbar1
      have hxK : v * w₀ * v⁻¹ ∈ kernelReflectionGroup a := hxN
      apply hw'
      have e : w = (v * u'⁻¹ * v⁻¹)⁻¹ * (v * w₀ * v⁻¹) := by
        rw [hw₀]
        group
      rw [e]
      exact mul_mem (inv_mem (hconj _ (inv_mem hu'))) hxK
  have hπ1 : π ≠ 1 := fun h => hπ2 (by rw [h]; simp)
  have hε : ∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧ ∀ k : Fin Tag.D4.rank,
      π (d4Idx k) = d4Idx (((CFSG.HardMathSupport.Lang.D4Three.d4Rho) ^ ε) k) := by
    rcases hπ.eq_cycle hπ1 hπ2 with h | h
    · refine ⟨1, Or.inl rfl, fun k => ?_⟩
      rw [h]
      revert k
      decide +kernel
    · refine ⟨2, Or.inr rfl, fun k => ?_⟩
      rw [h]
      revert k
      decide +kernel
  obtain ⟨ε, hε12, hεact⟩ := hε
  refine ⟨v * u'⁻¹ * v⁻¹, ε, hconj _ (inv_mem hu'), hε12, fun k => ?_⟩
  have hd : d4Idx k ∈ d4Set Tag.E6 := by
    rw [d4Set, Set.mem_setOf_eq]
    have hk : k.val < 4 := k.isLt
    change 1 ≤ k.val + 1 ∧ k.val + 1 ≤ 4
    omega
  have e : (v * u'⁻¹ * v⁻¹) * w = v * w₀ * v⁻¹ := by
    rw [hw₀]
    group
  rw [e, mul_smul, mul_smul, inv_smul_smul, hπact (d4Idx k) hd, hεact k]

theorem ntpD4_diagram
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (ha3 : ∀ i, a i ^ 3 = 1)
    (v : WeylGroup Tag.E6)
    (hv : rootCharKernel a = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (w : WeylGroup Tag.E6) (hw : w ∈ rootCharStabilizerSubgroup a) :
    ∃ (u : WeylGroup Tag.E6) (ε : ℕ), u ∈ kernelReflectionGroup a ∧ ε < 3 ∧
      (w ∉ kernelReflectionGroup a → ε ≠ 0) ∧
      ∀ k : Fin Tag.D4.rank,
        (u * w) • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
          v • (Pi.single (d4Idx (((CFSG.HardMathSupport.Lang.D4Three.d4Rho) ^ ε) k)) 1 :
            Fin Tag.E6.rank → ℤ) := by
  by_cases hmem : w ∈ kernelReflectionGroup a
  · refine ⟨w⁻¹, 0, inv_mem hmem, by norm_num, ?_, ?_⟩
    · intro h
      exact absurd hmem h
    · intro k
      simp
  · obtain ⟨u, ε, hu, hε, hact⟩ := d3b_core a ha3 v hv w hw hmem
    refine ⟨u, ε, hu, by omega, ?_, hact⟩
    intro _
    omega

end CFSG.StandardType.NTPlane

end
