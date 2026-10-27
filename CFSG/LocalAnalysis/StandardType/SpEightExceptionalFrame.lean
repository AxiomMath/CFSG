module

public import CFSG.LocalAnalysis.StandardType.SpEightLineSpaces
public import CFSG.LocalAnalysis.StandardType.ElementaryAbelianNineLines

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.SpPlaneThree CFSG.StandardType.ElementaryAbelianNine

theorem ZMod_two_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

theorem exists_plane_vector {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) {M N : Subgroup ↥E} (hM : Nat.card M = 3) (hN : Nat.card N = 3)
    (hMN : M ≠ N) {z : ↥E} (hzN : z ∈ N) (hz1 : z ≠ 1) (hVM : spLineSpace M ≠ ⊥) :
    ∃ u ∈ spLineSpace M, omega u (spMat z *ᵥ u) = 1 ∧ spMat z *ᵥ u ∈ spLineSpace M ∧
      spMat z *ᵥ (spMat z *ᵥ u) = u + spMat z *ᵥ u := by
  classical
  have h3 : (3 : ZMod 2) ≠ 0 := by decide
  let D := exists_spPlaneDecomp_three h3 hcomm hexp hcard
  have hz1' : (z : StatedSp 4 (ZMod 2)) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hstab : ∀ v ∈ spLineSpace M, spEnd (z : StatedSp 4 (ZMod 2)) v ∈ spLineSpace M :=
    fun v hv => spLineSpace_stable_of_comm hcomm z hv
  have hfix : ∀ v ∈ spLineSpace M, spEnd (z : StatedSp 4 (ZMod 2)) v = v → v = 0 :=
    fun v hv h => D.eq_zero_of_fixed_spLineSpace hM hN hMN z.2 hzN hz1' hv h
  obtain ⟨u, hu, hω⟩ := exists_spForm_ne_zero_of_no_fixed (D.nondeg (some ⟨M, hM⟩))
    (hexp z z.2) hstab hfix hVM
  have hzu : spMat z *ᵥ u ∈ spLineSpace M := hstab u hu
  have hnorm := norm_eq_zero_of_no_fixed (hexp z z.2) hstab hfix hu
  rw [spEnd_eq_spMat_mulVec, spEnd_eq_spMat_mulVec] at hnorm
  refine ⟨u, hu, ?_, hzu, ?_⟩
  · have h := hω
    rw [spEnd_eq_spMat_mulVec, ← omega_eq_spForm] at h
    exact ZMod_two_eq_one_of_ne_zero h
  · refine (eq_neg_of_add_eq_zero_right hnorm).trans ?_
    funext i
    exact CharTwo.neg_eq _

theorem omega_eq_zero_of_mem_spLineSpace {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) {M N : Subgroup ↥E} (hM : Nat.card M = 3) (hN : Nat.card N = 3)
    (hMN : M ≠ N) {u v : Vec} (hu : u ∈ spLineSpace M) (hv : v ∈ spLineSpace N) :
    omega u v = 0 := by
  classical
  have h3 : (3 : ZMod 2) ≠ 0 := by decide
  let D := exists_spPlaneDecomp_three h3 hcomm hexp hcard
  have hne : (some ⟨M, hM⟩ : Option {K : Subgroup ↥E // Nat.card K = 3}) ≠ some ⟨N, hN⟩ :=
    fun h => hMN (congrArg Subtype.val (Option.some.inj h))
  rw [omega_eq_spForm]
  exact D.orth (some ⟨M, hM⟩) (some ⟨N, hN⟩) hne u hu v hv

theorem spMat_mul_mulVec {E : Subgroup ↥(StatedSp 4 (ZMod 2))} (x y : ↥E) (v : Vec) :
    spMat (x * y) *ᵥ v = spMat x *ᵥ (spMat y *ᵥ v) := by
  simp only [spMat, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem sum_aStdM_inl (k : Fin 4) (bas : Idx → Vec) :
    (∑ i, aStdM i (.inl k) • bas i) = if k = 0 then bas (.inl 0) else bas (.inr k) := by
  fin_cases k <;>
    · simp only [Fintype.sum_sum_type, Fin.sum_univ_four]
      simp [aStdM, matOf, idx]

theorem sum_aStdM_inr (k : Fin 4) (bas : Idx → Vec) :
    (∑ i, aStdM i (.inr k) • bas i) =
      if k = 0 then bas (.inr 0) else bas (.inl k) + bas (.inr k) := by
  fin_cases k <;>
    · simp only [Fintype.sum_sum_type, Fin.sum_univ_four]
      simp [aStdM, matOf, idx]

theorem sum_bStdM_inl (k : Fin 4) (bas : Idx → Vec) :
    (∑ i, bStdM i (.inl k) • bas i) =
      (if k = 0 then bas (.inr 0)
       else if k = 1 then bas (.inl 1)
       else if k = 2 then bas (.inl 2) + bas (.inr 2)
       else bas (.inr 3)) := by
  fin_cases k <;>
    · simp only [Fintype.sum_sum_type, Fin.sum_univ_four]
      simp [bStdM, matOf, idx]

theorem sum_bStdM_inr (k : Fin 4) (bas : Idx → Vec) :
    (∑ i, bStdM i (.inr k) • bas i) =
      (if k = 0 then bas (.inl 0) + bas (.inr 0)
       else if k = 1 then bas (.inr 1)
       else if k = 2 then bas (.inl 2)
       else bas (.inl 3) + bas (.inr 3)) := by
  fin_cases k <;>
    · simp only [Fintype.sum_sum_type, Fin.sum_univ_four]
      simp [bStdM, matOf, idx]

theorem exists_frame_of_action_table (A B : Matrix Idx Idx (ZMod 2)) (u f : Fin 4 → Vec)
    (huu : ∀ k l, omega (u k) (u l) = 0) (hff : ∀ k l, omega (f k) (f l) = 0)
    (huf : ∀ k l, omega (u k) (f l) = if k = l then 1 else 0)
    (hA0u : A *ᵥ u 0 = u 0) (hA0f : A *ᵥ f 0 = f 0)
    (hAu : ∀ k : Fin 4, k ≠ 0 → A *ᵥ u k = f k)
    (hAf : ∀ k : Fin 4, k ≠ 0 → A *ᵥ f k = u k + f k)
    (hB0u : B *ᵥ u 0 = f 0) (hB0f : B *ᵥ f 0 = u 0 + f 0)
    (hB1u : B *ᵥ u 1 = u 1) (hB1f : B *ᵥ f 1 = f 1)
    (hB2u : B *ᵥ u 2 = u 2 + f 2) (hB2f : B *ᵥ f 2 = u 2)
    (hB3u : B *ᵥ u 3 = f 3) (hB3f : B *ᵥ f 3 = u 3 + f 3) :
    ∃ bas : Idx → Vec, (∀ i j, omega (bas i) (bas j) = Jm i j) ∧
      (∀ j, A *ᵥ bas j = ∑ i, aStdM i j • bas i) ∧
      (∀ j, B *ᵥ bas j = ∑ i, bStdM i j • bas i) := by
  refine ⟨Sum.elim u f, ?_, ?_, ?_⟩
  · rintro (k | k) (l | l)
    · simp [Jm, Matrix.fromBlocks_apply₁₁, huu k l]
    · simp [Jm, Matrix.fromBlocks_apply₁₂, Matrix.one_apply, huf k l]
    · rw [Sum.elim_inr, Sum.elim_inl, omega_comm, huf l k, Jm, Matrix.fromBlocks_apply₂₁,
        Matrix.neg_apply, Matrix.one_apply]
      by_cases hkl : k = l
      · rw [if_pos hkl, if_pos hkl.symm]
        exact (CharTwo.neg_eq (1 : ZMod 2)).symm
      · have hlk : ¬ l = k := fun h => hkl h.symm
        rw [if_neg hkl, if_neg hlk]
        exact (CharTwo.neg_eq (0 : ZMod 2)).symm
    · simp [Jm, Matrix.fromBlocks_apply₂₂, hff k l]
  · rintro (k | k)
    · rw [sum_aStdM_inl k]
      by_cases hk : k = 0
      · subst hk; simpa using hA0u
      · rw [if_neg hk]; exact hAu k hk
    · rw [sum_aStdM_inr k]
      by_cases hk : k = 0
      · subst hk; simpa using hA0f
      · rw [if_neg hk]; simpa using hAf k hk
  · rintro (k | k)
    · rw [sum_bStdM_inl k]
      fin_cases k
      · simpa using hB0u
      · simpa using hB1u
      · simpa using hB2u
      · simpa using hB3u
    · rw [sum_bStdM_inr k]
      fin_cases k
      · simpa using hB0f
      · simpa using hB1f
      · simpa using hB2f
      · simpa using hB3f

theorem exists_frame {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) {a b : ↥E} (ha1 : a ≠ 1) (hb : b ∉ Subgroup.zpowers a)
    (hcard3 : ∀ k, Nat.card (line a b k) = 3) (hinj : Function.Injective (line a b))
    (hV : ∀ k, spLineSpace (line a b k) ≠ ⊥) :
    ∃ bas : Idx → Vec, (∀ i j, omega (bas i) (bas j) = Jm i j) ∧
      (∀ j, spMat a *ᵥ bas j = ∑ i, aStdM i j • bas i) ∧
      (∀ j, spMat b *ᵥ bas j = ∑ i, bStdM i j • bas i) := by
  have hcommE : ∀ x y : ↥E, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
  have hexpE : ∀ x : ↥E, x ^ 3 = 1 := fun x => Subtype.ext (hexp x x.2)
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  let z : Fin 4 → ↥E := ![b, a, a, a]
  let n : Fin 4 → Fin 4 := ![1, 0, 0, 0]
  have hzN : ∀ k, z k ∈ line a b (n k) := by
    intro k
    fin_cases k
    · exact Subgroup.mem_zpowers b
    all_goals exact Subgroup.mem_zpowers a
  have hz1 : ∀ k, z k ≠ 1 := by
    intro k
    fin_cases k
    · exact hb1
    all_goals exact ha1
  have hne : ∀ k, line a b k ≠ line a b (n k) := by
    intro k h
    have := hinj h
    fin_cases k <;> simp [n] at this
  have hplane := fun k => exists_plane_vector hcomm hexp hcard (hcard3 k) (hcard3 (n k)) (hne k)
    (hzN k) (hz1 k) (hV k)
  choose u hu hωu hfu hzzu using hplane
  set f : Fin 4 → Vec := fun k => spMat (z k) *ᵥ u k with hf
  have hforth : ∀ k l, k ≠ l → ∀ x ∈ spLineSpace (line a b k), ∀ y ∈ spLineSpace (line a b l),
      omega x y = 0 := fun k l hkl x hx y hy =>
    omega_eq_zero_of_mem_spLineSpace hcomm hexp hcard (hcard3 k) (hcard3 l)
      (fun h => hkl (hinj h)) hx hy
  have huu : ∀ k l, omega (u k) (u l) = 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      exact omega_self _
    · exact hforth k l h _ (hu k) _ (hu l)
  have hff : ∀ k l, omega (f k) (f l) = 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      exact omega_self _
    · exact hforth k l h _ (hfu k) _ (hfu l)
  have huf : ∀ k l, omega (u k) (f l) = if k = l then 1 else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      simpa using hωu k
    · simpa [h] using hforth k l h _ (hu k) _ (hfu l)
  have hfix : ∀ (k : Fin 4) (d : ↥E), d ∈ line a b k → ∀ v ∈ spLineSpace (line a b k),
      spMat d *ᵥ v = v := fun k d hd v hv => spEnd_eq_of_mem_spLineSpace hd hv
  have ha3 : a ^ 3 = 1 := hexpE a
  have hb3 : b ^ 3 = 1 := hexpE b
  have hid2 : b = a ^ 2 * (a * b) := by
    rw [← mul_assoc, ← pow_succ, ha3, one_mul]
  have hid3 : b = a * (a * b ^ 2) ^ 2 := by
    letI : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hcommE }
    have h4 : b ^ 4 = b := (pow_succ b 3).trans (by rw [hb3, one_mul])
    calc b = a ^ 3 * b ^ 4 := by rw [ha3, h4, one_mul]
      _ = a * (a * b ^ 2) ^ 2 := by
        rw [mul_pow, ← pow_mul, pow_succ' a 2, mul_assoc]
  have h2v : ∀ w : Vec, w + w = 0 := fun w => by
    ext i
    simp [CharTwo.add_self_eq_zero]
  have hA0u : spMat a *ᵥ u 0 = u 0 := hfix 0 a (Subgroup.mem_zpowers a) _ (hu 0)
  have hA0f : spMat a *ᵥ f 0 = f 0 := hfix 0 a (Subgroup.mem_zpowers a) _ (hfu 0)
  have hAu : ∀ k : Fin 4, k ≠ 0 → spMat a *ᵥ u k = f k := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    all_goals rfl
  have hAf : ∀ k : Fin 4, k ≠ 0 → spMat a *ᵥ f k = u k + f k := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · exact hzzu 1
    · exact hzzu 2
    · exact hzzu 3
  have hB0u : spMat b *ᵥ u 0 = f 0 := rfl
  have hB0f : spMat b *ᵥ f 0 = u 0 + f 0 := hzzu 0
  have hB1u : spMat b *ᵥ u 1 = u 1 := hfix 1 b (Subgroup.mem_zpowers b) _ (hu 1)
  have hB1f : spMat b *ᵥ f 1 = f 1 := hfix 1 b (Subgroup.mem_zpowers b) _ (hfu 1)
  have hb2 : ∀ v ∈ spLineSpace (line a b 2), spMat b *ᵥ v = spMat a *ᵥ (spMat a *ᵥ v) := by
    intro v hv
    have hab : a * b ∈ line a b 2 := Subgroup.mem_zpowers _
    calc spMat b *ᵥ v = spMat (a ^ 2 * (a * b)) *ᵥ v := congrArg (fun x => spMat x *ᵥ v) hid2
      _ = spMat (a ^ 2) *ᵥ (spMat (a * b) *ᵥ v) := spMat_mul_mulVec _ _ _
      _ = spMat (a ^ 2) *ᵥ v := by rw [hfix 2 _ hab v hv]
      _ = spMat a *ᵥ (spMat a *ᵥ v) := by rw [pow_two, spMat_mul_mulVec]
  have hB2u : spMat b *ᵥ u 2 = u 2 + f 2 := by
    rw [hb2 _ (hu 2)]
    exact hzzu 2
  have hB2f : spMat b *ᵥ f 2 = u 2 := by
    rw [hb2 _ (hfu 2)]
    have h1 : spMat a *ᵥ f 2 = u 2 + f 2 := hzzu 2
    have h2 : spMat a *ᵥ u 2 = f 2 := rfl
    rw [h1, Matrix.mulVec_add, h2, h1]
    calc f 2 + (u 2 + f 2) = u 2 + (f 2 + f 2) := by abel
      _ = u 2 := by rw [h2v, add_zero]
  have hb3' : ∀ v ∈ spLineSpace (line a b 3), spMat b *ᵥ v = spMat a *ᵥ v := by
    intro v hv
    have hab : (a * b ^ 2) ^ 2 ∈ line a b 3 := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    calc spMat b *ᵥ v = spMat (a * (a * b ^ 2) ^ 2) *ᵥ v := congrArg (fun x => spMat x *ᵥ v) hid3
      _ = spMat a *ᵥ (spMat ((a * b ^ 2) ^ 2) *ᵥ v) := spMat_mul_mulVec _ _ _
      _ = spMat a *ᵥ v := by rw [hfix 3 _ hab v hv]
  have hB3u : spMat b *ᵥ u 3 = f 3 := by
    rw [hb3' _ (hu 3)]
    rfl
  have hB3f : spMat b *ᵥ f 3 = u 3 + f 3 := by
    rw [hb3' _ (hfu 3)]
    exact hzzu 3
  exact exists_frame_of_action_table (spMat a) (spMat b) u f huu hff huf hA0u hA0f hAu hAf hB0u
    hB0f hB1u hB1f hB2u hB2f hB3u hB3f

end CFSG.StandardType.SpEight
