module

public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323Chief
public import CFSG.RankThree.FFModules.Transvections

public section

namespace CFSG.Quasithin.H13.L3318

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

variable {K : Type} [Field K]

theorem eq_zero_of_unitriangular_fix {n : ℕ} {v : Fin n → K}
    (hv : ∀ u ∈ unitriangular n K, (u : Matrix (Fin n) (Fin n) K) *ᵥ v = v)
    (j : Fin n) (hj : (j : ℕ) ≠ 0) : v j = 0 := by
  have hn : 0 < n := Fin.pos j
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  have hij : i₀ ≠ j := fun h => hj (by rw [← h])
  have hmem : (SpecialLinearGroup.transvection hij (1 : K)) ∈ unitriangular n K := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [SpecialLinearGroup.transvection_coe]
      have hab' : a ≠ b := ne_of_gt hab
      have hne : ¬ (i₀ = a ∧ j = b) := by
        rintro ⟨h1, -⟩
        have := Fin.lt_def.mp hab
        rw [← h1, hi₀] at this
        simp at this
      rw [Matrix.add_apply, Matrix.one_apply_ne hab', Matrix.single_apply]
      simp [hne]
    · have hne : ¬ (i₀ = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
      rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_eq,
        Matrix.single_apply]
      simp [hne]
  have h := congrFun (hv _ hmem) i₀
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Matrix.single_mulVec] at h
  simpa using h

theorem flagStabilizer_singleton {n : ℕ} (i : ℕ) :
    flagStabilizer n K {i} = stabilizer (flagSpace n K i) := by
  ext g
  rw [mem_flagStabilizer]
  simp

theorem stabilizer_one_iff [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn : 0 < n)
    (g : SpecialLinearGroup (Fin n) K) :
    g ∈ stabilizer (flagSpace n K 1) ↔
      ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) K) i ⟨0, hn⟩ = if (i : ℕ) = 0 then 1 else 0 := by
  constructor
  · intro hg i
    split_ifs with hi
    · have hi' : i = ⟨0, hn⟩ := Fin.ext hi
      subst hi'
      rcases eq_zero_or_eq_one_of_card_two hK ((g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩)
        with h0 | h1
      · exfalso
        have hcol : ∀ k : Fin n, (g : Matrix (Fin n) (Fin n) K) k ⟨0, hn⟩ = 0 := by
          intro k
          by_cases hk : (k : ℕ) = 0
          · rw [show k = ⟨0, hn⟩ from Fin.ext hk]
            exact h0
          · exact stabilizer_entries hg (l := ⟨0, hn⟩) (by simp) (by omega)
        have hdet : (g : Matrix (Fin n) (Fin n) K).det = 0 :=
          Matrix.det_eq_zero_of_column_eq_zero ⟨0, hn⟩ hcol
        rw [g.2] at hdet
        exact one_ne_zero hdet
      · exact h1
    · exact stabilizer_entries hg (l := ⟨0, hn⟩) (by simp) (by omega)
  · intro hg
    rw [← flagStabilizer_singleton]
    refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have hl0 : l = ⟨0, hn⟩ := Fin.ext (by simp; omega)
    subst hl0
    have hk0 : ¬ (k : ℕ) = 0 := by omega
    rw [hg k]
    simp [hk0]

theorem br_eq_ite [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ perfectCore (flagStabilizer n K {3}))
    {i j : Fin n} (hi : 3 ≤ (i : ℕ)) (hj : 3 ≤ (j : ℕ)) :
    (x : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
  have h3 : 3 + (n - 3) ≤ n := by omega
  have h := blkAt_eq_one_of_small (I := {3}) hK h3 (Or.inr (Set.mem_singleton 3))
    (Or.inl (by omega)) (by omega) (perfectCore_le _)
    (Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)) ⟨x, hx⟩
  have h2 := congrFun (congrFun h ⟨(i : ℕ) - 3, by omega⟩) ⟨(j : ℕ) - 3, by omega⟩
  rw [blkAt_apply] at h2
  have hi' : (⟨3 + ((i : ℕ) - 3), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
  have hj' : (⟨3 + ((j : ℕ) - 3), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  simp only [hi', hj'] at h2
  rw [h2, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have : (⟨(i : ℕ) - 3, by omega⟩ : Fin (n - 3)) ≠ ⟨(j : ℕ) - 3, by omega⟩ := by
      intro e
      apply hij
      have := congrArg Fin.val e
      simp only at this
      exact Fin.ext (by omega)
    simp [this, hij]

theorem bl_eq_zero {n : ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ flagStabilizer n K {3}) {i j : Fin n} (hi : 3 ≤ (i : ℕ)) (hj : (j : ℕ) < 3) :
    (x : Matrix (Fin n) (Fin n) K) i j = 0 :=
  stabilizer_entries (mem_flagStabilizer.mp hx 3 rfl) hj hi

theorem transvection_eq_liftT {n : ℕ} (h : 0 + 3 ≤ n) {a c : Fin n} (ha : (a : ℕ) < 3)
    (hc : (c : ℕ) < 3) (hac : a ≠ c) :
    SpecialLinearGroup.transvection hac (1 : K) =
      liftT 0 3 h (i := ⟨a, ha⟩) (j := ⟨c, hc⟩) (fun e => hac (Fin.ext (by
        have := congrArg Fin.val e
        simpa using this))) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, coe_liftT]
  congr 2 <;> exact Fin.ext (by simp [blkIdxN])

theorem transvection_mem_perfectCore_three [Finite K] {n : ℕ} {a b : Fin n} (ha : (a : ℕ) < 3)
    (hb : 3 ≤ (b : ℕ)) (hab : a ≠ b) :
    SpecialLinearGroup.transvection hab (1 : K) ∈ perfectCore (flagStabilizer n K {3}) := by
  have hn : 0 + 3 ≤ n := by have := b.isLt; omega
  obtain ⟨c, hc3, hca⟩ : ∃ c : Fin n, (c : ℕ) < 3 ∧ c ≠ a := by
    by_cases ha0 : (a : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, by simp, fun e => by
        have := congrArg Fin.val e
        simp at this
        omega⟩
    · exact ⟨⟨0, by omega⟩, by simp, fun e => by
        have := congrArg Fin.val e
        simp at this
        omega⟩
  have hac : a ≠ c := hca.symm
  have hcb : c ≠ b := fun e => by
    have := congrArg Fin.val e
    omega
  have hno : ∀ c' ∈ ({3} : Set ℕ), ¬ (0 < c' ∧ c' < 0 + 3) := by
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    omega
  have hy : SpecialLinearGroup.transvection hac (1 : K) ∈ perfectCore (flagStabilizer n K {3}) := by
    rw [transvection_eq_liftT hn ha hc3 hac]
    exact Ln2.liftT_mem_perfectCore hn le_rfl hno _
  have hz : SpecialLinearGroup.transvection hcb (1 : K) ∈ flagStabilizer n K {3} := by
    refine mem_flagStabilizer_of_entries fun k l c' hc' hl hk => ?_
    rw [Set.mem_singleton_iff] at hc'
    subst hc'
    rw [SpecialLinearGroup.transvection_coe]
    have hkl : k ≠ l := fun e => by subst e; omega
    have hne : ¬ (c = k ∧ b = l) := by
      rintro ⟨e1, e2⟩
      subst e1
      omega
    simp [Matrix.one_apply_ne hkl, hne]
  have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hac hcb hab (1 : K) 1
  rw [mul_one] at hcomm
  rw [← hcomm, commutatorElement_def]
  have hzN : SpecialLinearGroup.transvection hcb (1 : K) ∈
      Subgroup.normalizer (perfectCore (flagStabilizer n K {3}) : Set _) :=
    normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hz)
  have h1 := (Subgroup.mem_normalizer_iff.mp hzN _).mp
    ((perfectCore (flagStabilizer n K {3})).inv_mem hy)
  have : SpecialLinearGroup.transvection hac (1 : K) * SpecialLinearGroup.transvection hcb 1 *
      (SpecialLinearGroup.transvection hac 1)⁻¹ * (SpecialLinearGroup.transvection hcb 1)⁻¹ =
      SpecialLinearGroup.transvection hac (1 : K) * (SpecialLinearGroup.transvection hcb 1 *
        (SpecialLinearGroup.transvection hac 1)⁻¹ * (SpecialLinearGroup.transvection hcb 1)⁻¹) := by
    group
  rw [this]
  exact mul_mem hy h1

theorem transvection_eq_liftT_one {n : ℕ} (h : 1 + (n - 1) ≤ n) {a c : Fin n}
    (ha : 1 ≤ (a : ℕ)) (hc : 1 ≤ (c : ℕ)) (hac : a ≠ c) :
    SpecialLinearGroup.transvection hac (1 : K) =
      liftT 1 (n - 1) h (i := ⟨(a : ℕ) - 1, by omega⟩) (j := ⟨(c : ℕ) - 1, by omega⟩)
        (fun e => hac (Fin.ext (by
          have := congrArg Fin.val e
          simp only at this
          omega))) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, coe_liftT]
  congr 2 <;> exact Fin.ext (by simp [blkIdxN]; omega)

theorem transvection_mem_perfectCore_levi_one [Finite K] {n : ℕ} (hn : 4 ≤ n) {a c : Fin n}
    (ha : 1 ≤ (a : ℕ)) (hc : 1 ≤ (c : ℕ)) (hac : a ≠ c) :
    SpecialLinearGroup.transvection hac (1 : K) ∈ perfectCore (flagStabilizer n K {1}) := by
  have h : 1 + (n - 1) ≤ n := by omega
  have hno : ∀ c' ∈ ({1} : Set ℕ), ¬ (1 < c' ∧ c' < 1 + (n - 1)) := by
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    omega
  rw [transvection_eq_liftT_one h ha hc hac]
  exact Ln2.liftT_mem_perfectCore h (by omega) hno _

theorem transvection_mem_perfectCore_one [Finite K] {n : ℕ} (hn : 4 ≤ n) {a b : Fin n}
    (ha : (a : ℕ) = 0) (hb : 1 ≤ (b : ℕ)) (hab : a ≠ b) :
    SpecialLinearGroup.transvection hab (1 : K) ∈ perfectCore (flagStabilizer n K {1}) := by
  obtain ⟨c, hc1, hcb⟩ : ∃ c : Fin n, 1 ≤ (c : ℕ) ∧ c ≠ b := by
    by_cases hb1 : (b : ℕ) = 1
    · exact ⟨⟨2, by omega⟩, by simp, fun e => by
        have := congrArg Fin.val e
        simp at this
        omega⟩
    · exact ⟨⟨1, by omega⟩, by simp, fun e => by
        have := congrArg Fin.val e
        simp at this
        omega⟩
  have hac : a ≠ c := fun e => by
    have := congrArg Fin.val e
    omega
  have hz : SpecialLinearGroup.transvection hcb (1 : K) ∈ perfectCore (flagStabilizer n K {1}) :=
    transvection_mem_perfectCore_levi_one hn hc1 hb hcb
  have hy : SpecialLinearGroup.transvection hac (1 : K) ∈ flagStabilizer n K {1} := by
    refine mem_flagStabilizer_of_entries fun k l c' hc' hl hk => ?_
    rw [Set.mem_singleton_iff] at hc'
    subst hc'
    rw [SpecialLinearGroup.transvection_coe]
    have hkl : k ≠ l := fun e => by subst e; omega
    have hne : ¬ (a = k ∧ c = l) := by
      rintro ⟨e1, e2⟩
      subst e1
      omega
    simp [Matrix.one_apply_ne hkl, hne]
  have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hac hcb hab (1 : K) 1
  rw [mul_one] at hcomm
  rw [← hcomm, commutatorElement_def]
  have hyN : SpecialLinearGroup.transvection hac (1 : K) ∈
      Subgroup.normalizer (perfectCore (flagStabilizer n K {1}) : Set _) :=
    normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hy)
  have h1 := (Subgroup.mem_normalizer_iff.mp hyN _).mp hz
  exact mul_mem h1 ((perfectCore (flagStabilizer n K {1})).inv_mem hz)

section NatDual

variable {F : Type} [Field F] [Fintype F]

theorem eq_zero_of_nat_dual (f : (Fin 3 → F) →+ (Fin 3 → F))
    (hf : ∀ (g : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
      f ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = CFSG.RankThree.FFModules.dualMat g *ᵥ f v) :
    f = 0 := by
  classical
  by_cases hinj : Function.Injective f
  · exfalso
    have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
    exact CFSG.RankThree.FFModules.not_exists_natural_dual_iso
      ⟨AddEquiv.ofBijective f hbij, fun g v => hf g v⟩
  · obtain ⟨v, w, hvw, hne⟩ : ∃ v w, f v = f w ∧ v ≠ w := by
      by_contra h
      push Not at h
      exact hinj fun v w hvw => h v w hvw
    have hker : f (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hall := Chief3323.eq_top_of_invariant f.ker
      (fun g u hu => by
        rw [AddMonoidHom.mem_ker] at hu ⊢
        rw [hf, hu, Matrix.mulVec_zero])
      (AddMonoidHom.mem_ker.mpr hker) (sub_ne_zero.mpr hne)
    refine AddMonoidHom.ext fun u => ?_
    exact AddMonoidHom.mem_ker.mp (hall u)

omit [Fintype F] in
theorem exists_dualMat_eq (h : SpecialLinearGroup (Fin 3) F) :
    ∃ g : SpecialLinearGroup (Fin 3) F,
      CFSG.RankThree.FFModules.dualMat g = (h : Matrix (Fin 3) (Fin 3) F) := by
  refine ⟨(h⁻¹).transpose, ?_⟩
  rw [CFSG.RankThree.FFModules.dualMat, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
    ← Matrix.adjugate_transpose, Matrix.transpose_transpose, Matrix.adjugate_adjugate]
  · simp [h.2]
  · norm_num

theorem eq_zero_of_dual_nat (f : (Fin 3 → F) →+ (Fin 3 → F))
    (hf : ∀ (g : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
      f (CFSG.RankThree.FFModules.dualMat g *ᵥ v) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ f v) :
    f = 0 := by
  classical
  by_cases hinj : Function.Injective f
  · exfalso
    have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
    set φ := AddEquiv.ofBijective f hbij with hφ
    refine CFSG.RankThree.FFModules.not_exists_natural_dual_iso ⟨φ.symm, fun g v => ?_⟩
    apply φ.injective
    rw [AddEquiv.apply_symm_apply]
    have := hf g (φ.symm v)
    rw [show f (φ.symm v) = v from φ.apply_symm_apply v] at this
    exact this.symm
  · obtain ⟨v, w, hvw, hne⟩ : ∃ v w, f v = f w ∧ v ≠ w := by
      by_contra h
      push Not at h
      exact hinj fun v w hvw => h v w hvw
    have hker : f (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hall := Chief3323.eq_top_of_invariant f.ker
      (fun h u hu => by
        rw [AddMonoidHom.mem_ker] at hu ⊢
        obtain ⟨g, hg⟩ := exists_dualMat_eq h
        rw [← hg, hf, hu, Matrix.mulVec_zero])
      (AddMonoidHom.mem_ker.mpr hker) (sub_ne_zero.mpr hne)
    refine AddMonoidHom.ext fun u => ?_
    exact AddMonoidHom.mem_ker.mp (hall u)

end NatDual

end CFSG.Quasithin.H13.L3318
