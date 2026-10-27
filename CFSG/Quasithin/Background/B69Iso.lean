module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinNonIso

public section

namespace CFSG.Quasithin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace B69

variable {n : ℕ} {K : Type} [Field K]

theorem unitriangularMatrix_single (p : {ij : Fin n × Fin n // ij.1 < ij.2}) (c : K) :
    unitriangularMatrix (Pi.single p c) = 1 + Matrix.single p.1.1 p.1.2 c := by
  ext i j
  simp only [unitriangularMatrix, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases h : i < j
  · have hne : i ≠ j := ne_of_lt h
    simp only [h, dite_true, hne, ite_false, zero_add]
    by_cases hp : (i = p.1.1 ∧ j = p.1.2)
    · have : (⟨(i, j), h⟩ : {ij : Fin n × Fin n // ij.1 < ij.2}) = p := by
        apply Subtype.ext
        exact Prod.ext hp.1 hp.2
      rw [this, Pi.single_eq_same]
      simp [hp.1.symm, hp.2.symm]
    · have : (⟨(i, j), h⟩ : {ij : Fin n × Fin n // ij.1 < ij.2}) ≠ p := by
        intro heq
        apply hp
        have := congrArg Subtype.val heq
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      rw [Pi.single_eq_of_ne this]
      have hp' : ¬ (p.1.1 = i ∧ p.1.2 = j) := fun h' => hp ⟨h'.1.symm, h'.2.symm⟩
      simp [hp']
  · by_cases hij : i = j
    · subst hij
      have hp : ¬ (p.1.1 = i ∧ p.1.2 = i) := fun h' => by
        have := p.2
        rw [h'.1, h'.2] at this
        exact lt_irrefl _ this
      simp [hp]
    · have hp : ¬ (p.1.1 = i ∧ p.1.2 = j) := fun h' => by
        have := p.2
        rw [h'.1, h'.2] at this
        exact h this
      simp [h, hij, hp]

@[expose] noncomputable def elemU (a b : Fin n) (hab : a < b) (c : K) : unitriangular n K :=
  (unitriangularEquiv n).symm (Pi.single ⟨(a, b), hab⟩ c)

theorem coe_elemU (a b : Fin n) (hab : a < b) (c : K) :
    (((elemU a b hab c : unitriangular n K) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + Matrix.single a b c :=
  unitriangularMatrix_single ⟨(a, b), hab⟩ c

theorem mem_center_aux {u : unitriangular n K} (hu : u ∈ Subgroup.center (unitriangular n K))
    {a b : Fin n} (hab : a < b) :
    (∀ i, i ≠ a → ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i a = 0) ∧
    (∀ j, j ≠ b → ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) b j = 0) := by
  have hc := Subgroup.mem_center_iff.mp hu (elemU a b hab 1)
  have hm : (((elemU a b hab 1 : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * (((u : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (((u : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * (((elemU a b hab 1 : unitriangular n K) :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg (fun w : unitriangular n K =>
      ((w : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) hc
  rw [coe_elemU] at hm
  set M : Matrix (Fin n) (Fin n) K := ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hM
  have hcomm : Matrix.single a b (1 : K) * M = M * Matrix.single a b (1 : K) := by
    rw [add_mul, mul_add, one_mul, mul_one] at hm
    exact add_left_cancel hm
  have hdiag : ∀ i, M i i = 1 := u.2.2
  constructor
  · intro i hi
    have h := congrFun (congrFun hcomm i) b
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (h := hi)] at h
    simpa using h.symm
  · intro j hj
    have h := congrFun (congrFun hcomm a) j
    rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne (hbj := hj)] at h
    simpa using h



theorem entry_zero_of_mem_center {u : unitriangular n K}
    (hu : u ∈ Subgroup.center (unitriangular n K)) {i j : Fin n} (hij : i < j)
    (h : i.val ≠ 0 ∨ j.val + 1 ≠ n) :
    ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
  by_cases hj : j.val + 1 = n
  · have hi0 : i.val ≠ 0 := by
      rcases h with h | h
      · exact h
      · exact absurd hj h
    have hlt : (⟨i.val - 1, by omega⟩ : Fin n) < i := by
      show i.val - 1 < i.val
      omega
    exact (mem_center_aux hu hlt).2 j (ne_of_gt hij)
  · have hlt : j < (⟨j.val + 1, by omega⟩ : Fin n) := by
      show j.val < j.val + 1
      omega
    exact (mem_center_aux hu hlt).1 i (ne_of_lt hij)

@[expose] def corner0 (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

@[expose] def corner1 (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

theorem corner_lt (hn : 2 ≤ n) : corner0 hn < corner1 hn := by
  show 0 < n - 1
  omega

@[expose] noncomputable def cornerElem (hn : 2 ≤ n) (c : K) : unitriangular n K :=
  elemU (corner0 hn) (corner1 hn) (corner_lt hn) c

theorem coe_cornerElem (hn : 2 ≤ n) (c : K) :
    (((cornerElem hn c : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + Matrix.single (corner0 hn) (corner1 hn) c :=
  coe_elemU _ _ _ _

theorem cornerElem_mul (hn : 2 ≤ n) (c c' : K) :
    cornerElem hn c * cornerElem hn c' = cornerElem hn (c + c') := by
  apply Subtype.ext
  apply Subtype.ext
  show (((cornerElem hn c : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * (((cornerElem hn c' : unitriangular n K) :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
  rw [coe_cornerElem, coe_cornerElem]
  show _ = (((cornerElem hn (c + c') : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)
  rw [coe_cornerElem]
  have h0 : corner1 hn ≠ corner0 hn := ne_of_gt (corner_lt hn)
  have e1 : Matrix.single (corner0 hn) (corner1 hn) c * Matrix.single (corner0 hn) (corner1 hn) c' =
      0 := Matrix.single_mul_single_of_ne c (corner0 hn) (corner1 hn) (corner0 hn) h0 c'
  have e2 : (1 + Matrix.single (corner0 hn) (corner1 hn) c) *
      (1 + Matrix.single (corner0 hn) (corner1 hn) c') =
      1 + Matrix.single (corner0 hn) (corner1 hn) c + Matrix.single (corner0 hn) (corner1 hn) c' +
        Matrix.single (corner0 hn) (corner1 hn) c * Matrix.single (corner0 hn) (corner1 hn) c' := by
    noncomm_ring
  rw [e2, e1, add_zero, Matrix.single_add]
  abel

theorem cornerElem_mem_center (hn : 2 ≤ n) (c : K) :
    cornerElem hn c ∈ Subgroup.center (unitriangular n K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  show (((g : unitriangular n K) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((cornerElem hn c : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
    (((cornerElem hn c : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * (((g : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)
  rw [coe_cornerElem, mul_add, add_mul, mul_one, one_mul]
  congr 1
  set G : Matrix (Fin n) (Fin n) K :=
    (((g : unitriangular n K) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hG
  have hcol : ∀ i, i ≠ corner0 hn → G i (corner0 hn) = 0 := by
    intro i hi
    apply g.2.1
    show corner0 hn < i
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    show 0 < i.val
    omega
  have hrow : ∀ j, j ≠ corner1 hn → G (corner1 hn) j = 0 := by
    intro j hj
    apply g.2.1
    show j.val < n - 1
    have : j.val ≠ n - 1 := fun h => hj (Fin.ext h)
    have := j.isLt
    omega
  have hdiag : ∀ i, G i i = 1 := g.2.2
  ext i j
  by_cases hi : i = corner0 hn <;> by_cases hj : j = corner1 hn
  · subst hi; subst hj
    simp [hdiag]
  · subst hi
    rw [Matrix.mul_single_apply_of_ne (hbj := hj), Matrix.single_mul_apply_same, hrow j hj]
    simp
  · subst hj
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (h := hi), hcol i hi]
    simp
  · rw [Matrix.mul_single_apply_of_ne (hbj := hj), Matrix.single_mul_apply_of_ne (h := hi)]

theorem cornerElem_injective (hn : 2 ≤ n) : Function.Injective (cornerElem (K := K) hn) := by
  intro c c' h
  have := congrArg (fun w : unitriangular n K =>
    ((w : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) (corner0 hn) (corner1 hn)) h
  simp only [coe_cornerElem] at this
  have hne : corner0 hn ≠ corner1 hn := ne_of_lt (corner_lt hn)
  simpa [Matrix.add_apply, Matrix.one_apply, hne] using this

theorem eq_cornerElem_of_mem_center (hn : 2 ≤ n) {u : unitriangular n K}
    (hu : u ∈ Subgroup.center (unitriangular n K)) :
    u = cornerElem hn
      (((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) (corner0 hn) (corner1 hn)) := by
  apply Subtype.ext
  apply Subtype.ext
  show ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    (((cornerElem hn _ : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)
  rw [coe_cornerElem]
  ext i j
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · by_cases hc : i = corner0 hn ∧ j = corner1 hn
    · obtain ⟨rfl, rfl⟩ := hc
      simp [(ne_of_lt hij)]
    · have hne : i ≠ j := ne_of_lt hij
      have hc' : ¬ (corner0 hn = i ∧ corner1 hn = j) := fun h => hc ⟨h.1.symm, h.2.symm⟩
      have hz := entry_zero_of_mem_center hu hij (by
        by_contra hh
        push Not at hh
        exact hc ⟨Fin.ext hh.1, Fin.ext (by have := j.isLt; unfold corner1; simp; omega)⟩)
      simp [hz, hne, hc']
  · have hne : corner0 hn ≠ corner1 hn := ne_of_lt (corner_lt hn)
    have hc' : ¬ (corner0 hn = i ∧ corner1 hn = i) := fun h => hne (h.1.trans h.2.symm)
    simp [u.2.2 i, hc']
  · have hc' : ¬ (corner0 hn = i ∧ corner1 hn = j) := by
      rintro ⟨h1, h2⟩
      have h3 : corner0 hn < corner1 hn := corner_lt hn
      rw [h1, h2] at h3
      exact absurd hij (not_lt.mpr h3.le)
    have hne : i ≠ j := ne_of_gt hij
    simp [u.2.1 i j hij, hne, hc']

theorem cornerElem_zero (hn : 2 ≤ n) : cornerElem (K := K) hn 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  show (((cornerElem hn (0 : K) : unitriangular n K) : SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K) = 1
  rw [coe_cornerElem]
  simp

theorem card_center_unitriangular (hn : 2 ≤ n) :
    Nat.card (Subgroup.center (unitriangular n K)) = Nat.card K := by
  let ι : Multiplicative K →* unitriangular n K :=
    { toFun := fun c => cornerElem hn (Multiplicative.toAdd c)
      map_one' := cornerElem_zero hn
      map_mul' := fun c c' => (cornerElem_mul hn _ _).symm }
  have hinj : Function.Injective ι := fun c c' h =>
    Multiplicative.toAdd.injective (cornerElem_injective hn h)
  have hrange : Subgroup.center (unitriangular n K) = ι.range := by
    ext u
    constructor
    · intro hu
      exact ⟨Multiplicative.ofAdd (((u : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) (corner0 hn) (corner1 hn)), (eq_cornerElem_of_mem_center hn hu).symm⟩
    · rintro ⟨c, rfl⟩
      exact cornerElem_mem_center hn _
  rw [hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr Multiplicative.toAdd

theorem card_center_sylow_projectiveSL [Finite K] [CharP K 2] (hn : 2 ≤ n)
    (T : Sylow 2 (projectiveSL n K)) :
    Nat.card (Subgroup.center (T : Subgroup (projectiveSL n K))) = Nat.card K := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := n) (by omega)
  have e1 : (T : Subgroup (projectiveSL n K)) ≃* (P₀ : Subgroup (projectiveSL n K)) :=
    Sylow.equiv T P₀
  have e2 : (P₀ : Subgroup (projectiveSL n K)) ≃* unitriangular n K :=
    (MulEquiv.subgroupCongr hP₀).trans (unitriangularEquivProj n).symm
  rw [Nat.card_congr (Subgroup.centerCongr (e1.trans e2)).toEquiv]
  exact card_center_unitriangular hn

theorem card_eq_of_equiv_projectiveSL {m : ℕ} {F : Type} [Field F] [Finite K] [Finite F]
    [CharP K 2] [CharP F 2] (hm : 2 ≤ m) (hn : 2 ≤ n)
    (e : projectiveSL m K ≃* projectiveSL n F) : Nat.card K = Nat.card F := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (projectiveSL m K)))
  let f : projectiveSL m K →* projectiveSL n F := e.toMonoidHom
  have hfs : Function.Surjective f := e.surjective
  have hfi : Function.Injective f := e.injective
  have e3 : (T : Subgroup (projectiveSL m K)) ≃*
      ((T.mapSurjective hfs : Sylow 2 (projectiveSL n F)) : Subgroup (projectiveSL n F)) :=
    (T : Subgroup (projectiveSL m K)).equivMapOfInjective f hfi
  have h1 := card_center_sylow_projectiveSL hm T
  have h2 := card_center_sylow_projectiveSL hn (T.mapSurjective hfs)
  rw [← h1, ← h2]
  exact Nat.card_congr (Subgroup.centerCongr e3).toEquiv

open CFSG.Assembly.LowTwoRank in
noncomputable def statedProjEquivProjectiveSL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n := n) (K := K))).symm

open CFSG.Assembly.LowTwoRank in
theorem not_equiv_sl_four_psl_three {G : Type} [Group G] {K F : Type} [Field K] [Field F]
    [Finite K] [Finite F] (hK : Nat.card K = 2) (hF : Nat.card F = 4)
    (e4 : G ≃* StatedProj (StatedSL 4 K)) (e3 : G ≃* StatedProj (StatedSL 3 F)) : False := by
  have hcK : CharP K 2 := CFSG.QuasithinUnique.Fin257.charP_two_of_card (f := 1) (by rw [hK]; norm_num)
  have hcF : CharP F 2 := CFSG.QuasithinUnique.Fin257.charP_two_of_card (f := 2) (by rw [hF]; norm_num)
  have e : projectiveSL 4 K ≃* projectiveSL 3 F :=
    (statedProjEquivProjectiveSL 4 K).symm.trans
      (e4.symm.trans (e3.trans (statedProjEquivProjectiveSL 3 F)))
  have := card_eq_of_equiv_projectiveSL (by norm_num) (by norm_num) e
  omega

end B69

end CFSG.Quasithin
