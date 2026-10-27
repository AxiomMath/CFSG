module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318B

public section

namespace CFSG.Quasithin.H13.MSY

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem fixed_eq_zero {F : Type} [Field F] {w : Fin 3 → F}
    (hw : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).mulVec w = w) :
    w = 0 := by
  funext j
  obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := ⟨j + 1, by
    intro h
    have := congrArg (fun x : Fin 3 => (x : ℕ)) h
    fin_cases j <;> simp_all⟩
  have h := congrFun (hw (Matrix.SpecialLinearGroup.transvection hij (1 : F))) i
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Matrix.single_mulVec] at h
  simpa using h

theorem moduleAct_true_eq {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    moduleAct true ((specialLinearGroupEquivStatedSL 3 F g : ↥(StatedSL 3 F)) :
      Matrix.GeneralLinearGroup (Fin 3) F) = CFSG.RankThree.FFModules.dualMat g := by
  simp only [moduleAct, ↓reduceIte, CFSG.RankThree.FFModules.dualMat]
  congr 1

theorem moduleAct_false_eq {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    moduleAct false ((specialLinearGroupEquivStatedSL 3 F g : ↥(StatedSL 3 F)) :
      Matrix.GeneralLinearGroup (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) := by
  simp only [moduleAct, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem inf_centralizer_eq_bot_of_case3 {G₀ R Y : Subgroup G} (h3 : IsC134Case3 G₀ R Y) :
    c134Q G₀ Y ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  set Q := c134Q G₀ Y with hQ
  obtain ⟨⟨-, F, _, _, α, -, hα, ⟨-, -, βZ, -, hβZk, hβZe⟩, ⟨-, hZQ, βQ, -, hβQk, hβQe⟩⟩, -⟩ := h3
  rw [eq_bot_iff]
  rintro q ⟨hqQ, hqC⟩
  have hfix : ∀ y : ↥Y, (q : G) = (y : G) * q * ((y⁻¹ : ↥Y) : G) := fun y => by
    rw [Subgroup.coe_inv, Subgroup.mem_centralizer_iff.mp hqC y y.2, mul_inv_cancel_right]
  have h1 : ∀ i, Multiplicative.toAdd (βQ ⟨q, hqQ⟩) i = 0 := by
    intro i
    apply fixed_eq_zero
    intro g
    obtain ⟨y, hy⟩ := hα.1 (specialLinearGroupEquivStatedSL 3 F (g⁻¹.transpose))
    have h := hβQe y ⟨q, hqQ⟩ ⟨q, hqQ⟩ (hfix y) i
    rw [hy, moduleAct_true_eq] at h
    have hd : CFSG.RankThree.FFModules.dualMat g⁻¹.transpose = (g : Matrix (Fin 3) (Fin 3) F) := by
      rw [CFSG.RankThree.FFModules.dualMat, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
        ← Matrix.adjugate_transpose, Matrix.transpose_transpose, Matrix.adjugate_adjugate]
      · simp [g.2]
      · norm_num
    rw [hd] at h
    exact h.symm
  have hqZ : (q : G) ∈ centerOf Q := by
    have : (⟨q, hqQ⟩ : ↥Q) ∈ βQ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      exact h1 i
    rw [hβQk] at this
    exact Subgroup.mem_subgroupOf.mp this
  have h2 : ∀ i, Multiplicative.toAdd (βZ ⟨q, hqZ⟩) i = 0 := by
    intro i
    apply fixed_eq_zero
    intro g
    obtain ⟨y, hy⟩ := hα.1 (specialLinearGroupEquivStatedSL 3 F g)
    have h := hβZe y ⟨q, hqZ⟩ ⟨q, hqZ⟩ (hfix y) i
    rw [hy, moduleAct_false_eq] at h
    exact h.symm
  have : (⟨q, hqZ⟩ : ↥(centerOf Q)) ∈ βZ.ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext i
    exact h2 i
  rw [hβZk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact this

theorem comm_eq_one_of_case3 {G₀ R Y : Subgroup G} (h3 : IsC134Case3 G₀ R Y) {v : G}
    (hQv : ∀ q ∈ c134Q G₀ Y, q * v * q⁻¹ * v⁻¹ ∈ centerOf (c134Q G₀ Y))
    (hZv : ∀ z ∈ centerOf (c134Q G₀ Y), z * v = v * z)
    (hYv : ∀ y ∈ Y, ∀ q ∈ c134Q G₀ Y, (v⁻¹ * y⁻¹ * v * y) * q = q * (v⁻¹ * y⁻¹ * v * y)) :
    ∀ q ∈ c134Q G₀ Y, q * v = v * q := by
  classical
  obtain ⟨⟨-, F, _, _, α, -, hα, ⟨-, -, βZ, -, hβZk, hβZe⟩, ⟨hYQ, hZQ, βQ, hβQs, hβQk, hβQe⟩⟩,
    -⟩ := h3
  let κ : ↥(c134Q G₀ Y) → ↥(centerOf (c134Q G₀ Y)) := fun q =>
    ⟨(q : G) * v * (q : G)⁻¹ * v⁻¹, hQv q q.2⟩
  let Fm : ↥(c134Q G₀ Y) → (Fin 3 → F) := fun q => Multiplicative.toAdd (βZ (κ q)) 0
  have hκmul : ∀ q q' : ↥(c134Q G₀ Y), κ (q * q') = κ q * κ q' := by
    intro q q'
    apply Subtype.ext
    have hc : (q : G) * (κ q' : G) = (κ q' : G) * q :=
      (Subgroup.mem_centralizer_iff.mp (κ q').2.2 q q.2)
    have hab : (κ q : G) * (κ q' : G) = (κ q' : G) * (κ q : G) :=
      (Subgroup.mem_centralizer_iff.mp (κ q').2.2 _ (κ q).2.1)
    show (q : G) * q' * v * ((q : G) * q')⁻¹ * v⁻¹ = (κ q : G) * (κ q' : G)
    rw [hab]
    show (q : G) * q' * v * ((q : G) * q')⁻¹ * v⁻¹ =
      ((q' : G) * v * (q' : G)⁻¹ * v⁻¹) * ((q : G) * v * (q : G)⁻¹ * v⁻¹)
    have : (q : G) * q' * v * ((q : G) * q')⁻¹ * v⁻¹ =
        (q : G) * ((q' : G) * v * (q' : G)⁻¹ * v⁻¹) * v * (q : G)⁻¹ * v⁻¹ := by group
    rw [this]
    have hc' : (q : G) * ((q' : G) * v * (q' : G)⁻¹ * v⁻¹) =
        ((q' : G) * v * (q' : G)⁻¹ * v⁻¹) * q := hc
    rw [hc']
    group
  have hFmul : ∀ q q' : ↥(c134Q G₀ Y), Fm (q * q') = Fm q + Fm q' := by
    intro q q'
    show Multiplicative.toAdd (βZ (κ (q * q'))) 0 = _
    rw [hκmul, map_mul, toAdd_mul]
    rfl
  have hFone : Fm 1 = 0 := by
    have h := hFmul 1 1
    rw [mul_one] at h
    have : Fm 1 + Fm 1 = Fm 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hFU : ∀ q : ↥(c134Q G₀ Y), (q : G) ∈ centerOf (c134Q G₀ Y) → Fm q = 0 := by
    intro q hq
    have hκ : κ q = 1 := by
      apply Subtype.ext
      show (q : G) * v * (q : G)⁻¹ * v⁻¹ = 1
      rw [hZv q hq]
      group
    show Multiplicative.toAdd (βZ (κ q)) 0 = 0
    rw [hκ, map_one, toAdd_one]
    rfl
  have hFeq : ∀ q q' : ↥(c134Q G₀ Y), βQ q = βQ q' → Fm q = Fm q' := by
    intro q q' hqq
    have hk : q⁻¹ * q' ∈ βQ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqq, inv_mul_cancel]
    rw [hβQk] at hk
    have h1 := hFU _ (Subgroup.mem_subgroupOf.mp hk)
    have h2 := hFmul q (q⁻¹ * q')
    rw [mul_inv_cancel_left, h1, add_zero] at h2
    exact h2.symm
  have hFconj : ∀ (y : ↥Y) (q q' : ↥(c134Q G₀ Y)), (q' : G) = (y : G) * q * ((y⁻¹ : ↥Y) : G) →
      Fm q' = (moduleAct false (α y : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec (Fm q) := by
    intro y q q' hq'
    have hκc : ((κ q' : ↥(centerOf (c134Q G₀ Y))) : G) =
        (y : G) * (κ q : G) * ((y⁻¹ : ↥Y) : G) := by
      show (q' : G) * v * (q' : G)⁻¹ * v⁻¹ = (y : G) * ((q : G) * v * (q : G)⁻¹ * v⁻¹) * _
      rw [hq', Subgroup.coe_inv]
      set w := v⁻¹ * (y : G)⁻¹ * v * y with hw
      have hu : w * (q : G)⁻¹ = (q : G)⁻¹ * w := hYv y y.2 _ ((c134Q G₀ Y).inv_mem q.2)
      calc (y : G) * q * (y : G)⁻¹ * v * ((y : G) * q * (y : G)⁻¹)⁻¹ * v⁻¹ =
            (y : G) * q * v * (w * (q : G)⁻¹) * w⁻¹ * v⁻¹ * (y : G)⁻¹ := by
            rw [hw]; group
        _ = (y : G) * q * v * ((q : G)⁻¹ * w) * w⁻¹ * v⁻¹ * (y : G)⁻¹ := by rw [hu]
        _ = (y : G) * ((q : G) * v * (q : G)⁻¹ * v⁻¹) * (y : G)⁻¹ := by group
    exact hβZe y (κ q) (κ q') hκc 0
  have hsec : ∀ x : Fin 2 → Fin 3 → F, ∃ q : ↥(c134Q G₀ Y), βQ q = Multiplicative.ofAdd x :=
    fun x =>
    hβQs (Multiplicative.ofAdd x)
  choose s hs using hsec
  have hzero : ∀ j : Fin 2, ∀ x : Fin 3 → F, Fm (s (Pi.single j x)) = 0 := by
    intro j
    let f : (Fin 3 → F) →+ (Fin 3 → F) :=
      { toFun := fun x => Fm (s (Pi.single j x))
        map_zero' := by
          show Fm (s (Pi.single j 0)) = 0
          exact (hFeq _ _ (by rw [hs, map_one, Pi.single_zero]; rfl)).trans hFone
        map_add' := fun x x' => by
          show Fm (s (Pi.single j (x + x'))) = Fm (s (Pi.single j x)) + Fm (s (Pi.single j x'))
          rw [← hFmul]
          apply hFeq
          rw [hs, map_mul, hs, hs, Pi.single_add]
          rfl }
    have hf : f = 0 := by
      refine L3318.eq_zero_of_dual_nat f fun g x => ?_
      obtain ⟨y, hy⟩ := hα.1 (specialLinearGroupEquivStatedSL 3 F g)
      have hq' : (y : G) * (s (Pi.single j x) : G) * ((y⁻¹ : ↥Y) : G) ∈ c134Q G₀ Y := by
        rw [Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp (hYQ y.2) _).mp (s (Pi.single j x)).2
      set q' : ↥(c134Q G₀ Y) := ⟨_, hq'⟩ with hq'def
      have h1 := hFconj y (s (Pi.single j x)) q' rfl
      rw [hy, moduleAct_false_eq] at h1
      have h2 : βQ q' = βQ (s (Pi.single j ((CFSG.RankThree.FFModules.dualMat g).mulVec x))) := by
        rw [hs]
        apply Multiplicative.toAdd.injective
        funext i
        have h3 := hβQe y (s (Pi.single j x)) q' rfl i
        rw [hy, moduleAct_true_eq, hs] at h3
        rw [h3]
        simp only [toAdd_ofAdd]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Pi.single_eq_of_ne hij]
      show Fm (s (Pi.single j ((CFSG.RankThree.FFModules.dualMat g).mulVec x))) =
        (g : Matrix (Fin 3) (Fin 3) F).mulVec (Fm (s (Pi.single j x)))
      rw [← hFeq _ _ h2, h1]
    intro x
    have := congrArg (fun f : (Fin 3 → F) →+ (Fin 3 → F) => f x) hf
    exact this
  intro q hq
  have hF : Fm ⟨q, hq⟩ = 0 := by
    set x := Multiplicative.toAdd (βQ ⟨q, hq⟩) with hx
    have h1 : βQ ⟨q, hq⟩ = βQ (s (Pi.single 0 (x 0)) * s (Pi.single 1 (x 1))) := by
      rw [map_mul, hs, hs]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, ← hx]
      funext i
      fin_cases i <;> simp
    rw [hFeq _ _ h1, hFmul, hzero, hzero, add_zero]
  have hκ : κ ⟨q, hq⟩ = 1 := by
    have : κ ⟨q, hq⟩ ∈ βZ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact hF
    rw [hβZk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have := congrArg Subtype.val hκ
  change q * v * q⁻¹ * v⁻¹ = 1 at this
  calc q * v = q * v * q⁻¹ * v⁻¹ * (v * q) := by group
    _ = v * q := by rw [this, one_mul]

end CFSG.Quasithin.H13.MSY
