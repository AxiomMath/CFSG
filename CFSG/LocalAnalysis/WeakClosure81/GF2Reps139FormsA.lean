module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}


private theorem w1369_realizes_nat
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {H : Subgroup (MulAut W)}
    (h : (CFSG.Quasithin.FFModel.nat Γ).Realizes H ⊤ ⊥) :
    ∃ (π : ↥Γ →* ↥H) (β : W ≃* Multiplicative (ι → F)),
      Function.Surjective π ∧
      ∀ (γ : ↥Γ) (w : W), β (((π γ : ↥H) : MulAut W) w) =
        CFSG.Quasithin.natAct Γ γ (β w) := by
  obtain ⟨π, hπ⟩ := h
  simp only [CFSG.Quasithin.FFModel.nat] at hπ
  obtain ⟨hπsurj, -, -, -, -, -, -, β, hβsurj, hβker, hβeq⟩ := hπ
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : β (u * v⁻¹) = 1 := by rw [map_mul, huv, map_inv, mul_inv_cancel]
    have h2 : ((u * v⁻¹ : ↥(⊤ : Subgroup W)) : W) = 1 :=
      Subgroup.mem_bot.mp ((hβker _).1 h1)
    exact mul_inv_eq_one.mp (Subtype.ext h2)
  let βe : ↥(⊤ : Subgroup W) ≃*
      (↥(⊤ : Subgroup (Multiplicative (ι → F))) ⧸
        (⊥ : Subgroup (Multiplicative (ι → F))).subgroupOf ⊤) :=
    MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  let e : (↥(⊤ : Subgroup (Multiplicative (ι → F))) ⧸
        (⊥ : Subgroup (Multiplicative (ι → F))).subgroupOf ⊤) ≃*
      Multiplicative (ι → F) :=
    (QuotientGroup.quotientMulEquivOfEq
        (Subgroup.bot_subgroupOf (⊤ : Subgroup (Multiplicative (ι → F))))).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have he_mk : ∀ m : ↥(⊤ : Subgroup (Multiplicative (ι → F))),
      e (QuotientGroup.mk m) = (m : Multiplicative (ι → F)) := by
    intro m
    simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let β' : W ≃* Multiplicative (ι → F) := (Subgroup.topEquiv.symm).trans (βe.trans e)
  have hβ'_apply : ∀ w : W, β' w = e (β ⟨w, Subgroup.mem_top w⟩) := by
    intro w; rfl
  refine ⟨π, β', hπsurj, ?_⟩
  intro γ w
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β ⟨w, Subgroup.mem_top w⟩)
  have h1 : β ⟨((π γ : ↥H) : MulAut W) w, Subgroup.mem_top _⟩ =
      QuotientGroup.mk ⟨(CFSG.Quasithin.FFModel.nat Γ).act γ (m₀ : Multiplicative (ι → F)),
        Subgroup.mem_top _⟩ := by
    apply hβeq γ ⟨w, Subgroup.mem_top w⟩ m₀ (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact hm₀.symm
  have hβ'w : β' w = (m₀ : Multiplicative (ι → F)) := by
    rw [hβ'_apply, ← hm₀, he_mk]
  have hβ'π : β' (((π γ : ↥H) : MulAut W) w) =
      CFSG.Quasithin.natAct Γ γ (m₀ : Multiplicative (ι → F)) := by
    rw [hβ'_apply, h1, he_mk]
    rfl
  exact hβ'π.trans (congrArg (CFSG.Quasithin.natAct Γ γ) hβ'w.symm)

private theorem w1369_hasSympForm_of_model
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 2]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {K : Subgroup (MulAut W)}
    (π : ↥Γ →* ↥K) (hπ : Function.Surjective π)
    (β : W ≃* Multiplicative (ι → F))
    (hβ : ∀ (γ : ↥Γ) (w : W), β (((π γ : ↥K) : MulAut W) w) = CFSG.Quasithin.natAct Γ γ (β w))
    (G : (ι → F) →+ (ι → F) →+ F)
    (hGlin₁ : ∀ (a : F) (x y : ι → F), G (a • x) y = a * G x y)
    (hGlin₂ : ∀ (a : F) (x y : ι → F), G x (a • y) = a * G x y)
    (hGalt : ∀ x : ι → F, G x x = 0)
    (hGnd : ∀ x : ι → F, (∀ y : ι → F, G x y = 0) → x = 0)
    (hGinv : ∀ (γ : ↥Γ) (x y : ι → F),
      G (((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x)
        (((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec y) = G x y) :
    HasSympForm K := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let tr : F →+ ZMod 2 := (Algebra.trace (ZMod 2) F).toAddMonoidHom
  let B : W →* W →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun x =>
      MonoidHom.mk' (fun y => Multiplicative.ofAdd
          (tr (G (Multiplicative.toAdd (β x)) (Multiplicative.toAdd (β y)))))
        (by
          intro y z
          have hyz : Multiplicative.toAdd (β (y * z)) =
              Multiplicative.toAdd (β y) + Multiplicative.toAdd (β z) := by
            rw [map_mul, toAdd_mul]
          rw [hyz, map_add, map_add, ofAdd_add]))
      (by
        intro x y
        apply MonoidHom.ext
        intro z
        have hxy : Multiplicative.toAdd (β (x * y)) =
            Multiplicative.toAdd (β x) + Multiplicative.toAdd (β y) := by
          rw [map_mul, toAdd_mul]
        change Multiplicative.ofAdd (tr (G (Multiplicative.toAdd (β (x * y)))
            (Multiplicative.toAdd (β z)))) =
          Multiplicative.ofAdd (tr (G (Multiplicative.toAdd (β x))
            (Multiplicative.toAdd (β z)))) *
            Multiplicative.ofAdd (tr (G (Multiplicative.toAdd (β y))
              (Multiplicative.toAdd (β z))))
        rw [hxy, map_add, AddMonoidHom.add_apply, map_add, ofAdd_add])
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x hx
    have htr : ∀ y : W, tr (G (Multiplicative.toAdd (β x)) (Multiplicative.toAdd (β y))) = 0 :=
      fun y => ofAdd_eq_one.mp (hx y)
    have hv : Multiplicative.toAdd (β x) = 0 := by
      apply hGnd
      intro w
      apply (traceForm_nondegenerate (ZMod 2) F).1
      intro a
      have h3 : tr (G (Multiplicative.toAdd (β x)) (a • w)) = 0 := by
        have := htr (β.symm (Multiplicative.ofAdd (a • w)))
        simpa using this
      have : Algebra.trace (ZMod 2) F
          (G (Multiplicative.toAdd (β x)) w * a) = 0 := by
        rw [mul_comm (G (Multiplicative.toAdd (β x)) w) a,
          ← hGlin₂ a (Multiplicative.toAdd (β x)) w]
        exact h3
      simpa [Algebra.traceForm_apply] using this
    have hβx : β x = 1 := by
      rw [← ofAdd_toAdd (β x), hv, ofAdd_zero]
    exact β.injective (by rw [hβx, map_one])
  · intro x
    show Multiplicative.ofAdd (tr (G (Multiplicative.toAdd (β x)) (Multiplicative.toAdd (β x)))) = 1
    rw [hGalt, map_zero, ofAdd_zero]
  · intro k hk x y
    obtain ⟨γ, hγ⟩ := hπ ⟨k, hk⟩
    have hγ' : ((π γ : ↥K) : MulAut W) = k := congrArg Subtype.val hγ
    rw [← hγ']
    have hx' : (β (((π γ : ↥K) : MulAut W) x)).toAdd =
        ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (β x).toAdd := by
      rw [hβ γ x]
      rfl
    have hy' : (β (((π γ : ↥K) : MulAut W) y)).toAdd =
        ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (β y).toAdd := by
      rw [hβ γ y]
      rfl
    show Multiplicative.ofAdd (tr (G (β (((π γ : ↥K) : MulAut W) x)).toAdd
        (β (((π γ : ↥K) : MulAut W) y)).toAdd)) =
      Multiplicative.ofAdd (tr (G (β x).toAdd (β y).toAdd))
    rw [hx', hy', hGinv]

private lemma w1369_dot_mulVec_transpose {m n : Type*} [Fintype m] [Fintype n]
    {R : Type*} [CommSemiring R] (A : Matrix m n R) (v : n → R) (z : m → R) :
    (A *ᵥ v) ⬝ᵥ z = v ⬝ᵥ (Aᵀ *ᵥ z) := by
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

private noncomputable def w1369_Gsp (n : ℕ) (F : Type) [Field F] :
    (Fin n ⊕ Fin n → F) →+ ((Fin n ⊕ Fin n → F) →+ F) :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun w => v ⬝ᵥ (Matrix.J (Fin n) F *ᵥ w))
      (by intro w w'; simp [Matrix.mulVec_add, dotProduct_add]))
    (by intro v v'; apply AddMonoidHom.ext; intro w; simp [add_dotProduct])

private lemma w1369_Gsp_apply (n : ℕ) (F : Type) [Field F] (v w : Fin n ⊕ Fin n → F) :
    w1369_Gsp n F v w = v ⬝ᵥ (Matrix.J (Fin n) F *ᵥ w) := rfl

private lemma w1369_Jsp_eq_J (n : ℕ) (F : Type) [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.J (Fin n) F := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, CharTwo.neg_eq]

private lemma w1369_J_mulVec_eq_zero (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) (hv : Matrix.J (Fin n) F *ᵥ v = 0) : v = 0 := by
  have h2 : Matrix.J (Fin n) F *ᵥ (Matrix.J (Fin n) F *ᵥ v) = 0 := by
    rw [hv, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, Matrix.J_squared] at h2
  rw [Matrix.neg_mulVec, Matrix.one_mulVec, neg_eq_zero] at h2
  exact h2

private lemma w1369_Gsp_lin₁ (n : ℕ) (F : Type) [Field F] (a : F)
    (x y : Fin n ⊕ Fin n → F) :
    w1369_Gsp n F (a • x) y = a * w1369_Gsp n F x y := by
  rw [w1369_Gsp_apply, w1369_Gsp_apply, smul_dotProduct, smul_eq_mul]

private lemma w1369_Gsp_lin₂ (n : ℕ) (F : Type) [Field F] (a : F)
    (x y : Fin n ⊕ Fin n → F) :
    w1369_Gsp n F x (a • y) = a * w1369_Gsp n F x y := by
  rw [w1369_Gsp_apply, w1369_Gsp_apply, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma w1369_dotProduct_eq_zero {n R : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R] (v : n → R) (h : ∀ w, v ⬝ᵥ w = 0) : v = 0 := by
  funext i
  have := h (Function.update 0 i 1)
  rw [dotProduct, Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma w1369_Gsp_alt (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (x : Fin n ⊕ Fin n → F) : w1369_Gsp n F x x = 0 := by
  simp [w1369_Gsp, Matrix.J, Matrix.fromBlocks_mulVec, dotProduct, mul_comm, Matrix.neg_mulVec]

private lemma w1369_Gsp_nd (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (x : Fin n ⊕ Fin n → F) (hx : ∀ y, w1369_Gsp n F x y = 0) : x = 0 := by
  have h1 : (Matrix.J (Fin n) F)ᵀ *ᵥ x = 0 := by
    apply w1369_dotProduct_eq_zero
    intro y
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
    exact hx y
  rw [Matrix.J_transpose, Matrix.neg_mulVec, neg_eq_zero] at h1
  exact w1369_J_mulVec_eq_zero n F x h1

private lemma w1369_Gsp_inv (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (γ : ↥(StatedSp n F)) (x y : Fin n ⊕ Fin n → F) :
    w1369_Gsp n F (((γ : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x)
        (((γ : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec y)
      = w1369_Gsp n F x y := by
  set A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    ((γ : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  have hJ : Aᵀ * Matrix.J (Fin n) F * A = Matrix.J (Fin n) F := by
    have hmem := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := F)).1 γ.2
    rwa [w1369_Jsp_eq_J n F] at hmem
  rw [w1369_Gsp_apply, w1369_Gsp_apply]
  calc (A *ᵥ x) ⬝ᵥ (Matrix.J (Fin n) F *ᵥ (A *ᵥ y))
      = x ⬝ᵥ (Aᵀ *ᵥ (Matrix.J (Fin n) F *ᵥ (A *ᵥ y))) :=
        w1369_dot_mulVec_transpose A x _
    _ = x ⬝ᵥ ((Aᵀ * Matrix.J (Fin n) F * A) *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = x ⬝ᵥ (Matrix.J (Fin n) F *ᵥ y) := by rw [hJ]

private noncomputable def w1369_Gplus (n : ℕ) (F : Type) [CommRing F] :
    (Fin n ⊕ Fin n → F) →+ ((Fin n ⊕ Fin n → F) →+ F) :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun w =>
      ∑ i : Fin n, (v (Sum.inl i) * w (Sum.inr i) + v (Sum.inr i) * w (Sum.inl i)))
      (by intro w w'; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; abel))
    (by intro v v'; apply AddMonoidHom.ext; intro w
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Pi.add_apply, add_mul,
          Finset.sum_add_distrib]
        abel)

private lemma w1369_Gplus_apply (n : ℕ) (F : Type) [CommRing F]
    (v w : Fin n ⊕ Fin n → F) :
    w1369_Gplus n F v w =
      ∑ i : Fin n, (v (Sum.inl i) * w (Sum.inr i) + v (Sum.inr i) * w (Sum.inl i)) := rfl
private lemma w1369_Gplus_polar (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (v w : Fin n ⊕ Fin n → F) :
    w1369_Gplus n F v w = CFSG.Open.StatedQuadPlus n F (v + w)
      - CFSG.Open.StatedQuadPlus n F v - CFSG.Open.StatedQuadPlus n F w := by
  rw [w1369_Gplus_apply]
  simp only [CFSG.Open.StatedQuadPlus, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma w1369_Gplus_lin₁ (n : ℕ) (F : Type) [CommRing F] (a : F)
    (x y : Fin n ⊕ Fin n → F) :
    w1369_Gplus n F (a • x) y = a * w1369_Gplus n F x y := by
  rw [w1369_Gplus_apply, w1369_Gplus_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma w1369_Gplus_lin₂ (n : ℕ) (F : Type) [CommRing F] (a : F)
    (x y : Fin n ⊕ Fin n → F) :
    w1369_Gplus n F x (a • y) = a * w1369_Gplus n F x y := by
  rw [w1369_Gplus_apply, w1369_Gplus_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma w1369_Gplus_alt (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (x : Fin n ⊕ Fin n → F) : w1369_Gplus n F x x = 0 := by
  rw [w1369_Gplus_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (x (Sum.inr i)) (x (Sum.inl i))]
  exact CharTwo.add_self_eq_zero _

private lemma w1369_Gplus_nd (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (x : Fin n ⊕ Fin n → F) (hx : ∀ y, w1369_Gplus n F x y = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have h := hx (Function.update 0 (Sum.inr i) (1 : F))
    rw [w1369_Gplus_apply] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      simp [Function.update_of_ne, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · have h := hx (Function.update (0 : Fin n ⊕ Fin n → F) (Sum.inl i) (1 : F))
    rw [w1369_Gplus_apply] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      simp [Function.update_of_ne, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma w1369_Gplus_inv (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (γ : ↥(StatedOmega (StatedQuadPlus n F))) (x y : Fin n ⊕ Fin n → F) :
    w1369_Gplus n F (((γ : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x)
        (((γ : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec y)
      = w1369_Gplus n F x y := by
  set A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    ((γ : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  have hQ : ∀ v, CFSG.Open.StatedQuadPlus n F (A.mulVec v) =
      CFSG.Open.StatedQuadPlus n F v :=
    CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
      (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore (CFSG.Open.StatedQuadPlus n F) γ.2)
  rw [w1369_Gplus_polar, w1369_Gplus_polar, ← Matrix.mulVec_add,
    hQ (x + y), hQ x, hQ y]
private noncomputable def w1369_GminusInner (d : ℕ) (F : Type) [CommRing F] (b : F)
    (v : Fin d ⊕ Fin d ⊕ Fin 2 → F) :
    (Fin d ⊕ Fin d ⊕ Fin 2 → F) →+ F :=
  AddMonoidHom.mk'
    (fun w => (∑ i : Fin d, (v (Sum.inl i) * w (Sum.inr (Sum.inl i)) +
        v (Sum.inr (Sum.inl i)) * w (Sum.inl i))) +
      b * (v (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) +
        v (Sum.inr (Sum.inr 1)) * w (Sum.inr (Sum.inr 0))))
    (by intro w w'; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring)

private noncomputable def w1369_Gminus (d : ℕ) (F : Type) [CommRing F] (b : F) :
    (Fin d ⊕ Fin d ⊕ Fin 2 → F) →+ ((Fin d ⊕ Fin d ⊕ Fin 2 → F) →+ F) :=
  AddMonoidHom.mk' (fun v => w1369_GminusInner d F b v)
    (by intro v v'; apply AddMonoidHom.ext; intro w
        simp only [w1369_GminusInner, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply,
          Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring)

private lemma w1369_Gminus_apply (d : ℕ) (F : Type) [CommRing F] (b : F)
    (v w : Fin d ⊕ Fin d ⊕ Fin 2 → F) :
    w1369_Gminus d F b v w =
      (∑ i : Fin d, (v (Sum.inl i) * w (Sum.inr (Sum.inl i)) +
        v (Sum.inr (Sum.inl i)) * w (Sum.inl i))) +
      b * (v (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) +
        v (Sum.inr (Sum.inr 1)) * w (Sum.inr (Sum.inr 0))) := rfl

private lemma w1369_b_ne_zero {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (h : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  haveI : ExpChar F 2 := inferInstance
  have hbij := PerfectRing.bijective_frobenius (R := F) (p := 2)
  obtain ⟨s, hs⟩ := hbij.2 c
  have hs' : s ^ 2 = c := hs
  exact h s (by rw [hs', hb, zero_mul, add_zero]; exact CharTwo.add_self_eq_zero c)
private lemma w1369_Gminus_polar (n : ℕ) (F : Type) [Field F] [CharP F 2] (b c : F)
    (v w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :
    w1369_Gminus (n - 1) F b v w = CFSG.Open.StatedQuadMinus n F b c (v + w)
      - CFSG.Open.StatedQuadMinus n F b c v - CFSG.Open.StatedQuadMinus n F b c w := by
  rw [w1369_Gminus_apply]
  simp only [CFSG.Open.StatedQuadMinus, Pi.add_apply]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]
  simp only [Finset.sum_add_distrib]
  have hwv : (∑ x : Fin (n - 1), w (Sum.inl x) * v (Sum.inr (Sum.inl x))) =
      ∑ x : Fin (n - 1), v (Sum.inr (Sum.inl x)) * w (Sum.inl x) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hwv]
  abel

private lemma w1369_Gminus_lin₁ (d : ℕ) (F : Type) [CommRing F] (b : F) (a : F)
    (x y : Fin d ⊕ Fin d ⊕ Fin 2 → F) :
    w1369_Gminus d F b (a • x) y = a * w1369_Gminus d F b x y := by
  rw [w1369_Gminus_apply, w1369_Gminus_apply]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul]; ring

private lemma w1369_Gminus_lin₂ (d : ℕ) (F : Type) [CommRing F] (b : F) (a : F)
    (x y : Fin d ⊕ Fin d ⊕ Fin 2 → F) :
    w1369_Gminus d F b x (a • y) = a * w1369_Gminus d F b x y := by
  rw [w1369_Gminus_apply, w1369_Gminus_apply]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul]; ring

private lemma w1369_Gminus_alt (d : ℕ) (F : Type) [Field F] [CharP F 2] (b : F)
    (x : Fin d ⊕ Fin d ⊕ Fin 2 → F) : w1369_Gminus d F b x x = 0 := by
  rw [w1369_Gminus_apply]
  have h1 : (∑ i : Fin d, (x (Sum.inl i) * x (Sum.inr (Sum.inl i)) +
      x (Sum.inr (Sum.inl i)) * x (Sum.inl i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [mul_comm (x (Sum.inr (Sum.inl i))) (x (Sum.inl i))]
    exact CharTwo.add_self_eq_zero _
  rw [h1]
  have h2 : x (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1)) +
      x (Sum.inr (Sum.inr 1)) * x (Sum.inr (Sum.inr 0)) = 0 := by
    rw [mul_comm (x (Sum.inr (Sum.inr 1))) (x (Sum.inr (Sum.inr 0)))]
    exact CharTwo.add_self_eq_zero _
  rw [h2, mul_zero, add_zero]

private lemma w1369_Gminus_nd (d : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (b c : F) (hb : b ≠ 0) (x : Fin d ⊕ Fin d ⊕ Fin 2 → F)
    (hx : ∀ y, w1369_Gminus d F b x y = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have h := hx (Function.update (0 : Fin d ⊕ Fin d ⊕ Fin 2 → F) (Sum.inr (Sum.inl i)) 1)
    rw [w1369_Gminus_apply] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji; simp [Function.update_of_ne, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · rcases i with i | i
    · have h := hx (Function.update (0 : Fin d ⊕ Fin d ⊕ Fin 2 → F) (Sum.inl i) 1)
      rw [w1369_Gminus_apply] at h
      rw [Finset.sum_eq_single i] at h
      · simpa using h
      · intro j _ hji; simp [Function.update_of_ne, hji]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · fin_cases i
      · let w : Fin d ⊕ Fin d ⊕ Fin 2 → F :=
            Function.update 0 (Sum.inr (Sum.inr 1)) 1
        have h := hx w
        rw [w1369_Gminus_apply] at h
        have hsum : (∑ j : Fin d, (x (Sum.inl j) * w (Sum.inr (Sum.inl j)) +
            x (Sum.inr (Sum.inl j)) * w (Sum.inl j))) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          simp [w, Function.update_of_ne]
        rw [hsum, zero_add] at h
        simp [w] at h
        exact h.resolve_left hb
      · let w : Fin d ⊕ Fin d ⊕ Fin 2 → F :=
            Function.update 0 (Sum.inr (Sum.inr 0)) 1
        have h := hx w
        rw [w1369_Gminus_apply] at h
        have hsum : (∑ j : Fin d, (x (Sum.inl j) * w (Sum.inr (Sum.inl j)) +
            x (Sum.inr (Sum.inl j)) * w (Sum.inl j))) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          simp [w, Function.update_of_ne]
        rw [hsum, zero_add] at h
        simp [w] at h
        exact h.resolve_left hb

private lemma w1369_Gminus_inv (n : ℕ) (F : Type) [Field F] [CharP F 2] (b c : F)
    (γ : ↥(StatedOmega (StatedQuadMinus n F b c)))
    (x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :
    w1369_Gminus (n - 1) F b
        (((γ : Matrix.GeneralLinearGroup (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).mulVec x)
        (((γ : Matrix.GeneralLinearGroup (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).mulVec y)
      = w1369_Gminus (n - 1) F b x y := by
  set A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
    ((γ : Matrix.GeneralLinearGroup (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)
  have hQ : ∀ v, CFSG.Open.StatedQuadMinus n F b c (A.mulVec v) =
      CFSG.Open.StatedQuadMinus n F b c v :=
    CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
      (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore
        (CFSG.Open.StatedQuadMinus n F b c) γ.2)
  rw [w1369_Gminus_polar, w1369_Gminus_polar, ← Matrix.mulVec_add,
    hQ (x + y), hQ x, hQ y]

theorem hasSympForm_of_natSpn {K : Subgroup (MulAut W)} {m a : ℕ} (h : NatSpn K ⊤ ⊥ m a) :
    HasSympForm K := by
  rcases h with ⟨hm, F, hF, hFfin, hFcard, hreal⟩
  letI := hF
  letI := hFfin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := a) (by
    rw [← Nat.card_eq_fintype_card]; exact hFcard)
  obtain ⟨π, β, hπsurj, hβ⟩ := w1369_realizes_nat (F := F)
    (Γ := CFSG.Open.StatedSp (m / 2) F) (H := K) hreal
  exact w1369_hasSympForm_of_model (F := F) (Γ := CFSG.Open.StatedSp (m / 2) F) (K := K)
    π hπsurj β hβ (w1369_Gsp (m / 2) F)
    (w1369_Gsp_lin₁ _ _) (w1369_Gsp_lin₂ _ _) (w1369_Gsp_alt _ _)
    (w1369_Gsp_nd _ _) (w1369_Gsp_inv _ _)

theorem hasSympForm_of_natOmegaPlus {K : Subgroup (MulAut W)} {m a : ℕ}
    (h : NatOmegaPlus K ⊤ ⊥ m a) : HasSympForm K := by
  rcases h with ⟨hm, F, hF, hFfin, hFcard, hreal⟩
  letI := hF
  letI := hFfin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := a) (by
    rw [← Nat.card_eq_fintype_card]; exact hFcard)
  obtain ⟨π, β, hπsurj, hβ⟩ := w1369_realizes_nat (F := F)
    (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (m / 2) F)) (H := K) hreal
  exact w1369_hasSympForm_of_model (F := F)
    (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (m / 2) F)) (K := K)
    π hπsurj β hβ (w1369_Gplus (m / 2) F)
    (w1369_Gplus_lin₁ _ _) (w1369_Gplus_lin₂ _ _) (w1369_Gplus_alt _ _)
    (w1369_Gplus_nd _ _) (w1369_Gplus_inv _ _)

theorem hasSympForm_of_natOmegaMinus {K : Subgroup (MulAut W)} {m a : ℕ}
    (h : NatOmegaMinus K ⊤ ⊥ m a) : HasSympForm K := by
  rcases h with ⟨hm, F, hF, hFfin, b, c, hFcard, hbc, hreal⟩
  letI := hF
  letI := hFfin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := a) (by
    rw [← Nat.card_eq_fintype_card]; exact hFcard)
  have hb : b ≠ 0 := w1369_b_ne_zero hbc
  obtain ⟨π, β, hπsurj, hβ⟩ := w1369_realizes_nat (F := F)
    (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m / 2) F b c)) (H := K) hreal
  exact w1369_hasSympForm_of_model (F := F)
    (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m / 2) F b c)) (K := K)
    π hπsurj β hβ (w1369_Gminus (m / 2 - 1) F b)
    (w1369_Gminus_lin₁ (m / 2 - 1) F b) (w1369_Gminus_lin₂ (m / 2 - 1) F b)
    (w1369_Gminus_alt (m / 2 - 1) F b)
    (w1369_Gminus_nd (m / 2 - 1) F b c hb) (w1369_Gminus_inv (m / 2) F b c)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
