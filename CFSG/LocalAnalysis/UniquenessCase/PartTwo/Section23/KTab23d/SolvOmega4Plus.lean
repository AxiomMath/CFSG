module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaPlusFour

import CFSG.LieType.BorelTits.OrthogonalForm
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open Matrix

local notation "ιP" => Fin 2 ⊕ Fin 2
local notation "x₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "x₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "y₀" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "y₁" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

section StabShape

variable {K : Type} [Field K]

private lemma quadP_apply_D08 (v : ιP → K) :
    StatedQuadPlus 2 K v = v x₀ * v y₀ + v x₁ * v y₁ := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]

private lemma mulVec_apply_D08 (M : Matrix ιP ιP K) (v : ιP → K) (i : ιP) :
    (M *ᵥ v) i = M i x₀ * v x₀ + M i x₁ * v x₁ + M i y₀ * v y₀ + M i y₁ * v y₁ := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

private lemma mul_apply_D08 (M N : Matrix ιP ιP K) (i j : ιP) :
    (M * N) i j = M i x₀ * N x₀ j + M i x₁ * N x₁ j + M i y₀ * N y₀ j + M i y₁ * N y₁ j := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

private def vec_D08 (a b c d : K) : ιP → K := Sum.elim ![a, b] ![c, d]

private lemma quad_mulVec_D08 (M : Matrix ιP ιP K)
    (hQ : ∀ v, StatedQuadPlus 2 K (M *ᵥ v) = StatedQuadPlus 2 K v) (a b c d : K) :
    (M x₀ x₀ * a + M x₀ x₁ * b + M x₀ y₀ * c + M x₀ y₁ * d) *
        (M y₀ x₀ * a + M y₀ x₁ * b + M y₀ y₀ * c + M y₀ y₁ * d) +
      (M x₁ x₀ * a + M x₁ x₁ * b + M x₁ y₀ * c + M x₁ y₁ * d) *
        (M y₁ x₀ * a + M y₁ x₁ * b + M y₁ y₀ * c + M y₁ y₁ * d) = a * c + b * d := by
  have h := hQ (vec_D08 a b c d)
  rw [quadP_apply_D08, quadP_apply_D08, mulVec_apply_D08, mulVec_apply_D08, mulVec_apply_D08,
    mulVec_apply_D08] at h
  exact h

private structure StabShape_D08 (M : Matrix ιP ιP K) : Prop where
  c_ne : M x₀ x₀ ≠ 0
  col1 : M x₁ x₀ = 0
  col2 : M y₁ x₀ = 0
  col3 : M y₀ x₀ = 0
  row1 : M y₀ x₁ = 0
  row2 : M y₀ y₁ = 0
  row3 : M y₀ y₀ * M x₀ x₀ = 1
  h1 : M x₁ x₁ * M y₁ x₁ = 0
  h2 : M x₁ y₁ * M y₁ y₁ = 0
  h3 : M x₁ x₁ * M y₁ y₁ + M x₁ y₁ * M y₁ x₁ = 1
  hp : M x₀ x₁ * M y₀ y₀ + M x₁ x₁ * M y₁ y₀ + M y₁ x₁ * M x₁ y₀ = 0
  hq : M x₀ y₁ * M y₀ y₀ + M x₁ y₁ * M y₁ y₀ + M y₁ y₁ * M x₁ y₀ = 0

private theorem stabShape_D08 {M : Matrix ιP ιP K}
    (hQ : ∀ v, StatedQuadPlus 2 K (M *ᵥ v) = StatedQuadPlus 2 K v)
    (h1 : M x₁ x₀ = 0) (h2 : M y₁ x₀ = 0) (h3 : M y₀ x₀ = 0) : StabShape_D08 M := by
  have g := quad_mulVec_D08 M hQ
  have e1 := g 0 1 0 0
  have e2 := g 0 0 0 1
  have e3 := g 0 0 1 0
  have e4 := g 1 1 0 0
  have e5 := g 1 0 0 1
  have e6 := g 1 0 1 0
  have e7 := g 0 1 0 1
  have e8 := g 0 1 1 0
  have e9 := g 0 0 1 1
  rw [h1, h2, h3] at e4 e5 e6
  have c1 : M x₀ x₀ * M y₀ x₁ = 0 := by linear_combination e4 - e1
  have c2 : M x₀ x₀ * M y₀ y₁ = 0 := by linear_combination e5 - e2
  have c3 : M y₀ y₀ * M x₀ x₀ = 1 := by linear_combination e6 - e3
  have cne : M x₀ x₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at c3
    exact zero_ne_one c3
  have r1 : M y₀ x₁ = 0 := (mul_eq_zero.mp c1).resolve_left cne
  have r2 : M y₀ y₁ = 0 := (mul_eq_zero.mp c2).resolve_left cne
  rw [r1] at e1
  rw [r2] at e2
  rw [r1, r2] at e7 e8 e9
  refine ⟨cne, h1, h2, h3, r1, r2, c3, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination e1
  · linear_combination e2
  · linear_combination e7 - e1 - e2
  · linear_combination e8 - e3 - e1
  · linear_combination e9 - e3 - e2

private lemma StabShape_D08.swap {M : Matrix ιP ιP K} (hM : StabShape_D08 M)
    (ha : M x₁ x₁ = 0) : M x₁ y₁ ≠ 0 ∧ M y₁ x₁ ≠ 0 := by
  have h3 := hM.h3
  rw [ha, zero_mul, zero_add] at h3
  exact ⟨left_ne_zero_of_mul_eq_one h3, right_ne_zero_of_mul_eq_one h3⟩

private lemma StabShape_D08.diag {M : Matrix ιP ιP K} (hM : StabShape_D08 M)
    (ha : M x₁ x₁ ≠ 0) : M y₁ x₁ = 0 ∧ M x₁ y₁ = 0 := by
  have c' : M y₁ x₁ = 0 := (mul_eq_zero.mp hM.h1).resolve_left ha
  have h3 := hM.h3
  rw [c', mul_zero, add_zero] at h3
  have hd : M y₁ y₁ ≠ 0 := right_ne_zero_of_mul_eq_one h3
  exact ⟨c', (mul_eq_zero.mp hM.h2).resolve_right hd⟩

private lemma StabShape_D08.unip {M : Matrix ιP ιP K} (hM : StabShape_D08 M)
    (hc : M x₀ x₀ = 1) (ha : M x₁ x₁ = 1) :
    M y₀ y₀ = 1 ∧ M y₁ x₁ = 0 ∧ M y₁ y₁ = 1 ∧ M x₁ y₁ = 0 ∧ M x₀ x₁ = - M y₁ y₀ ∧
      M x₀ y₁ = - M x₁ y₀ := by
  have w1 : M y₀ y₀ = 1 := by
    have := hM.row3
    rwa [hc, mul_one] at this
  have c' : M y₁ x₁ = 0 := by
    have := hM.h1
    rwa [ha, one_mul] at this
  have d1 : M y₁ y₁ = 1 := by
    have := hM.h3
    rwa [ha, c', mul_zero, add_zero, one_mul] at this
  have b0 : M x₁ y₁ = 0 := by
    have := hM.h2
    rwa [d1, mul_one] at this
  refine ⟨w1, c', d1, b0, ?_, ?_⟩
  · have := hM.hp
    rw [w1, ha, c'] at this
    linear_combination this
  · have := hM.hq
    rw [w1, b0, d1] at this
    linear_combination this

private lemma comm_D08 {M N : Matrix ιP ιP K} (hM : StabShape_D08 M) (hN : StabShape_D08 N)
    (hMc : M x₀ x₀ = 1) (hMa : M x₁ x₁ = 1) (hNc : N x₀ x₀ = 1) (hNa : N x₁ x₁ = 1) :
    M * N = N * M := by
  obtain ⟨w, c', d, b, p, q⟩ := hM.unip hMc hMa
  obtain ⟨w', c'', d', b', p', q'⟩ := hN.unip hNc hNa
  have key : ∀ i j : ιP, (M * N) i j = (N * M) i j := by
    simp only [Sum.forall, Fin.forall_fin_two]
    and_intros
    all_goals
      rw [mul_apply_D08, mul_apply_D08]
      simp only [hMc, hMa, hM.col1, hM.col2, hM.col3, hM.row1, hM.row2, w, c', d, b, p, q,
        hNc, hNa, hN.col1, hN.col2, hN.col3, hN.row1, hN.row2, w', c'', d', b', p', q']
      try ring
  exact Matrix.ext key

private theorem isSolvable_of_homs_D08 {G A B C : Type} [Group G] [CommGroup A] [CommGroup B]
    [CommGroup C] (χ : G →* A) (σ : G →* B) (α : ↥(χ.ker ⊓ σ.ker) →* C)
    (hα : ∀ x y : ↥α.ker, x * y = y * x) : Group.IsSolvable G := by
  have h1 : Group.IsSolvable ↥α.ker := Group.isSolvable_of_comm hα
  have h2 : Group.IsSolvable ↥(χ.ker ⊓ σ.ker) :=
    Group.isSolvable_of_ker_le_range α.ker.subtype α (by rw [Subgroup.range_subtype])
  exact Group.isSolvable_of_ker_le_range (χ.ker ⊓ σ.ker).subtype (χ.prod σ)
    (by rw [MonoidHom.ker_prod, Subgroup.range_subtype])

private lemma mul_x1x1_D08 {G : Type} [Group G] (m : G → Matrix ιP ιP K)
    (hmul : ∀ g h, m (g * h) = m g * m h) (hs : ∀ g, StabShape_D08 (m g)) (g h : G) :
    m (g * h) x₁ x₁ = m g x₁ x₁ * m h x₁ x₁ + m g x₁ y₁ * m h y₁ x₁ := by
  rw [hmul, mul_apply_D08, (hs g).col1, (hs h).row1]
  ring

private theorem exists_swapHom_D08 {G : Type} [Group G] (m : G → Matrix ιP ιP K)
    (hmul : ∀ g h, m (g * h) = m g * m h) (hs : ∀ g, StabShape_D08 (m g)) :
    ∃ σ : G →* Multiplicative (ZMod 2), ∀ g, σ g = 1 → m g x₁ x₁ ≠ 0 := by
  classical
  have hgh := mul_x1x1_D08 m hmul hs
  refine ⟨MonoidHom.mk' (fun g => if m g x₁ x₁ = 0 then Multiplicative.ofAdd 1 else 1)
    (fun g h => ?_), fun g hg h0 => ?_⟩
  · by_cases hg0 : m g x₁ x₁ = 0
    · obtain ⟨hb, -⟩ := (hs g).swap hg0
      by_cases hh0 : m h x₁ x₁ = 0
      · obtain ⟨-, hc⟩ := (hs h).swap hh0
        have hne : m (g * h) x₁ x₁ ≠ 0 := by
          rw [hgh, hg0, hh0, zero_mul, zero_add]
          exact mul_ne_zero hb hc
        simp only [hne, hg0, hh0, if_false, if_true, ← ofAdd_add]
        decide
      · obtain ⟨hc, -⟩ := (hs h).diag hh0
        have h0 : m (g * h) x₁ x₁ = 0 := by
          rw [hgh, hg0, hc]
          ring
        simp only [h0, hg0, hh0, if_false, if_true, mul_one]
    · obtain ⟨-, hb⟩ := (hs g).diag hg0
      by_cases hh0 : m h x₁ x₁ = 0
      · have h0 : m (g * h) x₁ x₁ = 0 := by
          rw [hgh, hh0, hb]
          ring
        simp only [h0, hg0, hh0, if_false, if_true, one_mul]
      · have hne : m (g * h) x₁ x₁ ≠ 0 := by
          rw [hgh, hb, zero_mul, add_zero]
          exact mul_ne_zero hg0 hh0
        simp only [hne, hg0, hh0, if_false, mul_one]
  · simp [h0] at hg

private theorem isSolvable_of_shape_D08 {G : Type} [Group G] (m : G → Matrix ιP ιP K)
    (hmul : ∀ g h, m (g * h) = m g * m h) (hinj : Function.Injective m)
    (hs : ∀ g, StabShape_D08 (m g)) : Group.IsSolvable G := by
  obtain ⟨σ, hσ1⟩ := exists_swapHom_D08 m hmul hs
  let χ : G →* Kˣ := MonoidHom.mk' (fun g => Units.mk0 (m g x₀ x₀) (hs g).c_ne) (fun g h => by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_mk0]
    rw [hmul, mul_apply_D08, (hs h).col1, (hs h).col2, (hs h).col3]
    ring)
  have hα1 : ∀ x : ↥(χ.ker ⊓ σ.ker), m (x : G) x₁ x₁ ≠ 0 := fun x =>
    hσ1 x (MonoidHom.mem_ker.mp x.2.2)
  let α : ↥(χ.ker ⊓ σ.ker) →* Kˣ := MonoidHom.mk'
    (fun x => Units.mk0 (m (x : G) x₁ x₁) (hα1 x)) (fun x y => by
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_mk0]
      rw [Subgroup.coe_mul, mul_x1x1_D08 m hmul hs, ((hs (x : G)).diag (hα1 x)).2, zero_mul,
        add_zero])
  refine isSolvable_of_homs_D08 χ σ α fun x y => ?_
  have hc : ∀ z : ↥α.ker, m ((z : ↥(χ.ker ⊓ σ.ker)) : G) x₀ x₀ = 1 ∧
      m ((z : ↥(χ.ker ⊓ σ.ker)) : G) x₁ x₁ = 1 := fun z =>
    ⟨congrArg Units.val (MonoidHom.mem_ker.mp (z : ↥(χ.ker ⊓ σ.ker)).2.1),
      congrArg Units.val (MonoidHom.mem_ker.mp z.2)⟩
  refine Subtype.ext (Subtype.ext (hinj ?_))
  simp only [Subgroup.coe_mul]
  rw [hmul, hmul]
  exact comm_D08 (hs _) (hs _) (hc x).1 (hc x).2 (hc y).1 (hc y).2

private lemma col_D08 {M : Matrix ιP ιP K} {c : K}
    (hc : M *ᵥ KTabC.e1P K = c • KTabC.e1P K) :
    M x₁ x₀ = 0 ∧ M y₁ x₀ = 0 ∧ M y₀ x₀ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [mulVec_apply_D08, KTabC.e1P, Pi.single_apply] using congrFun hc x₁
  · simpa [mulVec_apply_D08, KTabC.e1P, Pi.single_apply] using congrFun hc y₁
  · simpa [mulVec_apply_D08, KTabC.e1P, Pi.single_apply] using congrFun hc y₀

end StabShape

theorem isSolvable_lineStab_statedOmegaPlus_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    Group.IsSolvable ↥(lineStab (StatedOmega (StatedQuadPlus 2 K)) (KTabC.e1P K)) := by
  refine isSolvable_of_shape_D08
    (fun g => (((g : ↥(StatedOmega (StatedQuadPlus 2 K))) : GL ιP K) : Matrix ιP ιP K))
    (fun g h => rfl) (fun g h hgh => Subtype.ext (Subtype.ext (Units.ext hgh))) fun g => ?_
  obtain ⟨c, hc⟩ := g.2
  obtain ⟨h1, h2, h3⟩ := col_D08 hc
  exact stabShape_D08 (fun v => CFSG.LieType.BorelTits.orthGroup_preserves _
    (CFSG.LieType.BorelTits.statedOmega_le_orthGroup _
      (g : ↥(StatedOmega (StatedQuadPlus 2 K))).2) v) h1 h2 h3

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
