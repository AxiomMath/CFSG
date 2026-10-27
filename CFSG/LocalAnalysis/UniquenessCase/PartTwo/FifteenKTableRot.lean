module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableDefs
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.OrthRot

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.SectionRank.ClassicalEven.OrthRot
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def s15k_trt_pf (Q : QuadraticForm (ZMod 2) (ι → ZMod 2))
    (a : ι → ZMod 2) : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (QuadraticMap.polarBilin Q).flip a

private theorem s15k_trt_pf_apply (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) (a v : ι → ZMod 2) :
    s15k_trt_pf Q a v = QuadraticMap.polar Q v a := rfl

private theorem s15k_trt_isPolar (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) {a : ι → ZMod 2}
    (ha : Q a = 1) : IsPolar (⇑Q) a (s15k_trt_pf Q a) 1 := by
  intro v t
  rw [QuadraticMap.map_add (⇑Q) v (t • a), QuadraticMap.map_smul, ha, s15k_trt_pf_apply,
    QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]
  ring

private noncomputable def s15k_trt_plane (Q : QuadraticForm (ZMod 2) (ι → ZMod 2))
    {a b : ι → ZMod 2} (ha : Q a = 1) (hb : Q b = 1) (hab : QuadraticMap.polar Q a b = 1) :
    Plane (⇑Q) where
  a := a
  b := b
  f := s15k_trt_pf Q a
  g := s15k_trt_pf Q b
  isPolar_a := s15k_trt_isPolar Q ha
  isPolar_b := s15k_trt_isPolar Q hb
  f_b := by
    rw [s15k_trt_pf_apply, QuadraticMap.polar_comm]
    exact hab

private theorem s15k_trt_rot_mem_stab (Q : QuadraticForm (ZMod 2) (ι → ZMod 2))
    {a b z : ι → ZMod 2} (ha : Q a = 1) (hb : Q b = 1) (hab : QuadraticMap.polar Q a b = 1)
    (hza : QuadraticMap.polar Q z a = 0) (hzb : QuadraticMap.polar Q z b = 0) :
    (s15k_trt_plane Q ha hb hab).rot ∈ StatedOmega (⇑Q) ⊓ s15kVecStab z :=
  Subgroup.mem_inf.2 ⟨(s15k_trt_plane Q ha hb hab).rot_mem,
    (s15k_trt_plane Q ha hb hab).rot_fix hza hzb⟩

theorem s15k_table_rot_one (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) {z : ι → ZMod 2}
    (h : s15kPlane Q z) : 1 ≤ CFSG.Open.pRank 3 (StatedOmega (⇑Q) ⊓ s15kVecStab z) := by
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ := h
  refine s15k_table_one_le_pRank (s15k_trt_rot_mem_stab Q ha hb hab hza hzb)
    (s15k_trt_plane Q ha hb hab).rot_pow_three ?_
  intro h1
  have h2 := (s15k_trt_plane Q ha hb hab).rot_a
  rw [h1, Units.val_one, Matrix.one_mulVec] at h2
  exact (s15k_trt_plane Q ha hb hab).b_ne_smul_a 1 (by rw [one_smul]; exact h2.symm)

theorem s15k_table_rot_two (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) {z : ι → ZMod 2}
    (h : s15kPlanePair Q z) : 2 ≤ CFSG.Open.pRank 3 (StatedOmega (⇑Q) ⊓ s15kVecStab z) := by
  obtain ⟨a₀, b₀, a₁, b₁, ha₀, hb₀, hab₀, ha₁, hb₁, hab₁, h01, h02, h03, h04, hza₀, hzb₀,
    hza₁, hzb₁⟩ := h
  let P₀ := s15k_trt_plane Q ha₀ hb₀ hab₀
  let P₁ := s15k_trt_plane Q ha₁ hb₁ hab₁
  have horth : P₀.Orth P₁ :=
    { f_a := by
        show s15k_trt_pf Q a₀ a₁ = 0
        rw [s15k_trt_pf_apply, QuadraticMap.polar_comm]
        exact h01
      f_b := by
        show s15k_trt_pf Q a₀ b₁ = 0
        rw [s15k_trt_pf_apply, QuadraticMap.polar_comm]
        exact h02
      g_a := by
        show s15k_trt_pf Q b₀ a₁ = 0
        rw [s15k_trt_pf_apply, QuadraticMap.polar_comm]
        exact h03
      g_b := by
        show s15k_trt_pf Q b₀ b₁ = 0
        rw [s15k_trt_pf_apply, QuadraticMap.polar_comm]
        exact h04 }
  refine s15k_table_two_le_pRank (s15k_trt_rot_mem_stab Q ha₀ hb₀ hab₀ hza₀ hzb₀)
    (s15k_trt_rot_mem_stab Q ha₁ hb₁ hab₁ hza₁ hzb₁) P₀.rot_pow_three P₁.rot_pow_three
    (Plane.rot_commute horth) ?_ ?_
  · intro h1
    have h2 := P₀.rot_a
    rw [h1, Units.val_one, Matrix.one_mulVec] at h2
    exact P₀.b_ne_smul_a 1 (by rw [one_smul]; exact h2.symm)
  · intro k hk
    have h2 := P₁.rot_a
    rw [← hk, pow_mulVec_of_fix (P₀.rot_fix horth.f_a horth.g_a)] at h2
    exact P₁.b_ne_smul_a 1 (by rw [one_smul]; exact h2.symm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
