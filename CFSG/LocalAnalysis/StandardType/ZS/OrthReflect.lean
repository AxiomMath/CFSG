module

public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.LocalAnalysis.StandardType.ZS.ReflAxis

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem isIsom_mul {Q : QuadraticForm (ZMod p) U} {g h : U ≃ₗ[ZMod p] U}
    (hg : IsIsom p Q g) (hh : IsIsom p Q h) : IsIsom p Q (g * h) := by
  intro v
  rw [LinearEquiv.mul_apply, hg, hh]

theorem isIsom_inv {Q : QuadraticForm (ZMod p) U} {g : U ≃ₗ[ZMod p] U}
    (hg : IsIsom p Q g) : IsIsom p Q g⁻¹ := by
  intro v
  have h := hg (g⁻¹ v)
  simpa using h.symm

theorem IsIsom.polar_apply {Q : QuadraticForm (ZMod p) U} {g : U ≃ₗ[ZMod p] U}
    (hg : IsIsom p Q g) (u v : U) :
    QuadraticMap.polar Q (g u) (g v) = QuadraticMap.polar Q u v :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg) u v

theorem isIsom_reflect (Q : QuadraticForm (ZMod p) U) (a : U) :
    IsIsom p Q (CFSG.ClassicalGroups.Orthogonal.reflect Q a) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q a)

theorem reflect_apply_self {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {a : V} (ha : Q a ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a a = -a := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply ha,
    CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    mul_div_cancel_right₀ (2 : K) ha, two_smul]
  abel

theorem IsIsom.polar_eq_zero_of_apply_eq_neg_of_apply_eq (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} {t : U ≃ₗ[ZMod p] U} (hti : IsIsom p Q t) {x z : U}
    (htx : t x = -x) (htz : t z = z) : QuadraticMap.polar Q x z = 0 := by
  have h := hti.polar_apply x z
  rw [htx, htz, QuadraticMap.polar_neg_left] at h
  exact eq_zero_of_eq_neg (ZMod.prime_ne_zero p 2 hp) h.symm

theorem isRefl_reflect (hp : p ≠ 2) [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    {a : U} (ha : Q a ≠ 0) : IsRefl p (CFSG.ClassicalGroups.Orthogonal.reflect Q a) := by
  refine (isRefl_iff hp _).mpr ⟨a, (Q a)⁻¹ • QuadraticMap.polarBilin Q a, ?_, ?_⟩
  · rw [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, smul_eq_mul,
      ← mul_assoc, mul_comm ((Q a)⁻¹) 2, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  · ext x
    rw [Module.reflection_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply ha,
      LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm]

theorem movedSpace_reflect_le_span (Q : QuadraticForm (ZMod p) U) (a : U) :
    HardMathSupport.Kantor79.movedSpace (CFSG.ClassicalGroups.Orthogonal.reflect Q a) ≤
      Submodule.span (ZMod p) {a} := by
  by_cases ha : Q a = 0
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero ha]
    have hzero : HardMathSupport.Kantor79.movedSpace (1 : U ≃ₗ[ZMod p] U) = ⊥ := by
      rw [HardMathSupport.Kantor79.movedSpace]
      have hsub : (((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) = 0 := by
        ext v
        simp
      rw [hsub]
      simp
    rw [hzero]
    exact bot_le
  · rintro w ⟨v, rfl⟩
    change CFSG.ClassicalGroups.Orthogonal.reflect Q a v - v ∈ Submodule.span (ZMod p) {a}
    have hmove : CFSG.ClassicalGroups.Orthogonal.reflect Q a v - v =
        -((QuadraticMap.polar Q a v / Q a) • a) := by
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply ha]
      abel
    rw [hmove]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton a)))

theorem movedSpace_reflect_eq_span (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U} {a : U}
    (ha : Q a ≠ 0) :
    HardMathSupport.Kantor79.movedSpace (CFSG.ClassicalGroups.Orthogonal.reflect Q a) =
      Submodule.span (ZMod p) {a} := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hmem : a ∈ HardMathSupport.Kantor79.movedSpace
      (CFSG.ClassicalGroups.Orthogonal.reflect Q a) :=
    HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 (reflect_apply_self ha)
  exact (movedSpace_reflect_le_span Q a).antisymm
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)

theorem ker_reflect_sub_one_eq_ker_polar {Q : QuadraticForm (ZMod p) U} {a : U}
    (ha : Q a ≠ 0) :
    LinearMap.ker ((CFSG.ClassicalGroups.Orthogonal.reflect Q a : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q a) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have hcoe : ((CFSG.ClassicalGroups.Orthogonal.reflect Q a : U →ₗ[ZMod p] U) - 1) v =
      CFSG.ClassicalGroups.Orthogonal.reflect Q a v - v := by simp
  rw [hcoe, CFSG.ClassicalGroups.Orthogonal.reflect_apply ha,
    QuadraticMap.polarBilin_apply_apply]
  have h1 : v - (QuadraticMap.polar Q a v / Q a) • a - v =
      -((QuadraticMap.polar Q a v / Q a) • a) := by abel
  rw [h1, neg_eq_zero, smul_eq_zero]
  constructor
  · intro h
    have ha0 : a ≠ 0 := fun h0 => ha (by rw [h0, map_zero])
    rcases h with hc | h0
    · exact (div_eq_zero_iff.mp hc).resolve_right ha
    · exact absurd h0 ha0
  · intro h
    exact Or.inl (by rw [h, zero_div])

end CFSG.StandardType.ZS
