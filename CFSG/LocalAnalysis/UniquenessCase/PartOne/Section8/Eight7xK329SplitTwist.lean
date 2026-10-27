module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem k329_S5_of_no_order_three {H : Type} [Group H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (hno : ∀ ω ∈ Z, ω ^ 3 = 1 → ω = 1) {x : H} (hx : x ^ 3 ∈ Z) :
    K329Ct Z x ≤ Subgroup.centralizer ({x} : Set H) := by
  intro g hg
  have hg' : (QuotientGroup.mk x : H ⧸ Z) * QuotientGroup.mk g =
      QuotientGroup.mk g * QuotientGroup.mk x := by
    have := hg
    simpa [K329Ct, Subgroup.mem_centralizer_iff] using this
  have hω : (g * x)⁻¹ * (x * g) ∈ Z := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hg'.symm
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = (g * x)⁻¹ * (x * g) := ⟨_, rfl⟩
  rw [← hωdef] at hω
  have hxg : x * g = g * x * ω := by rw [hωdef]; group
  have hωc : ∀ y : H, ω * y = y * ω := fun y => (Subgroup.mem_center_iff.mp (hZ hω) y).symm
  have hx3c : ∀ y : H, x ^ 3 * y = y * x ^ 3 := fun y =>
    (Subgroup.mem_center_iff.mp (hZ hx) y).symm
  have h1 : g⁻¹ * x * g = x * ω := by
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * x * ω) := by rw [hxg]
      _ = x * ω := by group
  have h2 : (g⁻¹ * x * g) ^ 3 = x ^ 3 := by
    have e : (g⁻¹ * x * g) ^ 3 = g⁻¹ * x ^ 3 * g := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, ← hx3c g⁻¹]
    group
  have h3 : (x * ω) ^ 3 = x ^ 3 * ω ^ 3 := Commute.mul_pow (hωc x).symm 3
  have hω3 : ω ^ 3 = 1 := by
    have e : x ^ 3 * ω ^ 3 = x ^ 3 := by rw [← h3, ← h1, h2]
    simpa using e
  have hω1 : ω = 1 := hno ω hω hω3
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [hxg, hω1, mul_one]

theorem k329_scalar_injective {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro a b h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h' := congrArg (fun A : GL ι K => (A : Matrix ι ι K) i i) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.ext_iff] using h'

theorem k329_unit_eq_one_of_sq_cube {K : Type} [Field K] (c : Kˣ) (h2 : c ^ 2 = 1)
    (h3 : c ^ 3 = 1) : c = 1 := by
  calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
