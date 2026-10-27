module

public import CFSG.RankThree.PartOne.SEITZ12.Plane
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable {a₀ : ModGL F4.tag K}

theorem phi4_D_le : phi4D m K a₀ ≤ F4.reeGamma K m :=
  (Subgroup.closure_le _).2 fun _ hk => hk.1

theorem phi4_mem_D {y x : ModGL F4.tag K} (hy : y ∈ F4.reeGamma K m)
    (hx : x ∈ phi4Plane K a₀) (hx1 : x ≠ 1) (hyx : y * x = x * y) : y ∈ phi4D m K a₀ :=
  Subgroup.subset_closure ⟨hy, x, hx, hx1, hyx⟩

theorem phi4_a₀_mem_plane : a₀ ∈ phi4Plane K a₀ :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers a₀)

theorem phi4_b₀_mem_plane : szNw K * a₀ * (szNw K)⁻¹ ∈ phi4Plane K a₀ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem phi4_b₀_ne_one (h : a₀ ≠ 1) : szNw K * a₀ * (szNw K)⁻¹ ≠ 1 := by
  intro h1
  apply h
  have : a₀ = (szNw K)⁻¹ * (szNw K * a₀ * (szNw K)⁻¹) * (szNw K)⁻¹⁻¹ := by group
  rw [this, h1]
  group

theorem phi4_szSubB_le (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    szSubB K m ≤ F4.reeGamma K m := by
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem szNw_mem_reeGamma (rankOneGroupTwo_le_reeGamma hK hx))
    (inv_mem szNw_mem_reeGamma)

theorem phi4_b₀_mem_szSubB (ha₀ : a₀ ∈ rankOneGroupTwo K m) :
    szNw K * a₀ * (szNw K)⁻¹ ∈ szSubB K m :=
  ⟨a₀, ha₀, rfl⟩

theorem phi4_X₂_le_D (hK : Nat.card K = 2 ^ (2 * m + 1)) (ha₀ : a₀ ∈ rankOneGroupTwo K m)
    (ha₀1 : a₀ ≠ 1) : rankOneGroupTwo K m ≤ phi4D m K a₀ := by
  intro r hr
  refine phi4_mem_D (rankOneGroupTwo_le_reeGamma hK hr) phi4_b₀_mem_plane (phi4_b₀_ne_one ha₀1) ?_
  exact commute_rankOneGroupTwo_szSubB r hr _ (phi4_b₀_mem_szSubB ha₀)

theorem phi4_X₁_le_D (hK : Nat.card K = 2 ^ (2 * m + 1)) (ha₀ : a₀ ∈ rankOneGroupTwo K m)
    (ha₀1 : a₀ ≠ 1) : szSubB K m ≤ phi4D m K a₀ := by
  intro y hy
  refine phi4_mem_D (phi4_szSubB_le hK hy) phi4_a₀_mem_plane ha₀1 ?_
  exact (commute_rankOneGroupTwo_szSubB a₀ ha₀ y hy).symm

theorem phi4_finite_D : Finite (phi4D m K a₀) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  infer_instance

end CFSG.RankThree.PartOne.SEITZ12
