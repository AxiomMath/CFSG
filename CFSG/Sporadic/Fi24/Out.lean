module

public import CFSG.Sporadic.Fi24.Involutions
public import CFSG.Sporadic.Fi24.EdgeCent
public import CFSG.Sporadic.Fi24.ExtOuter

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tJ_mul_tJ : tJ * tJ = 1 := by
  apply jR_injective
  rw [map_mul, jR_tJ, tR_mul_xb_sq, map_one]

theorem tJ_ne_one :
    tJ ≠ 1 := by
  intro h
  have h1 : jR tJ = 1 := by rw [h, map_one]
  rw [jR_tJ] at h1
  apply tR_ne_xb
  calc tR = tR * xb * xb := by rw [mul_assoc, Pair.mul_self pair_R xb_mem_D24, mul_one]
    _ = xb := by rw [h1, one_mul]

section Out

theorem t1J_mul_t1J :
    t1J * t1J = 1 := by
  rw [t1J_eq, show (m1 : J) * tJ * (m1 : J)⁻¹ * ((m1 : J) * tJ * (m1 : J)⁻¹) =
    (m1 : J) * (tJ * tJ) * (m1 : J)⁻¹ by group, tJ_mul_tJ, mul_one, mul_inv_cancel]

theorem t1J_ne_one :
    t1J ≠ 1 := by
  intro h
  apply tJ_ne_one
  calc tJ = (m1 : J)⁻¹ * t1J * (m1 : J) := by rw [t1J_eq]; group
    _ = 1 := by rw [h]; group

theorem tJ_mem_centralizer_t1J :
    tJ ∈ Subgroup.centralizer ({t1J} : Set J) :=
  mem_centralizer_J.2 (mem_centralizer_J.1 t1J_mem_centralizer).symm

theorem isConj_tJ_t1J :
    IsConj tJ t1J := (isConj_iff (α := J)).2 ⟨(m1 : J), t1J_eq.symm⟩

theorem outTwo_centralizer_t1J
    (hH : OutTwo (Subgroup.centralizer ({tJ} : Set J))) :
    OutTwo (Subgroup.centralizer ({t1J} : Set J)) := by
  have h := OutTwo.centralizer_conj (G := J) (m1 : J) tJ hH
  rw [t1J_eq]
  exact h

variable (hPF : PolarFacts)
  (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Fi22.D) (σ : Equiv.Perm Fi22.D),
    (∀ g : Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Fi22.pair_D g = Pair.conjPerm Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Fi22.pair_D (χ : Fi22.J))
  {e : J} (he : EdgeSwap e) {d1 t2 : Fi23.J} (hd1 : d1 ∈ LocalClass Fi23.D23 Fi23.d)
  (hcover : ∀ g : Fi23.J, g ^ 2 = 1 → g ≠ 1 →
    IsConj Fi23.d g ∨ IsConj (Fi23.d * d1) g ∨ IsConj t2 g)
include hPF hfix22 hcent22 he hd1 hcover

theorem pow_mem_innerAut_J
    (α : MulAut J) : ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut J := by
  have hH := outTwo_centralizer_tJ hPF hfix22 he
  have hH1 := outTwo_centralizer_t1J hH
  have hinv : ∀ s : J, s * s = 1 → s ≠ 1 → IsConj s t1J ∨ IsConj s (fi23EquivM.symm t2 : J) := by
    intro s hs hs1
    rcases isConj_tJ_or_r2 hPF hd1 hcover hs hs1 with h | h
    · exact Or.inl (h.trans isConj_tJ_t1J)
    · exact Or.inr h
  have hgen : Subgroup.centralizer ({t1J} : Set J) ⊔ Subgroup.centralizer ({tJ} : Set J) = ⊤ := by
    rw [sup_comm]
    exact sup_centralizer_eq_top he
  have hC := centralizer_inter_isTwoGroup hPF hfix22 hcent22 he
  have h := pow_mem_innerAut_of_two_classes (G := J) (t := t1J) (t₂ := (fi23EquivM.symm t2 : J))
    (t₁ := tJ) t1J_mul_t1J t1J_ne_one hinv hH1 hH tJ_mem_centralizer_t1J hgen hC
  exact h α

end Out

theorem innerAut_le_range_conjJ :
    innerAut J ≤ conjJ.range := by
  rintro _ ⟨g, rfl⟩
  exact ⟨jR g, conjJ_jR g⟩

theorem range_conjJ_eq_top
    (hout : ∀ α : MulAut J, ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut J)
    (hcomp : ∀ φ : MulAut R, ∃ g : R, φ = MulAut.conj g) : conjJ.range = ⊤ :=
  eq_top_of_complete center_J innerAut_le_range_conjJ
    (complete_range_of_injective (G := R) (H := MulAut J) conjJ conjJ_injective hcomp) hout

@[expose] noncomputable def mulAutEquivR
    (hout : ∀ α : MulAut J, ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut J)
    (hcomp : ∀ φ : MulAut R, ∃ g : R, φ = MulAut.conj g) : R ≃* MulAut J :=
  MulEquiv.ofBijective conjJ
    ⟨conjJ_injective, MonoidHom.range_eq_top.1 (range_conjJ_eq_top hout hcomp)⟩

end CFSG.Sporadic.Fi24
