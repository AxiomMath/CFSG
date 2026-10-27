module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37Cnt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem conjSubgroup_le_M_of_E {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) {m : ℕ} (hSK : Nat.card S.K = 2 ^ m) (hm2 : 2 ≤ m) {n : ℕ}
    (hn : n < 2 * m) {g : G} (hU : E3.mQuot V (conjSubgroup D.M g⁻¹) ≤ n) {E : Subgroup G}
    (hEV : E ≤ V) (hEM : E ≤ conjSubgroup D.M g)
    (hEB : E ≤ centralizer ((conjSubgroup V g ⊓ D.M : Subgroup G) : Set G))
    (hEcard : Nat.card ↥E = Nat.card ↥V₀ * Nat.card S.K)
    (hEc : ∀ x ∈ E, x ≠ 1 → centralizer ({x} : Set G) ≤ D.M) :
    conjSubgroup V g ≤ D.M := by
  classical
  let U : Subgroup G := V ⊓ conjSubgroup D.M g⁻¹
  have hXM : conjSubgroup E g⁻¹ ≤ D.M := by
    have h := E3.conjSubgroup_mono_left g⁻¹ hEM
    rwa [E3.conjSubgroup_conj_inv] at h
  have hX : IsElemAbelian 2 (conjSubgroup E g⁻¹) :=
    E3.isElemAbelian_conjSubgroup (B2F.isElemAbelian_mono hEV hV) g⁻¹
  have hXcard : 2 * Nat.card ↥V₀ < Nat.card ↥(conjSubgroup E g⁻¹) := by
    rw [E3.card_conjSubgroup E g⁻¹, hEcard, hSK]
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hpos : 0 < Nat.card ↥V₀ := Nat.card_pos
    calc 2 * Nat.card ↥V₀ < 4 * Nat.card ↥V₀ := by omega
      _ = Nat.card ↥V₀ * 4 := by rw [Nat.mul_comm]
      _ ≤ Nat.card ↥V₀ * 2 ^ m := Nat.mul_le_mul_left _ h4
  have hU_eq : conjSubgroup U g = conjSubgroup V g ⊓ D.M := by
    dsimp only [U]
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_inv_conj]
  have hXcenU : conjSubgroup E g⁻¹ ≤ centralizer (U : Set G) := by
    have hEcU : E ≤ centralizer (conjSubgroup U g : Set G) := by
      rw [hU_eq]
      exact hEB
    have h := E3.conjSubgroup_mono_left g⁻¹ hEcU
    rwa [E3.conjSubgroup_centralizer, E3.conjSubgroup_conj_inv] at h
  have hXn : ∀ x ∈ conjSubgroup E g⁻¹,
      E3.mQuot V (V ⊓ centralizer ({x} : Set G)) ≤ n := by
    intro x hx
    have hxcen : x ∈ centralizer (U : Set G) := hXcenU hx
    have hUle : U ≤ V ⊓ centralizer ({x} : Set G) := by
      intro u hu
      dsimp only [U] at hu
      exact ⟨(Subgroup.mem_inf.1 hu).1,
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxcen u hu)⟩
    have hUeq : E3.mQuot V U = E3.mQuot V (conjSubgroup D.M g⁻¹) := by
      unfold E3.mQuot
      dsimp only [U]
      rw [inf_comm, Subgroup.inf_relIndex_right]
    calc E3.mQuot V (V ⊓ centralizer ({x} : Set G)) ≤ E3.mQuot V U := E3.mQuot_mono hUle
      _ = E3.mQuot V (conjSubgroup D.M g⁻¹) := hUeq
      _ ≤ n := hU
  have hN : ∀ x' ∈ conjSubgroup E g⁻¹, x' ≠ 1 →
      centralizer ({x'} : Set G) ≤ conjSubgroup D.M g⁻¹ := by
    intro x' hx' hx'1 z hz
    have hxE : g⁻¹ * x' * g ∈ E := E3.mem_conjSubgroup_inv_iff.1 hx'
    have hx1 : g⁻¹ * x' * g ≠ 1 := by
      intro h
      apply hx'1
      calc x' = g * (g⁻¹ * x' * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h]
        _ = 1 := by group
    have hzcomm : z * x' = x' * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    have hmem : g⁻¹ * z * g ∈ centralizer ({g⁻¹ * x' * g} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g⁻¹ * z * g) * (g⁻¹ * x' * g)
          = g⁻¹ * (z * x') * g := by group
        _ = g⁻¹ * (x' * z) * g := by rw [hzcomm]
        _ = (g⁻¹ * x' * g) * (g⁻¹ * z * g) := by group
    exact E3.mem_conjSubgroup_inv_iff.2 (hEc (g⁻¹ * x' * g) hxE hx1 hmem)
  have hVle : V ≤ conjSubgroup D.M g⁻¹ :=
    le_of_forall_centralizer_le (X := conjSubgroup E g⁻¹) (N := conjSubgroup D.M g⁻¹)
      hS S hSω hSK hn hXM hX hXcard hXn hN
  rw [← E3.conjSubgroup_inv_conj D.M g]
  exact (E3.conjSubgroup_le_conjSubgroup_iff (A := V)
    (B := conjSubgroup D.M g⁻¹) g).2 hVle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
