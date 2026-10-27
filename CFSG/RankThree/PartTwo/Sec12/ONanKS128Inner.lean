module

public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Frame

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128Move

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem semiAct_one_pow {ζ : MulAut (slPi π 3 (p ^ f) K)} {y : GL (Fin 3) K}
    (h : SemiAct ζ 1 y) (k : ℕ) (s : slPi π 3 (p ^ f) K) :
    (((ζ ^ k) s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = y ^ k * s * (y ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, semiAct_one_iff.1 h, ih, pow_succ']
    group

theorem scalar_conj (μ : Kˣ) (w : GL (Fin 3) K) :
    GeneralLinearGroup.scalar (Fin 3) μ * w * (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ = w := by
  rw [← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ w).eq]
  group

theorem inv_conj_scalar (μ : Kˣ) (g : GL (Fin 3) K) :
    g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * g = GeneralLinearGroup.scalar (Fin 3) μ := by
  have h := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ g).eq
  calc g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * g
      = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * g) := by group
    _ = g⁻¹ * (g * GeneralLinearGroup.scalar (Fin 3) μ) := by rw [← h]
    _ = GeneralLinearGroup.scalar (Fin 3) μ := by group

theorem mem_zpowers_conj_of_eq_pow_mul_scalar {ζ : MulAut (slPi π 3 (p ^ f) K)}
    {y : GL (Fin 3) K} (h : SemiAct ζ 1 y) {x : slPi π 3 (p ^ f) K} {e : ℕ} {μ : Kˣ}
    (hy : y = (x : GL (Fin 3) K) ^ e * GeneralLinearGroup.scalar (Fin 3) μ) :
    ζ ∈ Subgroup.zpowers (MulAut.conj x) := by
  have hζe : ζ = MulAut.conj (x ^ e) := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [semiAct_one_iff.1 h s, hy]
    change _ = ((x ^ e * s * (x ^ e)⁻¹ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, _root_.mul_inv_rev]
    calc (x : GL (Fin 3) K) ^ e * GeneralLinearGroup.scalar (Fin 3) μ * s *
          ((GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * ((x : GL (Fin 3) K) ^ e)⁻¹)
        = (x : GL (Fin 3) K) ^ e * (GeneralLinearGroup.scalar (Fin 3) μ * s *
          (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹) * ((x : GL (Fin 3) K) ^ e)⁻¹ := by group
      _ = _ := by rw [scalar_conj]
  rw [hζe, map_pow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) e

theorem conj_pow_mul_scalar (g D : GL (Fin 3) K) (e : ℕ) (ν : Kˣ) :
    g * (D ^ e * GeneralLinearGroup.scalar (Fin 3) ν) * g⁻¹ =
      (g * D * g⁻¹) ^ e * GeneralLinearGroup.scalar (Fin 3) ν := by
  have h := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ν g⁻¹).eq
  rw [conj_pow]
  calc g * (D ^ e * GeneralLinearGroup.scalar (Fin 3) ν) * g⁻¹
      = g * D ^ e * (GeneralLinearGroup.scalar (Fin 3) ν * g⁻¹) := by group
    _ = g * D ^ e * (g⁻¹ * GeneralLinearGroup.scalar (Fin 3) ν) := by rw [← h]
    _ = _ := by group

theorem exists_u_of_inner (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : slPi π 3 (p ^ f) K} (hxZ : x ∉ Subgroup.center (slPi π 3 (p ^ f) K)) (hx3 : x ^ 3 = 1)
    {ζ : MulAut (slPi π 3 (p ^ f) K)} (hζ3 : ζ ^ 3 = 1) (hζx : ζ x = x)
    (hζA : ζ ∉ Subgroup.zpowers (MulAut.conj x)) {y : GL (Fin 3) K} (hζy : SemiAct ζ 1 y) :
    ∃ u : slPi π 3 (p ^ f) K, u * x * u⁻¹ * x⁻¹ ∈ Subgroup.center (slPi π 3 (p ^ f) K) ∧
      u * x * u⁻¹ ≠ x ∧
      ζ u * u⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.center (slPi π 3 (p ^ f) K) ∧
      ζ u * u⁻¹ ∉ Subgroup.center (slPi π 3 (p ^ f) K) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hxs : (x : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
    intro hs
    exact hxZ (Subgroup.mem_center_iff.mpr fun s =>
      Subtype.ext (commute_of_mem_statedScalars hs (s : GL (Fin 3) K)))
  have hx3' : (x : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hx3]
    rfl
  obtain ⟨g, hg, a, ω, hω1, hω3, ha3, hframe⟩ := exists_frame hK hq x.2 hx3' hxs
  have hx : (x : GL (Fin 3) K) = g * diagUnits a (a * ω) (a * ω ^ 2) * g⁻¹ := by
    rw [← hframe]
    group
  have hfD : frobGL (1 : K ≃+* K) (diagUnits a (a * ω) (a * ω ^ 2)) =
      diagUnits a (a * ω) (a * ω ^ 2) := frobGL_one_apply _
  have hcD := commute_of_fixed hζy hζx hframe hfD
  obtain ⟨hne1, hne2, hne3⟩ := frame_entries_ne (a := a) hω1 hω3
  obtain ⟨c₀, c₁, c₂, hc⟩ := exists_diagUnits_of_commute hne1 hne2 hne3 hcD
  have hc' : g⁻¹ * y * g = diagUnits c₀ c₁ c₂ := by rw [← hc, frobGL_one_apply]
  have hy3 : y ^ 3 ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs => ?_
    have h := semiAct_one_pow hζy 3 ⟨s, hs⟩
    rw [hζ3, MulAut.one_apply] at h
    change s = y ^ 3 * s * (y ^ 3)⁻¹ at h
    calc y ^ 3 * s = (y ^ 3 * s * (y ^ 3)⁻¹) * y ^ 3 := by group
      _ = s * y ^ 3 := by rw [← h]
  obtain ⟨lam, hlam⟩ := hy3
  have hc3 : (diagUnits c₀ c₁ c₂ : GL (Fin 3) K) ^ 3 = diagUnits lam lam lam := by
    rw [← hc', ← scalar_eq_diagUnits, hlam]
    have := conj_pow (a := g⁻¹) (b := y) (i := 3)
    rw [inv_inv] at this
    rw [this, ← hlam]
    exact inv_conj_scalar lam g
  rw [diagUnits_pow, diagUnits_eq_iff] at hc3
  obtain ⟨hc30, hc31, hc32⟩ := hc3
  have ht0 : (c₀ * c₂⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hc30, hc32, mul_inv_cancel]
  have ht1 : (c₁ * c₀⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hc31, hc30, mul_inv_cancel]
  have hprod : c₀ * c₂⁻¹ * (c₁ * c₀⁻¹) * (c₂ * c₁⁻¹) = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    have h0 := c₀.ne_zero
    have h1 := c₁.ne_zero
    have h2 := c₂.ne_zero
    field_simp
  obtain ⟨u, hu, hcomm, hne⟩ := exists_u_of_frame hK hq hg hω1 hω3 hx (one_mem _) (one_mem _)
    (by simp : (1 : Kˣ) * 1 * 1 = 1)
  have hcoc := cocycle_in_frame hζy hu hc
  simp only [map_one, mul_one, inv_one] at hcoc
  obtain ⟨e, ν, hν3, hdν⟩ := exists_pow_mul_scalar hω1 hω3 ha3 ht0 ht1 hprod
  have hSν : (GeneralLinearGroup.scalar (Fin 3) ν : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K :=
    scalar_mem_slPi_of_pow_three hK hq hν3
  have hz : (⟨_, hSν⟩ : slPi π 3 (p ^ f) K) ∈ Subgroup.center (slPi π 3 (p ^ f) K) :=
    Subgroup.mem_center_iff.mpr fun s =>
      Subtype.ext (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ν (s : GL (Fin 3) K)).eq
  have hd : ζ u * u⁻¹ = x ^ e * ⟨_, hSν⟩ := by
    apply Subtype.ext
    rw [hcoc, hdν, Subgroup.coe_mul, Subgroup.coe_pow, hx]
    exact conj_pow_mul_scalar g _ e ν
  refine ⟨u, hcomm, hne, ?_, ?_⟩
  · rw [hd]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) e) hz
  · intro hcen
    have hsc : ((ζ u * u⁻¹ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
      refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs => ?_
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨s, hs⟩)).symm
    obtain ⟨lam', hlam'⟩ := hsc
    have h2 : g * diagUnits (c₀ * c₂⁻¹) (c₁ * c₀⁻¹) (c₂ * c₁⁻¹) * g⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) lam' := hcoc.symm.trans hlam'.symm
    have h1 : (diagUnits (c₀ * c₂⁻¹) (c₁ * c₀⁻¹) (c₂ * c₁⁻¹) : GL (Fin 3) K) =
        diagUnits lam' lam' lam' := by
      rw [← scalar_eq_diagUnits]
      calc (diagUnits (c₀ * c₂⁻¹) (c₁ * c₀⁻¹) (c₂ * c₁⁻¹) : GL (Fin 3) K)
          = g⁻¹ * (g * diagUnits (c₀ * c₂⁻¹) (c₁ * c₀⁻¹) (c₂ * c₁⁻¹) * g⁻¹) * g := by group
        _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) lam' * g := by rw [h2]
        _ = _ := inv_conj_scalar lam' g
    obtain ⟨-, e1, e2⟩ := diagUnits_eq_iff.1 h1
    have hl3 : lam' ^ 3 = 1 := by rw [← e1]; exact ht1
    have hc1 : c₁ = lam' * c₀ := by rw [← e1]; group
    have hc2 : c₂ = lam' ^ 2 * c₀ := by
      calc c₂ = (c₂ * c₁⁻¹) * c₁ := by group
        _ = lam' * (lam' * c₀) := by rw [e2, hc1]
        _ = lam' ^ 2 * c₀ := by rw [sq, mul_assoc]
    obtain ⟨e', he'⟩ : ∃ e' : ℕ, lam' = ω ^ e' := by
      rcases eq_one_or_eq_or_eq_sq hω1 hω3 hl3 with h | h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
      · exact ⟨2, h⟩
    have hcD' : (diagUnits c₀ c₁ c₂ : GL (Fin 3) K) =
        diagUnits a (a * ω) (a * ω ^ 2) ^ e' *
          GeneralLinearGroup.scalar (Fin 3) (c₀ * (a ^ e')⁻¹) := by
      rw [← diagUnits_geometric a ω c₀ e', hc1, hc2, he', ← pow_mul, mul_comm e' 2, mul_comm]
    have hy : y = (x : GL (Fin 3) K) ^ e' *
        GeneralLinearGroup.scalar (Fin 3) (c₀ * (a ^ e')⁻¹) := by
      rw [hx, ← conj_pow_mul_scalar, ← hcD', ← hc']
      group
    exact hζA (mem_zpowers_conj_of_eq_pow_mul_scalar hζy hy)

end CFSG.RankThree.PartTwo.Sec12.KS128Move
