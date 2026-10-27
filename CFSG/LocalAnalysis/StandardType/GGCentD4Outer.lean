module

public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.Chevalley.BorelSelfNormalizer
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Lang.D4Three
open scoped Pointwise

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem d4P_conj_rootDiagUnit
    {L : Type} [Field L] (b : Fin Tag.D4.rank → Lˣ) :
    d4P L * rootDiagUnit Tag.D4 b * (d4P L)⁻¹ =
      rootDiagUnit Tag.D4 (fun i => b (d4Rho.symm i)) := by
  have h : d4P L * rootDiagUnit Tag.D4 b =
      rootDiagUnit Tag.D4 (fun i => b (d4Rho.symm i)) * d4P L :=
    diagramMap_mul_rootDiagUnit (K := L) (t := TwistTag.D4) b
  rw [h, mul_inv_cancel_right]

theorem ntpD4_graph_not_inner
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ε : ℕ} (hε : ε = 1 ∨ ε = 2) (h : ↥(adjointGroup Tag.D4 L)) :
    MulAut.conj h ≠ d4Graph L ε := by
  classical
  intro hconj
  have hagree : ∀ g ∈ adjointGroup Tag.D4 L,
      (h : ModGL Tag.D4 L) * g * (h : ModGL Tag.D4 L)⁻¹ = d4P L ^ ε * g * (d4P L ^ ε)⁻¹ := by
    intro g hg
    have h1 := congrArg
      (fun φ : MulAut ↥(adjointGroup Tag.D4 L) =>
        ((φ ⟨g, hg⟩ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)) hconj
    simpa only [MulAut.conj_apply, coe_d4Graph, Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hstr := triangular_borel_structure Tag.D4 L
  have hUA : posUnipotent Tag.D4 L ≤ adjointGroup Tag.D4 L :=
    le_sup_right.trans (hstr.2.2.2.2.2.2.2.2.2.2.2 L).1
  have hTA : torusGroup Tag.D4 L ≤ adjointGroup Tag.D4 L :=
    le_sup_left.trans (hstr.2.2.2.2.2.2.2.2.2.2.2 L).1
  have hPU : (posUnipotent Tag.D4 L).map (MulAut.conj (d4P L ^ ε)).toMonoidHom =
      posUnipotent Tag.D4 L :=
    map_conj_pow_of_map_conj _ (map_conj_diagramMap TwistTag.D4 L (Or.inr (Or.inl rfl))) ε
  have hPT : (torusGroup Tag.D4 L).map (MulAut.conj (d4P L ^ ε)).toMonoidHom =
      torusGroup Tag.D4 L :=
    map_conj_pow_of_map_conj _
      (CFSG.LieType.AlgebraicGroups.map_conj_diagramMap_torusGroup (k := L) TwistTag.D4) ε
  have hhU : (h : ModGL Tag.D4 L) ∈
      Subgroup.normalizer (posUnipotent Tag.D4 L : Set (ModGL Tag.D4 L)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [← hPU]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (hagree u (hUA hu)).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, hagree u (hUA hu)⟩
  have hhB : (h : ModGL Tag.D4 L) ∈ borelGroup Tag.D4 L := by
    rw [← (borel_self_normalizers Tag.D4 L).1]
    exact ⟨h.2, hhU⟩
  have hTU : (h : ModGL Tag.D4 L) ∈
      (SetLike.coe (torusGroup Tag.D4 L) * SetLike.coe (posUnipotent Tag.D4 L) :
        Set (ModGL Tag.D4 L)) := by
    rw [← hstr.2.2.2.2.1]
    exact hhB
  obtain ⟨s, hs, u, hu, hsu⟩ := Set.mem_mul.1 hTU
  have hTfix : ∀ t ∈ torusGroup Tag.D4 L, d4P L ^ ε * t * (d4P L ^ ε)⁻¹ = t := by
    intro t ht
    have hst : s * t = t * s := hstr.1 s hs t ht
    have h1 : (h : ModGL Tag.D4 L) * t * (h : ModGL Tag.D4 L)⁻¹ * t⁻¹ ∈
        posUnipotent Tag.D4 L := by
      rw [← hsu]
      have hst' : s⁻¹ * t⁻¹ = t⁻¹ * s⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hst]
      have e : s * u * t * (s * u)⁻¹ * t⁻¹ = s * (u * (t * u⁻¹ * t⁻¹)) * s⁻¹ := by
        calc s * u * t * (s * u)⁻¹ * t⁻¹ = s * u * t * u⁻¹ * (s⁻¹ * t⁻¹) := by group
          _ = s * u * t * u⁻¹ * (t⁻¹ * s⁻¹) := by rw [hst']
          _ = s * (u * (t * u⁻¹ * t⁻¹)) * s⁻¹ := by group
      rw [e]
      have h2 : t * u⁻¹ * t⁻¹ ∈ posUnipotent Tag.D4 L :=
        (Subgroup.mem_normalizer_iff.1 (hstr.2.2.1 ht) u⁻¹).1 (inv_mem hu)
      exact (Subgroup.mem_normalizer_iff.1 (hstr.2.2.1 hs) _).1 (mul_mem hu h2)
    rw [hagree t (hTA ht)] at h1
    have h3 : d4P L ^ ε * t * (d4P L ^ ε)⁻¹ ∈ torusGroup Tag.D4 L := by
      rw [← hPT]
      exact ⟨t, ht, rfl⟩
    have h4 : d4P L ^ ε * t * (d4P L ^ ε)⁻¹ * t⁻¹ ∈
        torusGroup Tag.D4 L ⊓ posUnipotent Tag.D4 L :=
      Subgroup.mem_inf.2 ⟨mul_mem h3 (inv_mem ht), h1⟩
    rw [hstr.2.2.2.1, Subgroup.mem_bot, mul_inv_eq_one] at h4
    exact h4
  obtain ⟨c₀, hc₀⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset L)
  have hc0 : c₀ ≠ 0 := fun h0 => hc₀ (by simp [h0])
  have hc1 : c₀ ≠ 1 := fun h1 => hc₀ (by simp [h1])
  set c : Lˣ := Units.mk0 c₀ hc0
  let b : Fin Tag.D4.rank → Lˣ := fun j => c ^ Tag.D4.cartan 0 j
  have hfix := hTfix _ (torusElt_mem_torusGroup (τ := Tag.D4) (R := L) 0 c)
  rw [torusElt_eq_rootDiagUnit] at hfix
  have hmove : ∃ i, b (((d4Rho.symm) ^ ε) i) ≠ b i := by
    refine ⟨0, ?_⟩
    have h00 : Tag.D4.cartan 0 0 = 2 := by decide
    have hne : ((d4Rho.symm) ^ ε) 0 = 3 ∨ ((d4Rho.symm) ^ ε) 0 = 1 := by
      rcases hε with rfl | rfl <;> decide
    have h03 : Tag.D4.cartan 0 3 = 0 := by decide
    have h01 : Tag.D4.cartan 0 1 = 0 := by decide
    intro heq
    have hsq : c ^ (2 : ℤ) = 1 := by
      have : b 0 = 1 := by
        rw [← heq]
        rcases hne with h | h
        · simp only [b, h, h03, zpow_zero]
        · simp only [b, h, h01, zpow_zero]
      simpa only [b, h00] using this
    have hsq' : c₀ ^ 2 = 1 := by
      have := congrArg Units.val hsq
      simpa [c] using this
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have hc1' : (c₀ + 1) ^ 2 = 0 := by linear_combination hsq' + c₀ * h2 + h2
    exact hc1 (by linear_combination (pow_eq_zero_iff two_ne_zero).1 hc1' - h2)
  obtain ⟨i, hi⟩ := hmove
  apply hi
  have hconjb : d4P L ^ ε * rootDiagUnit Tag.D4 b * (d4P L ^ ε)⁻¹ =
      rootDiagUnit Tag.D4 (fun j => b (((d4Rho.symm) ^ ε) j)) := by
    rcases hε with rfl | rfl
    · rw [pow_one, d4P_conj_rootDiagUnit]
      rfl
    · have e : d4P L ^ 2 * rootDiagUnit Tag.D4 b * (d4P L ^ 2)⁻¹ =
          d4P L * (d4P L * rootDiagUnit Tag.D4 b * (d4P L)⁻¹) * (d4P L)⁻¹ := by
        rw [pow_two, mul_inv_rev]
        simp only [mul_assoc]
      rw [e, d4P_conj_rootDiagUnit, d4P_conj_rootDiagUnit]
      rfl
  have := rootDiagUnit_injective (hconjb.symm.trans hfix)
  exact congrFun this i

end CFSG.StandardType.NTPlane
