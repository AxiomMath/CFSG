module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  RootSpace

theorem not_dvd_card_weyl_E6 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    ¬ p ∣ Nat.card (WeylGroup Tag.E6) := by
  have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
  rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
  intro hd
  have h51840 : p ∣ 2 ^ 7 * 3 ^ 4 * 5 := by norm_num; exact hd
  rcases (Nat.Prime.dvd_mul hp).1 h51840 with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)

theorem e6T3_classification {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (z : Fin Tag.E6.rank → ZMod p) (hz : z ≠ 0) (c : ZMod p)
    (hw : (dualMatrix (ZMod p) e6T3W).mulVec z = c • z) :
    ∃ u : WeylGroup Tag.E6, ∃ S ∈ e6T3Supports,
      (u • ·) '' rootKernel z = parabolicRoots Tag.E6 ↑S ∧
      ∀ x ∈ Submodule.span ℝ (ofLattice '' parabolicRoots Tag.E6 ↑S),
        weylAct Tag.E6 (u * e6T3W * u⁻¹) x = x → x = 0 := by
  obtain ⟨u₀, J₀, hΦ₀, hJ₀⟩ := exists_smul_rootKernel_eq_parabolicRoots hp5 z
  have hmaps : ∀ α ∈ rootKernel z, e6T3W • α ∈ rootKernel z := fun α hα =>
    ⟨IsRoot.smul hα.1 e6T3W, by
      rw [← charVal_dualMatrix, hw, charVal_smul_col, hα.2, mul_zero]⟩
  set T := u₀ * e6T3W * u₀⁻¹ with hTdef
  have hTmaps : ∀ β ∈ parabolicRoots Tag.E6 J₀, T • β ∈ parabolicRoots Tag.E6 J₀ := by
    intro β hβ
    rw [← hΦ₀] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hmaps α hα, by rw [hTdef, mul_smul, mul_smul, inv_smul_smul]⟩
  have hTlat : ∀ x : Fin Tag.E6.rank → ℤ, T • T • x + T • x + x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ : ∃ y, x = u₀ • y := ⟨u₀⁻¹ • x, (smul_inv_smul u₀ x).symm⟩
    simp only [hTdef, mul_smul, inv_smul_smul]
    rw [← weyl_smul_add, ← weyl_smul_add, e6T3_lattice, weyl_smul_zero]
  classical
  have heven : J₀.toFinset.card % 2 = 0 := by
    have h := even_card_of_sq_add_self_add_one (weylMatrix_sq_add_of_smul hTlat) J₀.toFinset
      fun a ha c hc => by
        rw [Set.mem_toFinset] at ha hc
        rw [weylMatrix_apply]
        exact (hTmaps _ (single_mem_parabolicRoots_E6 hc)).2 a ha
    exact Nat.even_iff.1 h
  have hfin : (rootKernel z).Finite := (finite_setOf_isRoot Tag.E6).subset fun α hα => hα.1
  have h3 : 3 ∣ (rootKernel z).ncard :=
    three_dvd_ncard_of_free hfin e6T3_cube hmaps fun α hα h =>
      (IsRoot.ne_zero hα.1) (e6T3_lattice_fixed h)
  have hcardΦ : (parabolicRoots Tag.E6 J₀).ncard = (rootKernel z).ncard := by
    rw [← hΦ₀]
    exact Set.ncard_image_of_injective _ (MulAction.injective u₀)
  have hJ' : (J₀.toFinset : Set (Fin Tag.E6.rank)) = J₀ := Set.coe_toFinset J₀
  have hS : J₀.toFinset ∈ e6T3Supports := by
    refine e6T3_supports_complete _ (fun h => hJ₀ hz ?_) heven ?_
    · rw [← hJ', h, Finset.coe_univ]
    · rw [← e6T3_parabolic_card, hJ', hcardΦ]
      exact Nat.mod_eq_zero_of_dvd h3
  refine ⟨u₀, J₀.toFinset, hS, by rw [hJ']; exact hΦ₀, fun x _ hx => ?_⟩
  have hx' : weylAct Tag.E6 e6T3W (weylAct Tag.E6 u₀⁻¹ x) = weylAct Tag.E6 u₀⁻¹ x := by
    have := congrArg (weylAct Tag.E6 u₀⁻¹) hx
    rwa [weylAct_mul_apply, weylAct_mul_apply, ← weylAct_mul_apply u₀⁻¹ u₀,
      inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id] at this
  have h0 := e6T3_real_fixed hx'
  have := congrArg (weylAct Tag.E6 u₀) h0
  rwa [← weylAct_mul_apply, mul_inv_cancel, map_one, LinearIsometryEquiv.coe_one, id,
    map_zero] at this

end CFSG.RankThree.PartOne.KE6
