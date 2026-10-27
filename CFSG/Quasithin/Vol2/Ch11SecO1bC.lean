module

public import CFSG.Quasithin.Vol2.Ch11SecO1bB
public import CFSG.Quasithin.Vol2.Ch11SecGFacts
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA
open CFSG.Open (pCoreOf)
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isEndStable_comm_of_linear {D : FFModel} {K M : Type} [Field K] [AddCommGroup M]
    [Module K M] {LM : LinModel D K M} [IsMulCommutative ↥(fsuV T I)]
    (hS : SecD.NatSetting11 G T L I n) {π : D.Gam →* ↥(autOn L (fsuV T I))}
    {f : ↥(fsuV T I) → M} (hf : IsCoord LM (autOn L (fsuV T I)) ⊥ π f)
    (hcomm : ∀ T' : M →+ M, (∀ (γ : D.Gam) (x : M), T' (LM.lin γ x) = LM.lin γ (T' x)) →
      ∃ c : K, ∀ x, T' x = c • x)
    {X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hlin : ∀ x (hx : x ∈ X), ∃ A : M →ₗ[K] M,
      ∀ w, f (SecA.conjV (fsuV T I) x (hXV hx) w) = A (f w)) :
    IsEndStable L (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) ⁅fsuV T I, X⁆ := by
  rw [SecA.isEndStable_iff hS.le_normalizer, SecA.inf_centralizer_subgroupOf,
    SecO1.subgroupOf_centralizer_eq_bot hS, ← Ch10.SecA.commV_autOn_eq hXV,
    hf.endStableW_iff (SecO1.sq_eq_one hS) hcomm bot_le]
  have key : ∀ u ∈ commV (autOn X (fsuV T I)), ∀ c : K,
      ∃ u' ∈ commV (autOn X (fsuV T I)), f u' = c • f u := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨h, hh, w, rfl⟩ := hu
      obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hh
      obtain ⟨A, hA⟩ := hlin x hx
      intro c
      obtain ⟨w', hw'⟩ := hf.surj (c • f w)
      refine ⟨SecA.conjV (fsuV T I) x hxV w' * w'⁻¹, Subgroup.subset_closure ⟨_, hh, w', rfl⟩,
        ?_⟩
      rw [hf.map_mul_inv, hA, hw', hf.map_mul_inv, hA, map_smul, smul_sub]
    | one =>
      intro c
      exact ⟨1, Subgroup.one_mem _, by rw [hf.map_one, smul_zero]⟩
    | mul u v _ _ hu hv =>
      intro c
      obtain ⟨u', hu', e1⟩ := hu c
      obtain ⟨v', hv', e2⟩ := hv c
      exact ⟨u' * v', Subgroup.mul_mem _ hu' hv', by rw [hf.map_mul, hf.map_mul, e1, e2, smul_add]⟩
    | inv u _ hu =>
      intro c
      obtain ⟨u', hu', e⟩ := hu c
      exact ⟨u'⁻¹, Subgroup.inv_mem _ hu', by rw [hf.map_inv, hf.map_inv, e, smul_neg]⟩
  intro c x hx
  obtain ⟨u, hu, rfl⟩ := hf.mem_img.mp hx
  obtain ⟨u', hu', e⟩ := key u hu c
  exact hf.mem_img.mpr ⟨u', hu', e⟩

end CFSG.Quasithin.Vol2.Ch11.SecO1b

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecO1b
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

theorem commEndStableFact_holds : CommEndStableFact := by
  intro G _ _ T L I n V₁ hS hk hV₁ X hX
  have := SecO1.isMulCommutative hS
  have hXV : X ≤ Subgroup.normalizer (fsuV T I : Set G) := fun x hx =>
    r1_le_normalizer hS hV₁ (hX hx)
  rcases hk with hk | hk
  · obtain ⟨K, _, _, _, hK, π, f, hf, g, hg⟩ := exists_coord_sl3_syl hS hk
    refine isEndStable_comm_of_linear hS hf (fun T' hT' => commutant_statedSL (by norm_num) T' hT')
      hXV fun x hx => ?_
    obtain ⟨a, b, hab⟩ := r1_shape_sl3 hS hK hf hg hV₁ (hX hx)
    refine ⟨Matrix.mulVecLin ((g : Matrix (Fin 3) (Fin 3) K) *
      (CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat a b 0 *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))), fun w => ?_⟩
    rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hab w,
      Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  · obtain ⟨K, _, _, _, hK, π, f, hπ, hf, g, hg⟩ := exists_coord_sp4_syl hS hk
    refine isEndStable_comm_of_linear hS hf (fun T' hT' => commutant_statedSp T' hT') hXV
      fun x hx => ?_
    obtain ⟨N, -, hN⟩ := r1_shape_sp4 hS hK hπ hf hg hV₁ (hX hx)
    exact ⟨Matrix.mulVecLin (mat 2 K (g * N * g⁻¹)), fun w => by
      rw [Matrix.mulVecLin_apply, hN w]⟩

end CFSG.Quasithin.Vol2.Ch11.SecG
