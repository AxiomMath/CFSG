module

public import CFSG.Quasithin.Vol2.Ch11SecAKA14
public import CFSG.Quasithin.Vol2.Ch11SecAFactsLine
public import CFSG.Quasithin.Vol2.Ch11SecAKA8

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spLevi_mem_perfectCore)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq exists_move_gammaW_two)

namespace KA

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [CommGroup W] [Finite W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H}
  {f : W → (Fin 2 ⊕ Fin 2 → K)}

omit [Finite K] [CharP K 2] [Finite W] in
theorem gamma2_eq (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) :
    perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)) =
      (perfectCore (Q2 K 1)).map (psiSp π g) :=
  gammaW_pre_eq hf g 1 _ flag_two_eq

omit [CharP K 2] in
theorem pCoreOf_gamma2_eq (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) :
    pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup))) =
      (pCoreOf 2 (perfectCore (Q2 K 1))).map (psiSp π g) := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  rw [gamma2_eq hf g, Ch11.SecS.C11P9A.pCoreOf_map_of_injective _ (psiSp_injective hf g)]

omit [Finite K] [CharP K 2] [Finite W] in
theorem act_levi1 (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (w : W) :
    mat 2 K g⁻¹ *ᵥ f (psiSp π g (spLevi 1 A) w) =
      mat 2 K (spLevi 1 A) *ᵥ (mat 2 K g⁻¹ *ᵥ f w) := by
  rw [psiSp_apply, hf.act4, gconj_mulVec_sp, mat_inv_mulVec]

theorem line_radical (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : StatedSp 2 K) :
    ∀ s ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmapSp g (spPlane K)).toAddSubgroup))),
      ∀ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup, s u = u := by
  intro s hs u hu
  rw [pCoreOf_gamma2_eq hf g] at hs
  obtain ⟨N, hN, rfl⟩ := hs
  rw [psiSp_apply]
  apply fix_of_mulVec_eq hK4 hf hZ
  have hu' : mat 2 K g⁻¹ *ᵥ f u ∈ spPlane K := mem_gmapSp.mp hu
  rw [gconj_mulVec_sp, pCore1_mulVec hK4 hN hu', mat_mulVec_inv]

omit [Finite K] [CharP K 2] [Finite W] in
theorem line_moves (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) :
    ∃ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)),
      ∃ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup, s u ≠ u := by
  obtain ⟨b, hb⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
  have hb1 : f b ∈ gmapSp g (spLine K) := mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hb, one_smul]⟩
  have hbZ : b ∉ Z := fun h => v0_ne_zero g (hb ▸ (hf.ker b).mpr h)
  obtain ⟨s, hs, hsb⟩ := exists_move_gammaW_two hK4 hf g hb1 hbZ
  exact ⟨s, hs, b, gmapSp_mono g spLine_le_spPlane hb1, hsb⟩

omit [Finite K] [CharP K 2] [Finite W] in
theorem line_fixed (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : StatedSp 2 K) :
    ∀ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup,
      (∀ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)),
        s u = u) ↔ u ∈ Z := by
  intro u hu
  refine ⟨fun hfix => ?_, fun hz s hs => hZ s (perfectCore_le _ hs).1 u hz⟩
  have hu' : mat 2 K g⁻¹ *ᵥ f u ∈ spPlane K := mem_gmapSp.mp hu
  have key : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      mat 2 K (spLevi 1 A) *ᵥ (mat 2 K g⁻¹ *ᵥ f u) = mat 2 K g⁻¹ *ᵥ f u := by
    intro A
    have hs : psiSp π g (spLevi 1 A) ∈
        perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)) := by
      rw [gamma2_eq hf g]
      exact ⟨_, spLevi_mem_perfectCore hK4 1 A, rfl⟩
    rw [← act_levi1 hf g A u, hfix _ hs]
  rw [← hf.ker]
  generalize hx : mat 2 K g⁻¹ *ᵥ f u = x at hu' key
  have hx0 : x = 0 → f u = 0 := fun h => by
    rw [← mat_mulVec_inv g (f u), hx, h, Matrix.mulVec_zero]
  apply hx0
  obtain ⟨h2, h3⟩ := hu'
  let A₁ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let A₂ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hxP : x ∈ spPlane K := ⟨h2, h3⟩
  have k1 := key A₁
  have k2 := key A₂
  rw [spLevi1_mulVec_plane A₁ hxP] at k1
  rw [spLevi1_mulVec_plane A₂ hxP] at k2
  have a1 := congrFun k1 (.inl 0)
  have a2 := congrFun k2 (.inl 1)
  simp [vec4, A₁, A₂] at a1 a2
  exact vec4_eq (by simp [a2]) (by simp [a1]) (by simp [h2]) (by simp [h3])

omit [Finite K] [CharP K 2] [Finite W] in
theorem line_comm (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) :
    hf.pre (gmapSp g (spPlane K)).toAddSubgroup =
      Ch11.SecA.commS (perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)))
        (hf.pre (gmapSp g (spPlane K)).toAddSubgroup) ⊔ Z := by
  set U₂ := hf.pre (gmapSp g (spPlane K)).toAddSubgroup with hU₂
  have hmem : ∀ a b : K, ∃ v ∈ U₂, mat 2 K g⁻¹ *ᵥ f v = vec4 a b 0 0 := fun a b => by
    obtain ⟨v, hv⟩ := hf.surj (mat 2 K g *ᵥ vec4 a b 0 0)
    refine ⟨v, ?_, by rw [hv, mat_inv_mulVec]⟩
    show f v ∈ gmapSp g (spPlane K)
    rw [hv, mem_gmapSp, mat_inv_mulVec]
    exact ⟨rfl, rfl⟩
  have hgen : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U₂,
      psiSp π g (spLevi 1 A) v * v⁻¹ ∈ Ch11.SecA.commS (perfectCore (H ⊓ Ch11.SecA.stabW U₂))
        U₂ := by
    intro A v hv
    have hs : psiSp π g (spLevi 1 A) ∈ perfectCore (H ⊓ Ch11.SecA.stabW U₂) := by
      rw [gamma2_eq hf g]
      exact ⟨_, spLevi_mem_perfectCore hK4 1 A, rfl⟩
    exact Subgroup.subset_closure ⟨_, hs, v, hv, rfl⟩
  apply le_antisymm
  · intro u hu
    have hu' : mat 2 K g⁻¹ *ᵥ f u ∈ spPlane K := mem_gmapSp.mp hu
    let A₁ : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
    let A₂ : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
    obtain ⟨v₁, hv₁U, hv₁⟩ := hmem 0 ((mat 2 K g⁻¹ *ᵥ f u) (.inl 0))
    obtain ⟨v₀, hv₀U, hv₀⟩ := hmem ((mat 2 K g⁻¹ *ᵥ f u) (.inl 1)) 0
    have hfu : f u = f ((psiSp π g (spLevi 1 A₁) v₁ * v₁⁻¹) *
        (psiSp π g (spLevi 1 A₂) v₀ * v₀⁻¹)) := by
      have h1 : mat 2 K g⁻¹ *ᵥ f u = mat 2 K g⁻¹ *ᵥ f ((psiSp π g (spLevi 1 A₁) v₁ * v₁⁻¹) *
          (psiSp π g (spLevi 1 A₂) v₀ * v₀⁻¹)) := by
        rw [hf.map_mul, hf.map_mul_inv, hf.map_mul_inv, Matrix.mulVec_add, Matrix.mulVec_sub,
          Matrix.mulVec_sub, act_levi1 hf g A₁ v₁, act_levi1 hf g A₂ v₀, hv₁, hv₀,
          spLevi1_mulVec_plane A₁ ⟨rfl, rfl⟩, spLevi1_mulVec_plane A₂ ⟨rfl, rfl⟩]
        refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4, A₁, A₂, hu'.1, hu'.2]
      have h2 := congrArg (fun y => mat 2 K g *ᵥ y) h1
      simpa only [mat_mulVec_inv] using h2
    obtain ⟨z, hz, hdz⟩ : ∃ z ∈ Z, u = (psiSp π g (spLevi 1 A₁) v₁ * v₁⁻¹) *
        (psiSp π g (spLevi 1 A₂) v₀ * v₀⁻¹) * z :=
      ⟨_, (hf.eq_iff _ _).mp hfu, by rw [mul_comm u, mul_inv_cancel_left]⟩
    rw [hdz]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hgen A₁ v₁ hv₁U))
      (Subgroup.mem_sup_left (hgen A₂ v₀ hv₀U))) (Subgroup.mem_sup_right hz)
  · refine sup_le ((Subgroup.closure_le _).mpr ?_) (hf.le_pre _)
    rintro _ ⟨s, hs, u, hu, rfl⟩
    exact Subgroup.mul_mem _ ((Ch11.SecA.mem_stabW.mp (perfectCore_le _ hs).2 u).mp hu)
      (Subgroup.inv_mem _ hu)

end KA

end CFSG.Quasithin.Vol2.KGNat
