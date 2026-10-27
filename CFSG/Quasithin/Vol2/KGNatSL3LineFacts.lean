module

public import CFSG.Quasithin.Vol2.KGNatSL3Line
public import CFSG.Quasithin.Vol2.Ch11SecAFactsLine

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem vec3_decomp {K : Type} [Field K] (x : Fin 3 → K) (h2 : x 2 = 0) :
    x = x 0 • ![1, 0, 0] + x 1 • ![0, 1, 0] :=
  vec3_eq (by simp) (by simp) (by simp [h2])

theorem map_one_of_mul {W : Type*} [CommGroup W] {U : Subgroup W} {θ : W → W}
    (hθ : ∀ u ∈ U, ∀ v ∈ U, θ (u * v) = θ u * θ v) : θ 1 = 1 := by
  have h := hθ 1 U.one_mem 1 U.one_mem
  rw [mul_one] at h
  exact mul_eq_left.mp h.symm

theorem map_inv_of_mul {W : Type*} [CommGroup W] {U : Subgroup W} {θ : W → W}
    (hθ : ∀ u ∈ U, ∀ v ∈ U, θ (u * v) = θ u * θ v) {u : W} (hu : u ∈ U) : θ u⁻¹ = (θ u)⁻¹ := by
  have h2 := hθ u hu u⁻¹ (U.inv_mem hu)
  rw [mul_inv_cancel, map_one_of_mul hθ] at h2
  exact eq_inv_of_mul_eq_one_right h2.symm

theorem factLineSL3_holds : Ch11.SecA.FactLineSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₂ hU₂
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  have hU' : Ch11.SecA.IsFlagW H P Z (Nat.card K) 2 U₂ := by rw [hK]; exact hU₂
  have hUeq := eq_U2_of_isFlagW hW hf hg hU'
  subst hUeq
  refine ⟨?_, ?_, fun u hu => fixed_plane_iff hSL hf hZ g hu, ?_, ?_⟩
  · intro s hs u hu
    obtain ⟨N, -, hN0, hN1, rfl⟩ := levi_of_mem_pCoreOf_HU2 hSL hf g hs
    have hx := vec3_decomp _ ((mem_pre_plane_iff hf g u).mp hu)
    obtain ⟨u₀, hu₀⟩ := hf.surj ((((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f u) 0 • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]))
    obtain ⟨u₁, hu₁⟩ := hf.surj ((((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f u) 1 • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0]))
    have hfu : f u = f (u₀ * u₁) := by
      rw [hf.map_mul, hu₀, hu₁, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add,
        ← hx, g_ginv_mulVec]
    obtain ⟨z, hz, hdz⟩ : ∃ z ∈ Z, u = u₀ * u₁ * z :=
      ⟨_, (hf.eq_iff _ _).mp hfu, by rw [mul_comm u, mul_inv_cancel_left]⟩
    have hs0 : ((rho3 π (g * N * g⁻¹) : ↥H) : MulAut W) u₀ = u₀ :=
      fix_HU1 hSL hf hZ g _ ((mem_perfectCore_HU1_iff hSL hf g _).mpr ⟨N, hN0, rfl⟩) u₀
        ((mem_pre_line_iff hf g u₀).mpr ⟨_, hu₀⟩)
    have hs1 : ((rho3 π (g * N * g⁻¹) : ↥H) : MulAut W) u₁ = u₁ := by
      refine fix_HU1 hSL hf hZ (g * p01 K) _ ((mem_perfectCore_HU1_iff hSL hf (g * p01 K) _).mpr
        ⟨(p01 K)⁻¹ * N * p01 K, ?_, ?_⟩) u₁ ((mem_pre_line_iff hf _ u₁).mpr
          ⟨(((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u) 1, ?_⟩)
      · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p01_mulVec,
          show (![(![1, 0, 0] : Fin 3 → K) 1, (![1, 0, 0] : Fin 3 → K) 0,
            (![1, 0, 0] : Fin 3 → K) 2] : Fin 3 → K) = ![0, 1, 0] from vec3_eq rfl rfl rfl,
          hN1, p01_inv, p01_mulVec]
        exact vec3_eq rfl rfl rfl
      · rw [show g * p01 K * ((p01 K)⁻¹ * N * p01 K) * (g * p01 K)⁻¹ = g * N * g⁻¹ by group]
      · rw [hu₁, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, p01_mulVec]
        congr 2
    rw [hdz, map_mul, map_mul, hs0, hs1, hZ _ (rho3 π _).2 z hz]
  · obtain ⟨u, hu⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0])
    refine ⟨_, (mem_perfectCore_HU2_iff hSL hf g _).mpr ⟨blockSL (sl2Up K), blockSL_mem _, rfl⟩,
      u, (mem_pre_plane_iff hf g u).mpr (by rw [hu, ginv_g_mulVec]; rfl), fun h => ?_⟩
    have h1 := congrArg f h
    rw [hf.act3, gconj_mulVec, hu, ginv_g_mulVec, blockSL_up_mulVec] at h1
    have h2 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
    simp only [ginv_g_mulVec] at h2
    have h3 := congrFun h2 0
    simp at h3
  · apply le_antisymm
    · intro u hu
      have hx := vec3_decomp _ ((mem_pre_plane_iff hf g u).mp hu)
      obtain ⟨x0, hx0⟩ : ∃ c : K, (((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ f u) 0 = c := ⟨_, rfl⟩
      obtain ⟨x1, hx1⟩ : ∃ c : K, (((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ f u) 1 = c := ⟨_, rfl⟩
      rw [hx0, hx1] at hx
      obtain ⟨v₁, hv₁⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, x0, 0])
      obtain ⟨v₀, hv₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![x1, 0, 0])
      have hv₁U := (mem_pre_plane_iff hf g v₁).mpr (by rw [hv₁, ginv_g_mulVec]; rfl)
      have hv₀U := (mem_pre_plane_iff hf g v₀).mpr (by rw [hv₀, ginv_g_mulVec]; rfl)
      have hs₁ := (mem_perfectCore_HU2_iff hSL hf g
        ((rho3 π (g * blockSL (sl2Up K) * g⁻¹) : ↥H) : MulAut W)).mpr
          ⟨blockSL (sl2Up K), blockSL_mem _, rfl⟩
      have hs₂ := (mem_perfectCore_HU2_iff hSL hf g
        ((rho3 π (g * blockSL (sl2Low K) * g⁻¹) : ↥H) : MulAut W)).mpr
          ⟨blockSL (sl2Low K), blockSL_mem _, rfl⟩
      have hc₁ : ((rho3 π (g * blockSL (sl2Up K) * g⁻¹) : ↥H) : MulAut W) v₁ * v₁⁻¹ ∈
          Ch11.SecA.commS (perfectCore (H ⊓ Ch11.SecA.stabW
            (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)))
            (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) :=
        Subgroup.subset_closure ⟨_, hs₁, v₁, hv₁U, rfl⟩
      have hc₂ : ((rho3 π (g * blockSL (sl2Low K) * g⁻¹) : ↥H) : MulAut W) v₀ * v₀⁻¹ ∈
          Ch11.SecA.commS (perfectCore (H ⊓ Ch11.SecA.stabW
            (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)))
            (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) :=
        Subgroup.subset_closure ⟨_, hs₂, v₀, hv₀U, rfl⟩
      have hfu : f u = f ((((rho3 π (g * blockSL (sl2Up K) * g⁻¹) : ↥H) : MulAut W) v₁ *
          v₁⁻¹) * (((rho3 π (g * blockSL (sl2Low K) * g⁻¹) : ↥H) : MulAut W) v₀ * v₀⁻¹)) := by
        rw [hf.map_mul, hf.map_mul_inv, hf.map_mul_inv, hf.act3, hf.act3, gconj_mulVec,
          gconj_mulVec, hv₁, hv₀, ginv_g_mulVec, ginv_g_mulVec, blockSL_up_mulVec,
          blockSL_low_mulVec, ← Matrix.mulVec_sub, ← Matrix.mulVec_sub, ← Matrix.mulVec_add,
          ← g_ginv_mulVec g (f u), hx]
        congr 1
        exact vec3_eq (by simp) (by simp) (by simp)
      obtain ⟨c₁, hc₁def⟩ : ∃ c, ((rho3 π (g * blockSL (sl2Up K) * g⁻¹) : ↥H) : MulAut W) v₁ *
          v₁⁻¹ = c := ⟨_, rfl⟩
      obtain ⟨c₂, hc₂def⟩ : ∃ c, ((rho3 π (g * blockSL (sl2Low K) * g⁻¹) : ↥H) : MulAut W) v₀ *
          v₀⁻¹ = c := ⟨_, rfl⟩
      rw [hc₁def] at hc₁ hfu
      rw [hc₂def] at hc₂ hfu
      obtain ⟨z, hz, hdz⟩ : ∃ z ∈ Z, u = c₁ * c₂ * z :=
        ⟨_, (hf.eq_iff _ _).mp hfu, by rw [mul_comm u, mul_inv_cancel_left]⟩
      rw [hdz]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc₁)
        (Subgroup.mem_sup_left hc₂)) (Subgroup.mem_sup_right hz)
    · refine sup_le ((Subgroup.closure_le _).mpr ?_) (hf.le_pre _)
      rintro _ ⟨s, hs, u, hu, rfl⟩
      exact Subgroup.mul_mem _ ((Ch11.SecA.mem_stabW.mp (perfectCore_le _ hs).2 u).mp hu)
        (Subgroup.inv_mem _ hu)
  · intro φ ψ hφU hψU hφm hψm hφS hψS
    obtain ⟨c, hc⟩ := exists_scalar_line hSL hf hZ g hφU hφm hφS
    obtain ⟨d, hd⟩ := exists_scalar_line hSL hf hZ g hψU hψm hψS
    have hχZ : ∀ u ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup,
        φ (ψ u) * (ψ (φ u))⁻¹ ∈ Z := fun u hu => (hf.eq_iff _ _).mp (by
      rw [hc _ (hψU u hu), hd u hu, hd _ (hφU u hu), hc u hu, smul_smul, smul_smul, mul_comm])
    let C : Subgroup W :=
      { carrier := {y | y ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup ∧
          φ (ψ y) = ψ (φ y)}
        mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
          rw [hψm _ ha.1 _ hb.1, hφm _ (hψU _ ha.1) _ (hψU _ hb.1), ha.2, hb.2,
            hφm _ ha.1 _ hb.1, hψm _ (hφU _ ha.1) _ (hφU _ hb.1)]⟩
        one_mem' := ⟨Subgroup.one_mem _, by
          rw [map_one_of_mul hψm, map_one_of_mul hφm, map_one_of_mul hψm]⟩
        inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
          rw [map_inv_of_mul hψm ha.1, map_inv_of_mul hφm (hψU _ ha.1), ha.2,
            map_inv_of_mul hφm ha.1, map_inv_of_mul hψm (hφU _ ha.1)]⟩ }
    have hle : Ch11.SecA.commS (perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)))
        (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) ≤ C := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨s, hs, u, hu, rfl⟩
      have hst := Ch11.SecA.mem_stabW.mp (perfectCore_le _ hs).2
      have hsu := (hst u).mp hu
      have hψu := hψU u hu
      have hφu := hφU u hu
      refine ⟨Subgroup.mul_mem _ hsu (Subgroup.inv_mem _ hu), ?_⟩
      rw [hψm _ hsu _ (Subgroup.inv_mem _ hu), map_inv_of_mul hψm hu, hψS s hs u hu,
        hφm _ ((hst _).mp hψu) _ (Subgroup.inv_mem _ hψu), map_inv_of_mul hφm hψu,
        hφS s hs _ hψu, hφm _ hsu _ (Subgroup.inv_mem _ hu), map_inv_of_mul hφm hu,
        hφS s hs u hu, hψm _ ((hst _).mp hφu) _ (Subgroup.inv_mem _ hφu),
        map_inv_of_mul hψm hφu, hψS s hs _ hφu]
      obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ Z, φ (ψ u) = z * ψ (φ u) := ⟨_, hχZ u hu, by group⟩
      rw [hzdef, map_mul, hZ s (perfectCore_le _ hs).1 z hz, mul_comm z, _root_.mul_inv_rev,
        mul_comm (ψ (φ u))⁻¹, mul_assoc, mul_inv_cancel_left]
    intro y hy
    exact (hle hy).2

end CFSG.Quasithin.Vol2.KGNat
