module

public import CFSG.Quasithin.Vol2.Ch11SecAKDf
public import CFSG.Quasithin.H13.VolIAltCoverG2Field
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix

section ActionModel

variable {W : Type} [CommGroup W]

theorem exists_model_action {D : FFModel} (h : D.IsActionModel) (hD : D.Faithful)
    {H : Subgroup (MulAut W)} (hR : D.Realizes H ⊤ ⊥) :
    ∃ (π : D.Gam ≃* ↥H) (e : W ≃* D.Mod),
      ∀ γ w, e (((π γ : ↥H) : MulAut W) w) = h.modAct γ (e w) := by
  obtain ⟨π, hπ⟩ := hR
  have hinj := FFC.injective_of_faithful_sec hD hπ
  obtain ⟨hs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e : W ≃* D.Mod := Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)
  refine ⟨MulEquiv.ofBijective π ⟨hinj, hs⟩, e, fun γ w => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
  have h1 := hβe γ ⟨w, trivial⟩ m trivial (h.sec_inv γ m m.2) hm.symm
  refine h1.trans ?_
  change _ = h.modAct γ (β ⟨w, trivial⟩)
  rw [← hm]
  rfl

end ActionModel

section Zorn

variable (K : Type) [Field K]

theorem g2D_le : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
  Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)

variable [CharP K 2]

@[expose] noncomputable def g2QA :
    ↥⁅quasithinG2 K, quasithinG2 K⁆ →* MulAut (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Mod :=
  (FFModel.zornQ_isActionModel ⁅quasithinG2 K, quasithinG2 K⁆ (g2D_le K)).modAct

variable {K}

theorem zornQSec_comm (σ : K ≃+* K) (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (m : ↥(zornO0 K)) :
    CFSG.Quasithin.H13.VolI.zornQSecEquiv σ
        (g2QA K γ (QuotientGroup.mk m : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Mod)) =
      g2QA K (CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv σ γ)
        (CFSG.Quasithin.H13.VolI.zornQSecEquiv σ
          (QuotientGroup.mk m : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Mod)) := by
  obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective
    (CFSG.Quasithin.H13.VolI.zornQSecEquiv σ
      (QuotientGroup.mk m : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Sec))
  have hm0 : zornAct _ γ m.1 ∈ zornO0 K := zornAct_mem_O0 _ (g2D_le K) γ m.2
  have hm1 : zornAct _ (CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv σ γ) m'.1 ∈ zornO0 K :=
    zornAct_mem_O0 _ (g2D_le K) _ m'.2
  have key := CFSG.Quasithin.H13.VolI.zornQSecEquiv_act σ γ _ rfl m m' hm'.symm hm0 hm1
  rw [← hm']
  exact key

theorem zeta_mem_indM (σ : K ≃+* K) :
    CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv σ ∈ indM (g2QA K) := by
  refine ⟨CFSG.Quasithin.H13.VolI.zornQSecEquiv σ, fun γ => MulEquiv.ext fun q => ?_⟩
  obtain ⟨q', rfl⟩ := (CFSG.Quasithin.H13.VolI.zornQSecEquiv σ).surjective q
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  refine QuotientGroup.induction_on q' fun m => ?_
  exact (zornQSec_comm σ γ m).symm

end Zorn

section Trace

variable {K : Type} [Field K]

@[expose] noncomputable def trO (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) : K :=
  LinearMap.trace K (quasithinZorn K) (g : quasithinZorn K →ₗ[K] quasithinZorn K)

theorem trO_conj (c g : quasithinZorn K ≃ₗ[K] quasithinZorn K) : trO (c * g * c⁻¹) = trO g := by
  rw [trO, trO, ← LinearMap.trace_conj' (g : quasithinZorn K →ₗ[K] quasithinZorn K) c]
  congr 1

theorem trace_gALin (A : Matrix (Fin 3) (Fin 3) K) :
    LinearMap.trace K (quasithinZorn K) (gALin A) =
      1 + (A.trace + ((adjugate A)ᵀ.trace + 1)) := by
  have h : gALin A = LinearMap.prodMap LinearMap.id (LinearMap.prodMap (Matrix.toLin' A)
      (LinearMap.prodMap (Matrix.toLin' (adjugate A)ᵀ) LinearMap.id)) :=
    LinearMap.ext fun x => rfl
  rw [h, LinearMap.trace_prodMap', LinearMap.trace_prodMap', LinearMap.trace_prodMap',
    LinearMap.trace_id, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Module.finrank_self,
    Nat.cast_one]

@[expose] def compM (t : K) : Matrix (Fin 3) (Fin 3) K := !![t, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_compM (t : K) : (compM t).det = 1 := by
  simp [compM, Matrix.det_fin_three]

@[expose] def compSL (t : K) : SL3 K := ⟨compM t, det_compM t⟩

theorem trace_compM (t : K) : (compM t).trace = t := by
  simp [compM, Matrix.trace_fin_three]

theorem trace_adj_compM (t : K) : ((adjugate (compM t))ᵀ).trace = 0 := by
  rw [Matrix.trace_transpose]
  simp [compM, Matrix.adjugate_fin_three, Matrix.trace_fin_three]

theorem trO_g2A_comp [CharP K 2] (t : K) :
    trO ((g2A (compSL t) : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) = t := by
  rw [trO]
  change LinearMap.trace K (quasithinZorn K) (gALin (compM t)) = t
  rw [trace_gALin, trace_compM, trace_adj_compM]
  linear_combination (CharTwo.two_eq_zero : (2 : K) = 0)

theorem gAFun_compM (t r u₀ u₁ u₂ v₀ v₁ v₂ s : K) :
    gAFun (compM t) (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk r (t * u₀ + u₂) u₀ u₁ v₂ (v₀ - t * v₂) v₁ s := by
  simp only [gAFun, zmk, Prod.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    simp [compM, Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals ring

theorem zornConj_g2A_comp (σ : K ≃+* K) (t : K) :
    zornConj σ ((g2A (compSL t) : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) =
      ((g2A (compSL (σ t)) : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) := by
  refine LinearEquiv.ext fun y => ?_
  rw [zornConj_apply, g2A_apply, g2A_apply]
  change zornMap σ (gAFun (compM t) (zornMap σ.symm y)) = gAFun (compM (σ t)) y
  have hy : zornMap σ.symm y = zmk (σ.symm y.1) (σ.symm (y.2.1 0)) (σ.symm (y.2.1 1))
      (σ.symm (y.2.1 2)) (σ.symm (y.2.2.1 0)) (σ.symm (y.2.2.1 1)) (σ.symm (y.2.2.1 2))
      (σ.symm y.2.2.2) := by
    rw [zorn_eta (zornMap σ.symm y)]
    rfl
  rw [hy, gAFun_compM, zorn_eta y, gAFun_compM]
  simp only [zornMap, zmk, Prod.mk.injEq, RingEquiv.apply_symm_apply, true_and, and_true]
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp

end Trace

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
