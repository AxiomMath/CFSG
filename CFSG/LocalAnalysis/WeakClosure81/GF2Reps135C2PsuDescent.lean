module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuLabelData
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent
import CFSG.LieType.SpecialLinear.ExteriorModel.AdjointHeart
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.GraphSwitch
import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
public import CFSG.LieType.SpecialLinear.ExteriorModel.Fundamental

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem c2psudes_exists_equiv_single {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {k : Type} [Field k] [CharP k 2] (φ₀ : F →+* k) {m : ℕ}
    (ε : Fin f → Finset (Fin m)) {r₀ : Fin f} {j : Fin m}
    (h₀ : ε r₀ = {j}) (hrest : ∀ r, r ≠ r₀ → ε r = ∅) :
    ∃ β : BModel k ε ≃ₗ[k] (Set.powersetCard (Fin m) j → k), ∀ g v,
      β (suRep φ₀ m ε g v) =
        ((minorMatrix (j : ℕ) (SUExtras.mat (unitaryInvolution F 2 f) m g)).map
          (suFrob φ₀ f r₀)) *ᵥ β v := by
  classical
  have hε : ∀ r, (ε r).card ≤ 1 := by
    intro r
    by_cases hr : r = r₀
    · subst hr
      rw [h₀]
      simp
    · rw [hrest r hr]
      simp
  let e := bIdxEquivSingle ε r₀ j h₀ hrest
  let β : BModel k ε ≃ₗ[k] (Set.powersetCard (Fin m) j → k) :=
    (bModelEquivOfCardLeOne (k := k) ε hε).trans (LinearEquiv.funCongrLeft k k e.symm)
  refine ⟨β, ?_⟩
  intro g v
  let H : Fin f → SpecialLinearGroup (Fin m) k := suTwist φ₀ f m g
  let T : Matrix (Set.powersetCard (Fin m) j) (Set.powersetCard (Fin m) j) k :=
    (minorMatrix (j : ℕ) (SUExtras.mat (unitaryInvolution F 2 f) m g)).map (suFrob φ₀ f r₀)
  have hH : (fun r => (H r : Matrix (Fin m) (Fin m) k)) =
      fun r => (SUExtras.mat (unitaryInvolution F 2 f) m g).map (suFrob φ₀ f r) := by
    funext r
    exact coe_suTwist_apply φ₀ m g r
  have hmat : bMat ε (fun r => (H r : Matrix (Fin m) (Fin m) k)) =
      Matrix.reindex e.symm e.symm T := by
    ext s t
    rw [bMat_apply_of_single ε r₀ j h₀ hrest, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [congrFun hH r₀]
    dsimp only [T]
    simp only [minor_map, Matrix.map_apply, minorMatrix, Matrix.of_apply, Equiv.symm_symm]
    rfl
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bModelEquivOfCardLeOne (k := k) ε hε) (suRep φ₀ m ε g v)) = _
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bModelEquivOfCardLeOne (k := k) ε hε)
        (bRep ε ((suTwist φ₀ f m) g) v)) = _
  rw [bModelEquivOfCardLeOne_bRep ε hε ((suTwist φ₀ f m) g) v]
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bMat ε (fun r => (H r : Matrix (Fin m) (Fin m) k))) *ᵥ
        (bModelEquivOfCardLeOne (k := k) ε hε v)) =
    T *ᵥ (LinearEquiv.funCongrLeft k k e.symm (bModelEquivOfCardLeOne (k := k) ε hε v))
  rw [hmat]
  rw [← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply]
  rw [Matrix.mulVecLin_reindex]
  rw [Equiv.symm_symm, ← LinearEquiv.funCongrLeft_symm]
  simp only [LinearMap.comp_apply]
  exact LinearEquiv.symm_apply_apply (LinearEquiv.funCongrLeft k k e) _

private theorem c2psudes_adjugate_rev_apply {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {m : ℕ} (g : SU (unitaryInvolution F 2 f) m) (a b : Fin m) :
    adjugate (SUExtras.mat (unitaryInvolution F 2 f) m g) (Fin.rev b) (Fin.rev a) =
      unitaryInvolution F 2 f ((SUExtras.mat (unitaryInvolution F 2 f) m g) a b) := by
  have hA : ((g : GL (Fin m) F)) ∈ SU (unitaryInvolution F 2 f) m := g.2
  have hdet : (SUExtras.mat (unitaryInvolution F 2 f) m g).det = 1 := by
    rw [SUExtras.mat_apply]
    exact (mem_SU.mp hA).1
  have hN : (((g : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (SUExtras.mat (unitaryInvolution F 2 f) m g)⁻¹ := by
    rw [SUExtras.mat_apply]
    exact Matrix.GeneralLinearGroup.coe_inv (n := Fin m) (R := F) (g : GL (Fin m) F)
  have hadj : adjugate (SUExtras.mat (unitaryInvolution F 2 f) m g) =
      (((g : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
    rw [hN, Matrix.inv_def, hdet]
    simp
  have key : (((g : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
      (Fin.rev b) (Fin.rev a) =
      unitaryInvolution F 2 f ((SUExtras.mat (unitaryInvolution F 2 f) m g) a b) := by
    have h := congrFun (congrFun
      (inv_transpose_eq_submatrix_rev_of_mem_SU (σ := unitaryInvolution F 2 f) hA)
      (Fin.rev a)) (Fin.rev b)
    simpa [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply,
      SUExtras.mat_apply] using h
  rw [hadj, key]

private theorem c2psudes_minorMatrix_one_submatrix {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {k : Type} [Field k] [CharP k 2] (φ₀ : F →+* k) {m : ℕ}
    (g : SU (unitaryInvolution F 2 f) m) (r₀ : Fin f)
    (e : Fin m ≃ Set.powersetCard (Fin m) 1)
    (he : ∀ x, (e x : Finset (Fin m)) = {x}) :
    ((minorMatrix 1 (SUExtras.mat (unitaryInvolution F 2 f) m g)).map (suFrob φ₀ f r₀)).submatrix
        (fun x => e x) (fun x => e x) =
      (SUExtras.mat (unitaryInvolution F 2 f) m g).map (suFrob φ₀ f r₀) := by
  ext a b
  rw [Matrix.submatrix_apply, Matrix.map_apply, minorMatrix, Matrix.of_apply,
    AdjointHeartModel.minor_singleton rfl _ _ _ (he a) (he b)]
  rfl

private theorem c2psudes_minorMatrix_compl_submatrix {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {k : Type} [Field k] [CharP k 2] (φ₀ : F →+* k) {m : ℕ} (hm : 1 ≤ m)
    (g : SU (unitaryInvolution F 2 f) m) (r₀ : Fin f)
    (e : Fin m ≃ Set.powersetCard (Fin m) (m - 1))
    (he : ∀ x, (e x : Finset (Fin m)) = {Fin.rev x}ᶜ) :
    ((minorMatrix (m - 1) (SUExtras.mat (unitaryInvolution F 2 f) m g)).map
        (suFrob φ₀ f r₀)).submatrix (fun x => e x) (fun x => e x) =
      (SUExtras.mat (unitaryInvolution F 2 f) m g).map
        ((suFrob φ₀ f r₀).comp (unitaryInvolution F 2 f).toRingHom) := by
  ext a b
  rw [Matrix.submatrix_apply, Matrix.map_apply, minorMatrix, Matrix.of_apply,
    AdjointHeartModel.minor_compl_singleton (n := m) (by omega)
      (SUExtras.mat (unitaryInvolution F 2 f) m g) rfl (e a) (e b) (he a) (he b)]
  rw [c2psudes_adjugate_rev_apply g a b]
  rfl

private theorem c2psudes_theta_action_aux {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {k : Type} [Field k] [CharP k 2] (φ₀ : F →+* k) {m : ℕ}
    (ε : Fin f → Finset (Fin m)) {r₀ : Fin f} {j : Fin m}
    (h₀ : ε r₀ = {j}) (hrest : ∀ r, r ≠ r₀ → ε r = ∅)
    (e : Fin m ≃ Set.powersetCard (Fin m) j) (τ' : F →+* k)
    (hsub : ∀ g : SU (unitaryInvolution F 2 f) m,
      ((minorMatrix (j : ℕ) (SUExtras.mat (unitaryInvolution F 2 f) m g)).map
        (suFrob φ₀ f r₀)).submatrix e e =
      (SUExtras.mat (unitaryInvolution F 2 f) m g).map τ') :
    ∃ Θ : BModel k ε ≃ₗ[k] (Fin m → k), ∀ g v,
      Θ (suRep φ₀ m ε g v) =
        ((SUExtras.mat (unitaryInvolution F 2 f) m g).map τ') *ᵥ Θ v := by
  classical
  obtain ⟨β', hβ'⟩ := c2psudes_exists_equiv_single φ₀ ε h₀ hrest
  let Θ : BModel k ε ≃ₗ[k] (Fin m → k) :=
    β'.trans (LinearEquiv.funCongrLeft k k e)
  refine ⟨Θ, ?_⟩
  intro g v
  let M : Matrix (Set.powersetCard (Fin m) j) (Set.powersetCard (Fin m) j) k :=
    (minorMatrix (j : ℕ) (SUExtras.mat (unitaryInvolution F 2 f) m g)).map (suFrob φ₀ f r₀)
  let N : Matrix (Fin m) (Fin m) k :=
    (SUExtras.mat (unitaryInvolution F 2 f) m g).map τ'
  have hreindex : ∀ w : Set.powersetCard (Fin m) j → k,
      (LinearEquiv.funCongrLeft k k e) (M *ᵥ w) =
        (M.submatrix e e) *ᵥ (LinearEquiv.funCongrLeft k k e w) := by
    intro w
    funext i
    rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Matrix.mulVec_apply_eq_sum]
    conv_rhs => rw [Matrix.mulVec_apply_eq_sum, ← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Matrix.submatrix_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  have hβg : β' (suRep φ₀ m ε g v) = M *ᵥ β' v := hβ' g v
  have hsubg : M.submatrix e e = N := hsub g
  change (LinearEquiv.funCongrLeft k k e) (β' (suRep φ₀ m ε g v)) =
    N *ᵥ (LinearEquiv.funCongrLeft k k e (β' v))
  rw [hβg, ← hsubg]
  exact hreindex (β' v)

theorem w135c2_psu_descent {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W) [ρ.IsIrreducible]
    {ε : Fin f → Finset (Fin m)} (hε : HasUnitaryLabel (by omega : 2 ≤ m) hK ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule) = 2 ^ s) (hs : 2 * f ≤ s)
    (r₀ : Fin f) (j : Fin m) (hrest : ∀ r, r ≠ r₀ → ε r = ∅) (h₀ : ε r₀ = {j})
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = m) :
    ∃ β : W ≃+ (Fin m → K), ∀ (g : SU (unitaryInvolution K 2 f) m) (w : W),
      β (ρ g w) = ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ β w := by
  classical
  obtain ⟨k, hk, hchar, halg, φ₀, ζ, hζ, y₀, χ, μ, htype, -, -, β₀, hβ₀⟩ := hε
  let E := Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m)) ρ.asModule
  let X := ρ.asModule
  have hmodel :
      ∃ (τ' : K →+* k) (Θ : BModel k ε ≃ₗ[k] (Fin m → k)),
        ∀ (g : SU (unitaryInvolution K 2 f) m) (v : BModel k ε),
          Θ (suRep φ₀ m ε g v) =
            ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map τ' *ᵥ Θ v := by
    rcases hj with hj | hj
    · have hj1 : j = (⟨1, by omega⟩ : Fin m) := Fin.ext hj
      rw [hj1] at h₀
      let e : Fin m ≃ Set.powersetCard (Fin m) 1 := Set.powersetCard.ofSingleton
      have he : ∀ x : Fin m, (e x : Finset (Fin m)) = {x} := fun x => rfl
      obtain ⟨Θ, hΘ⟩ := c2psudes_theta_action_aux φ₀ ε h₀ hrest e (suFrob φ₀ f r₀)
        (fun g => c2psudes_minorMatrix_one_submatrix φ₀ g r₀ e he)
      exact ⟨suFrob φ₀ f r₀, Θ, hΘ⟩
    · have hj2 : (j : ℕ) = m - 1 := by omega
      have hj1 : j = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext hj2
      rw [hj1] at h₀
      let e : Fin m ≃ Set.powersetCard (Fin m) (m - 1) :=
        Equiv.ofBijective (fun a => ⟨{Fin.rev a}ᶜ, by simp [Finset.card_compl]⟩)
          ⟨fun a b h => Fin.rev_injective
              (Finset.singleton_injective (compl_injective (congrArg Subtype.val h))),
            fun s => by
              have hc : (s : Finset (Fin m))ᶜ.card = 1 := by
                rw [Finset.card_compl, s.2, Fintype.card_fin]
                omega
              obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
              refine ⟨Fin.rev a, Subtype.ext ?_⟩
              show ({Fin.rev (Fin.rev a)}ᶜ : Finset (Fin m)) = s
              rw [Fin.rev_rev, ← ha, compl_compl]⟩
      have he : ∀ x : Fin m, (e x : Finset (Fin m)) = {Fin.rev x}ᶜ := fun x => rfl
      obtain ⟨Θ, hΘ⟩ := c2psudes_theta_action_aux φ₀ ε h₀ hrest e
        ((suFrob φ₀ f r₀).comp (unitaryInvolution K 2 f).toRingHom)
        (fun g => c2psudes_minorMatrix_compl_submatrix φ₀ (by omega) g r₀ e he)
      exact ⟨(suFrob φ₀ f r₀).comp (unitaryInvolution K 2 f).toRingHom, Θ, hΘ⟩
  obtain ⟨τ', Θ, hΘ⟩ := hmodel
  letI : Algebra K k := τ'.toAlgebra
  let T : SU (unitaryInvolution K 2 f) m → Matrix (Fin m) (Fin m) K :=
    fun g => ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
  let Φ : W →+ (Fin m → k) :=
    (Θ.toLinearMap.toAddMonoidHom.comp β₀.toLinearMap.toAddMonoidHom).comp
      ((TensorProduct.mk E k X 1).toAddMonoidHom.comp ρ.asModuleEquiv.symm.toAddMonoidHom)
  have hΦ : ∀ w : W, Φ w = Θ (β₀ ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w)) := fun w => rfl
  have hTmap : ∀ g, (T g).map (algebraMap K k) = (T g).map τ' := fun g => by
    rw [RingHom.algebraMap_toAlgebra]
  have hΦeq : ∀ (g : SU (unitaryInvolution K 2 f) m) (w : W),
      Φ (ρ g w) = (T g).map (algebraMap K k) *ᵥ Φ w := by
    intro g w
    rw [hΦ, hΦ, hTmap g]
    have h1 : ρ.asModuleEquiv.symm (ρ g w) =
        CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w) := by
      rw [CFSG.endFieldRep_apply]
      exact congrArg (fun v => ρ.asModuleEquiv.symm (ρ g v))
        (ρ.asModuleEquiv.apply_symm_apply w).symm
    have h2 : ((1 : k) ⊗ₜ[E] (CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w))) =
        CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g
          ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w) := by
      rw [CFSG.Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul]
    rw [h1, h2, hβ₀, hΘ]
  letI : DistribMulAction (SU (unitaryInvolution K 2 f) m) W := DistribMulAction.compHom W ρ
  haveI : Nontrivial W :=
    ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp
      (inferInstance : ρ.IsIrreducible)).1
  have hΦ0 : Φ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    intro h0
    have hw0 : Φ w = 0 := by rw [h0]; rfl
    rw [hΦ] at hw0
    have h1 : (1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w = 0 := by
      apply β₀.injective
      apply Θ.injective
      simpa using hw0
    have h2 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff E X (A := k)
      (ρ.asModuleEquiv.symm w)).mp h1
    exact hw (by simpa using congrArg ρ.asModuleEquiv h2)
  have hV : IsIrreducibleAdd
      (fun (g : SU (unitaryInvolution K 2 f) m) (v : W) => g • v) := by
    intro A hA
    have hirr' := ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp
      (inferInstance : ρ.IsIrreducible)).2
    rcases hirr' (AddSubgroup.toZModSubmodule 2 A)
      (fun g u hu => by
        rw [AddSubgroup.mem_toZModSubmodule] at hu ⊢
        exact hA g hu) with h | h
    · left
      rw [← AddSubgroup.toZModSubmodule_toAddSubgroup (n := 2) A, h]
      rfl
    · right
      rw [← AddSubgroup.toZModSubmodule_toAddSubgroup (n := 2) A, h]
      rfl
  obtain ⟨Ψ, hΨ0, hΨeq⟩ := exists_addHom_of_extend T Φ hΦ0 hΦeq
  have hker : Ψ.ker = ⊥ := by
    rcases hV Ψ.ker (fun g v hv => by
      rw [AddMonoidHom.mem_ker] at hv ⊢
      rw [hΨeq g v, hv, Matrix.mulVec_zero]) with h | h
    · exact h
    · exfalso
      exact hΨ0 ((AddMonoidHom.ker_eq_top_iff).mp h)
  have hinj : Function.Injective Ψ := (AddMonoidHom.ker_eq_bot_iff Ψ).mp hker
  have hfinB : finrank k (BModel k ε) = m := by
    rw [Θ.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hcardW : Nat.card W = 2 ^ (s * m) := by
    have h1 := card_eq_pow_finrank_extendScalars (ρ := ρ) k
    rw [hE, β₀.finrank_eq, hfinB, ← pow_mul] at h1
    exact h1
  have hcardK : Nat.card (Fin m → K) = 2 ^ (2 * f * m) := by
    calc Nat.card (Fin m → K) = (Nat.card K) ^ m := by
          rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ((2 ^ f) ^ 2) ^ m := by rw [hK]
      _ = 2 ^ (2 * f * m) := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          ring
  have hle : Nat.card (Fin m → K) ≤ Nat.card W := by
    rw [hcardK, hcardW]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right m hs)
  have hbij : Function.Bijective Ψ :=
    Function.Injective.bijective_of_nat_card_le hinj hle
  exact ⟨AddEquiv.ofBijective Ψ hbij, fun g w => hΨeq g w⟩

end CFSG.LocalAnalysis.WeakClosure81
