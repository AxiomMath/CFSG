module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Defs
public import CFSG.Quasithin.Vol2.Ch9H11Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KO4PlusSwap.Transport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped Matrix MatrixGroups
open CFSG.Quasithin.H13.H11P
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit (DeterminantIsometries
  determinantForm_apply specialImage specialRho specialRho_apply tau tau_apply)
open CFSG.Quasithin.G11.P3Ortho.Om4 (Ψ Ψ_apply toMat mem_specialImage_or_mul_tau)

section Model

variable {K : Type} [Field K]

theorem w4t_o4_exists_isometry {x : MulAut (VM K)} (hx : x ∈ kLin K)
    (hdet : ∀ X : Mat K, (addMap x X).det = X.det) :
    ∃ a ∈ DeterminantIsometries K,
      AddEquiv.toMultiplicative (a : Mat K ≃ₗ[K] Mat K).toAddEquiv = x := by
  let a : Mat K ≃ₗ[K] Mat K :=
    { toFun := addMap x
      map_add' := map_add (addMap x)
      map_smul' := fun l X => hx l X
      invFun := addMap x⁻¹
      left_inv := fun X => by rw [← addMap_mul, inv_mul_cancel, addMap_one]
      right_inv := fun X => addMap_inv_apply x X }
  refine ⟨a, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun X => ?_,
    eq_of_addMap fun X => rfl⟩
  rw [determinantForm_apply, determinantForm_apply]
  exact hdet X

theorem w4t_o4_swap_scalar [CharP K 2] {x : MulAut (VM K)} {c : K}
    {P Q : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : ∀ X, addMap x X = c • ((P : Mat K) * Xᵀ * (Q : Mat K)ᵀ)) (hxx : x * x = 1) : c = 1 := by
  have hxx' : addMap x (addMap x 1) = 1 := by rw [← addMap_mul, hxx, addMap_one]
  rw [h, h] at hxx'
  have hdet := congrArg Matrix.det hxx'
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_one, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe,
    Matrix.det_one, Fintype.card_fin, mul_one] at hdet
  have hc1 : c * c = 1 := eq_one_of_sq_eq_one hdet
  exact eq_one_of_sq_eq_one (by rw [sq]; exact hc1)

theorem w4t_o4_mem_commV_Lm (X : Mat K) : Multiplicative.ofAdd X ∈ commV (Lm K) := by
  have hmem : ∀ (g : SL(2, K)) (Y : Mat K),
      Multiplicative.ofAdd ((g : Mat K) * Y - Y) ∈ commV (Lm K) := by
    intro g Y
    have e : rho (g, 1) (Multiplicative.ofAdd Y) * (Multiplicative.ofAdd Y)⁻¹ =
        Multiplicative.ofAdd ((g : Mat K) * Y - Y) := by
      show Multiplicative.ofAdd ((g : Mat K) * Y * ((1 : SL(2, K)) : Mat K)ᵀ) *
        (Multiplicative.ofAdd Y)⁻¹ = _
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one, ← ofAdd_neg,
        ← ofAdd_add, ← sub_eq_add_neg]
    rw [← e]
    exact Subgroup.subset_closure ⟨rho (g, 1), ⟨(g, 1), rfl⟩, Multiplicative.ofAdd Y, rfl⟩
  have hX : X = ((uu 1 : SL(2, K)) : Mat K) * !![0, 0; X 0 0, X 0 1] - !![0, 0; X 0 0, X 0 1] +
      (((ul 1 : SL(2, K)) : Mat K) * !![X 1 0, X 1 1; 0, 0] - !![X 1 0, X 1 1; 0, 0]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_uu, coe_ul]
  rw [hX, ofAdd_add]
  exact (commV (Lm K)).mul_mem (hmem _ _) (hmem _ _)

theorem w4t_o4_swap_form [CharP K 2] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {x : MulAut (VM K)} (hN : x ∈ NLm K) (hxx : x * x = 1) (hx : x ∉ Lm K)
    (hrk : rkIdx (fixV (Subgroup.zpowers x)) = n) :
    ∃ P Q : SL(2, K), ∀ X, addMap x X = (P : Mat K) * Xᵀ * (Q : Mat K)ᵀ := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, -, P, Q, σ, hform⟩ := normal_form h4 hN
  have hsemi : IsSemi x σ := isSemi_of_form hform
  have hσ : σ = 1 := by
    by_contra hσ
    have hsq := card_fix_sq (Y := ⊤) (fun _ _ _ => Subgroup.mem_top _) hsemi hσ hxx
      (fun _ _ => Subgroup.mem_top _)
    have hC : Nat.card {X : Mat K // MemM (⊤ : Subgroup (VM K)) X ∧ addMap x X = X} =
        Nat.card (fixV (Subgroup.zpowers x)) := by
      rw [card_eq_card_memM]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun X => by
        rw [memM_fixV_zpowers]
        exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top _, h⟩⟩)
    have hT4 : Nat.card {X : Mat K // MemM (⊤ : Subgroup (VM K)) X} = (2 ^ (2 * n)) ^ 2 := by
      rw [← card_eq_card_memM, Subgroup.card_top, card_VM, hK, ← pow_mul, ← pow_mul]
      ring_nf
    rw [hC, hT4, ← sq] at hsq
    have hfix : Nat.card (fixV (Subgroup.zpowers x)) = 2 ^ (2 * n) :=
      Nat.pow_left_injective two_ne_zero hsq
    have hVM : Nat.card (VM K) = 2 ^ (4 * n) := by
      rw [card_VM, hK, ← pow_mul, mul_comm]
    have hrk' := rkIdx_eq_of_card hfix hVM
    omega
  subst hσ
  rcases mem_Lm_or_swap h4 hN hsemi hxx with hLm | ⟨c', -, P', Q', hswap⟩
  · exact absurd hLm hx
  have hc1 : c' = 1 := w4t_o4_swap_scalar hswap hxx
  subst hc1
  exact ⟨P', Q', fun X => by rw [hswap, one_smul]⟩

theorem w4t_o4_mem_sup_iff [CharP K 2] [Finite K] {x : MulAut (VM K)} {P Q : SL(2, K)}
    (hx : ∀ X, addMap x X = (P : Mat K) * Xᵀ * (Q : Mat K)ᵀ) (y : MulAut (VM K)) :
    y ∈ Lm K ⊔ Subgroup.zpowers x ↔ ∃ a ∈ DeterminantIsometries K,
      AddEquiv.toMultiplicative (a : Mat K ≃ₗ[K] Mat K).toAddEquiv = y := by
  let ι : (Mat K ≃ₗ[K] Mat K) →* MulAut (VM K) :=
    { toFun := fun g => AddEquiv.toMultiplicative g.toAddEquiv
      map_one' := MulEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl }
  have hxlin : x ∈ kLin K := fun l X => by
    rw [hx, hx, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have htrn : trn = (rho (P, Q))⁻¹ * x := by
    rw [eq_inv_mul_iff_mul_eq]
    refine eq_of_addMap fun X => ?_
    rw [addMap_mul, addMap_trn, addMap_rho, hx]
  have hle : Lm K ⊔ Subgroup.zpowers x ≤ (DeterminantIsometries K).map ι := by
    refine sup_le ?_ ?_
    · rintro _ ⟨p, rfl⟩
      obtain ⟨a, ha, hax⟩ := w4t_o4_exists_isometry (rho_mem_kLin p) fun X => by
        rw [addMap_rho, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
          Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]
      exact ⟨a, ha, hax⟩
    · rw [Subgroup.zpowers_le]
      obtain ⟨a, ha, hax⟩ := w4t_o4_exists_isometry hxlin fun X => by
        rw [hx, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
          Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]
      exact ⟨a, ha, hax⟩
  have hspec : ∀ g : ↥(DeterminantIsometries K), g ∈ specialImage K →
      ι (g : Mat K ≃ₗ[K] Mat K) ∈ Lm K := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(z.1, ⟨((z.2⁻¹ : SL(2, K)) : Mat K)ᵀ, by
      rw [Matrix.det_transpose]
      exact (z.2⁻¹).2⟩), eq_of_addMap fun X => ?_⟩
    rw [addMap_rho]
    show _ = (specialRho z : Mat K ≃ₗ[K] Mat K) X
    rw [specialRho_apply, Matrix.transpose_transpose]
  constructor
  · intro hy
    obtain ⟨a, ha, hay⟩ := hle hy
    exact ⟨a, ha, hay⟩
  · rintro ⟨a, ha, rfl⟩
    show ι a ∈ Lm K ⊔ Subgroup.zpowers x
    rcases mem_specialImage_or_mul_tau ⟨a, ha⟩ with h | h
    · exact (le_sup_left : Lm K ≤ _) (hspec _ h)
    · have e : ι a = ι ((⟨a, ha⟩ * tau : DeterminantIsometries K) : Mat K ≃ₗ[K] Mat K) * trn := by
        refine eq_of_addMap fun X => ?_
        rw [addMap_mul, addMap_trn]
        show a X = ((⟨a, ha⟩ * tau : DeterminantIsometries K) : Mat K ≃ₗ[K] Mat K) Xᵀ
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, tau_apply, Matrix.transpose_transpose]
      rw [e, htrn]
      exact mul_mem ((le_sup_left : Lm K ≤ _) (hspec _ h)) (mul_mem (inv_mem
        ((le_sup_left : Lm K ≤ _) ⟨(P, Q), rfl⟩)) ((le_sup_right : _ ≤ Lm K ⊔ _)
          (Subgroup.mem_zpowers x)))

end Model

section Realization

variable {K : Type} [Field K]

theorem w4t_o4_realizes {W : Type} [CommGroup W] {R : Subgroup (MulAut W)} (ψ : W ≃* VM K)
    (hR : ∀ r : MulAut W, r ∈ R ↔ ∃ a ∈ DeterminantIsometries K,
      AddEquiv.toMultiplicative (a : Mat K ≃ₗ[K] Mat K).toAddEquiv = MulAut.congr ψ r) :
    (FFModel.nat (CFSG.PGLModel.orthogonalPlus 2 K)).Realizes R (commV R) ⊥ := by
  classical
  let ι : (Mat K ≃ₗ[K] Mat K) →* MulAut (VM K) :=
    { toFun := fun g => AddEquiv.toMultiplicative g.toAddEquiv
      map_one' := MulEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl }
  have hΦapp : ∀ (a : MulAut W) (v : VM K), MulAut.congr ψ a v = ψ (a (ψ.symm v)) := fun a v => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hΦsymm : ∀ (a : MulAut (VM K)) (v : W), ψ ((MulAut.congr ψ).symm a v) = a (ψ v) :=
    fun a v => by
      conv_rhs => rw [← (MulAut.congr ψ).apply_symm_apply a]
      rw [hΦapp, MulEquiv.symm_apply_apply]
  have hge : ∀ a ∈ DeterminantIsometries K, (MulAut.congr ψ).symm (ι a) ∈ R := fun a ha =>
    (hR _).mpr ⟨a, ha, ((MulAut.congr ψ).apply_symm_apply _).symm⟩
  have hrhoR : ∀ p : SL(2, K) × SL(2, K), (MulAut.congr ψ).symm (rho p) ∈ R := by
    intro p
    obtain ⟨a, ha, hax⟩ := w4t_o4_exists_isometry (rho_mem_kLin p) fun X => by
      rw [addMap_rho, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]
    have h := hge a ha
    rwa [show ι a = rho p from hax] at h
  have hcommV : commV R = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hmono : commV (Lm K) ≤ commV (R.map (MulAut.congr ψ).toMonoidHom) := by
      apply Subgroup.closure_mono
      rintro _ ⟨x, ⟨p, rfl⟩, v, rfl⟩
      exact ⟨rho p, ⟨(MulAut.congr ψ).symm (rho p), hrhoR p,
        (MulAut.congr ψ).apply_symm_apply _⟩, v, rfl⟩
    have hw := hmono (w4t_o4_mem_commV_Lm (Multiplicative.toAdd (ψ w)))
    rw [commV_map_congr_equiv] at hw
    obtain ⟨u, hu, hu'⟩ := hw
    rwa [ψ.injective hu'] at hu
  have hΨ : ∀ γ : ↥(CFSG.PGLModel.orthogonalPlus 2 K),
      Ψ K (γ : GL (Fin 2 ⊕ Fin 2) K) ∈ DeterminantIsometries K := fun γ => by
    rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.KO4Swap.map_orthogonalPlus_two K]
    exact ⟨γ, γ.2, rfl⟩
  let π : ↥(CFSG.PGLModel.orthogonalPlus 2 K) →* ↥R :=
    { toFun := fun γ => ⟨(MulAut.congr ψ).symm (ι (Ψ K γ)), hge _ (hΨ γ)⟩
      map_one' := Subtype.ext (by
        show (MulAut.congr ψ).symm (ι (Ψ K ((1 : ↥(CFSG.PGLModel.orthogonalPlus 2 K)) :
          GL (Fin 2 ⊕ Fin 2) K))) = 1
        rw [OneMemClass.coe_one, map_one, map_one, map_one])
      map_mul' := fun γ δ => Subtype.ext (by
        show (MulAut.congr ψ).symm (ι (Ψ K ((γ * δ : ↥(CFSG.PGLModel.orthogonalPlus 2 K)) :
          GL (Fin 2 ⊕ Fin 2) K))) =
            (MulAut.congr ψ).symm (ι (Ψ K γ)) * (MulAut.congr ψ).symm (ι (Ψ K δ))
        rw [Subgroup.coe_mul, map_mul, map_mul, map_mul]) }
  have hπ : Function.Surjective π := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, hax⟩ := (hR r).mp hr
    rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.KO4Swap.map_orthogonalPlus_two K] at ha
    obtain ⟨γ, hγ, rfl⟩ := ha
    refine ⟨⟨γ, hγ⟩, Subtype.ext ?_⟩
    show (MulAut.congr ψ).symm (ι (Ψ K γ)) = r
    rw [MulEquiv.symm_apply_eq]
    exact hax
  let θ : ↥(commV R) →* ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))) :=
    { toFun := fun u => ⟨Multiplicative.ofAdd ((toMat K).symm (Multiplicative.toAdd (ψ u))),
        Subgroup.mem_top _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u u' => Subtype.ext (by simp) }
  let β := (QuotientGroup.mk' ((⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))).subgroupOf
    ⊤)).comp θ
  refine ⟨π, ?_⟩
  dsimp only [FFModel.RealizesVia, FFModel.nat]
  refine ⟨hπ, bot_le, bot_le, fun _ u _ => ?_, fun h z hz => ?_, fun _ _ _ => Subgroup.mem_top _,
    fun γ m hm => ?_, β, ?_, fun u => ?_, fun γ u m hu hm hβu => ?_⟩
  · rw [hcommV]
    exact Subgroup.mem_top _
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · rw [Subgroup.mem_bot] at hm ⊢
    rw [hm]
    show Multiplicative.ofAdd (_ *ᵥ Multiplicative.toAdd 1) = 1
    rw [toAdd_one, Matrix.mulVec_zero, ofAdd_zero]
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨ψ.symm (Multiplicative.ofAdd (toMat K (Multiplicative.toAdd
      (m : Multiplicative (Fin 2 ⊕ Fin 2 → K))))), hcommV ▸ Subgroup.mem_top _⟩, ?_⟩
    show QuotientGroup.mk (θ _) = QuotientGroup.mk m
    congr 1
    apply Subtype.ext
    show Multiplicative.ofAdd ((toMat K).symm (Multiplicative.toAdd
      (ψ (ψ.symm (Multiplicative.ofAdd (toMat K (Multiplicative.toAdd
        (m : Multiplicative (Fin 2 ⊕ Fin 2 → K))))))))) = (m : Multiplicative (Fin 2 ⊕ Fin 2 → K))
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, LinearEquiv.symm_apply_apply, ofAdd_toAdd]
  · constructor
    · intro h
      have h1 : θ u ∈ (⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))).subgroupOf ⊤ :=
        (QuotientGroup.eq_one_iff _).mp h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h1
      have h2 : (toMat K).symm (Multiplicative.toAdd (ψ u)) = 0 :=
        Multiplicative.ofAdd.injective h1
      have h3 : Multiplicative.toAdd (ψ u) = 0 := (toMat K).symm.map_eq_zero_iff.mp h2
      have h4 : ψ u = 1 := Multiplicative.toAdd.injective h3
      rw [Subgroup.mem_bot]
      exact (map_eq_one_iff ψ ψ.injective).mp h4
    · intro h
      rw [Subgroup.mem_bot] at h
      have hu1 : u = 1 := Subtype.ext h
      rw [hu1, map_one]
  · have hθm : θ u = m := by
      have h1 := QuotientGroup.eq.mp hβu
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h1
      have h1' : (θ u)⁻¹ * m = 1 := Subtype.ext h1
      exact inv_mul_eq_one.mp h1'
    show QuotientGroup.mk (θ _) = QuotientGroup.mk _
    congr 1
    apply Subtype.ext
    rw [← hθm]
    show Multiplicative.ofAdd ((toMat K).symm (Multiplicative.toAdd
      (ψ ((MulAut.congr ψ).symm (ι (Ψ K γ)) (u : W))))) =
        Multiplicative.ofAdd (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ
          Multiplicative.toAdd (Multiplicative.ofAdd ((toMat K).symm
            (Multiplicative.toAdd (ψ (u : W))))))
    rw [hΦsymm, toAdd_ofAdd]
    show Multiplicative.ofAdd ((toMat K).symm ((Ψ K γ) (Multiplicative.toAdd (ψ (u : W))))) = _
    rw [Ψ_apply, LinearEquiv.symm_apply_apply]

end Realization

section Main

theorem isNaturalO4Plus_of_isMatTensor2 {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (ht2 : orderOf t = 2)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hT : IsMatTensor2 L (L.map (MulAut.conj t).toMonoidHom) K)
    (hrk : rkIdx (fixV (Subgroup.zpowers t)) = n) :
    IsNaturalO4Plus (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t) n := by
  classical
  obtain ⟨φ₁, φ₂, ψ, h₁, h₂⟩ := hT
  have h2 : (2 : K) = 0 := by
    have h1 := congrArg (fun w => Multiplicative.toAdd (ψ w))
      (hW (ψ.symm (Multiplicative.ofAdd (1 : Mat K))))
    simp only [map_pow, MulEquiv.apply_symm_apply, toAdd_pow, toAdd_ofAdd, map_one,
      toAdd_one] at h1
    have h3 := congrFun (congrFun h1 0) 0
    simpa using h3
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have ht : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hΦapp : ∀ (a : MulAut W) (v : VM K), MulAut.congr ψ a v = ψ (a (ψ.symm v)) := fun a v => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hΦ₁ : ∀ (x : MulAut W) (hx : x ∈ L), MulAut.congr ψ x = rho (φ₁ ⟨x, hx⟩, 1) := by
    intro x hx
    refine eq_of_addMap fun X => ?_
    rw [addMap_rho, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
      addMap_apply, hΦapp]
    have := h₁ ⟨x, hx⟩ (ψ.symm (Multiplicative.ofAdd X))
    rwa [MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
  have hΦ₂ : ∀ (y : MulAut W) (hy : y ∈ L.map (MulAut.conj t).toMonoidHom),
      MulAut.congr ψ y = rho (1, φ₂ ⟨y, hy⟩) := by
    intro y hy
    refine eq_of_addMap fun X => ?_
    rw [addMap_rho, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, addMap_apply, hΦapp]
    have := h₂ ⟨y, hy⟩ (ψ.symm (Multiplicative.ofAdd X))
    rwa [MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
  have hΦ₁' : ∀ g, MulAut.congr ψ (φ₁.symm g : MulAut W) = rho (g, 1) := fun g => by
    rw [hΦ₁ _ (φ₁.symm g).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hΦ₂' : ∀ h, MulAut.congr ψ (φ₂.symm h : MulAut W) = rho (1, h) := fun h => by
    rw [hΦ₂ _ (φ₂.symm h).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hmapLL : (L ⊔ L.map (MulAut.conj t).toMonoidHom).map (MulAut.congr ψ).toMonoidHom =
      Lm K := by
    rw [Subgroup.map_sup]
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, (hΦ₁ x hx).symm⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (hΦ₂ y hy).symm⟩
    · rintro _ ⟨p, rfl⟩
      have hp : rho p = rho (p.1, 1) * rho (1, p.2) := by rw [rho_mul_mk, mul_one, one_mul]
      rw [hp, ← hΦ₁', ← hΦ₂']
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (φ₁.symm p.1).2))
        (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ (φ₂.symm p.2).2))
  have hconj : ∀ s ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom,
      t * s * t⁻¹ ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom := by
    have hle : (L ⊔ L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom ≤
        L ⊔ L.map (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.map_sup]
      refine sup_le le_sup_right ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine (le_sup_left : L ≤ _) ?_
      have e : (MulAut.conj t).toMonoidHom ((MulAut.conj t).toMonoidHom x) = x := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, htinv]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [ht, one_mul, mul_one]
      rw [e]
      exact hx
    intro s hs
    exact hle ⟨s, hs, rfl⟩
  set t' := MulAut.congr ψ t with ht'
  have ht't' : t' * t' = 1 := by rw [ht', ← map_mul, ht, map_one]
  have hfwd : ∀ h ∈ Lm K, t' * h * t'⁻¹ ∈ Lm K := by
    intro h hh
    rw [← hmapLL] at hh ⊢
    obtain ⟨s, hs, rfl⟩ := hh
    refine ⟨t * s * t⁻¹, hconj s hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, ht']
  have hN : t' ∈ NLm K := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have e : t' * (t' * h * t'⁻¹) * t'⁻¹ = h := by
      calc t' * (t' * h * t'⁻¹) * t'⁻¹ = (t' * t') * h * (t' * t')⁻¹ := by group
        _ = h := by rw [ht't', one_mul, inv_one, mul_one]
    rw [← e]
    exact hfwd _ hh
  have hnot : t' ∉ Lm K := by
    rintro ⟨⟨P₀, Q₀⟩, hPQ⟩
    have hg : uu (1 : K) ≠ 1 := fun h => one_ne_zero (uu_injective (h.trans uu_zero.symm))
    have e1 := hΦ₂ _ (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom (φ₁.symm (uu 1)).2)
    have e2 : MulAut.congr ψ ((MulAut.conj t).toMonoidHom (φ₁.symm (uu 1) : MulAut W)) =
        rho (P₀ * uu 1 * P₀⁻¹, Q₀ * 1 * Q₀⁻¹) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, ← ht', ← hPQ,
        hΦ₁', ← map_inv, rho_mul_mk, Prod.inv_mk, rho_mul_mk]
    have e3 := rho_injective (e2.symm.trans e1)
    have e4 : P₀ * uu 1 * P₀⁻¹ = 1 := congrArg Prod.fst e3
    apply hg
    calc uu (1 : K) = P₀⁻¹ * (P₀ * uu 1 * P₀⁻¹) * P₀ := by group
      _ = 1 := by rw [e4, mul_one, inv_mul_cancel]
  have hzp : Subgroup.zpowers t' = (Subgroup.zpowers t).map (MulAut.congr ψ).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hrk' : rkIdx (fixV (Subgroup.zpowers t')) = n := by
    rw [← hrk]
    unfold rkIdx
    rw [hzp, fixV_map_congr_equiv, Subgroup.index_map_of_bijective ψ.bijective]
  obtain ⟨P, Q, hPQ⟩ := w4t_o4_swap_form hK hn hN ht't' hnot hrk'
  have hRmap : (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t).map
      (MulAut.congr ψ).toMonoidHom = Lm K ⊔ Subgroup.zpowers t' := by
    rw [Subgroup.map_sup, hmapLL, hzp]
  refine ⟨K, inferInstance, inferInstance, hK, w4t_o4_realizes ψ fun r => ?_⟩
  rw [← w4t_o4_mem_sup_iff hPQ, ← hRmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end Main

end CFSG.LocalAnalysis.WeakClosure81
