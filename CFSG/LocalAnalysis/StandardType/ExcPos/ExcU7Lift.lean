module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7Frame
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7TvSwapped
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7TvFixed
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7TvCentral

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.StandardType.LieKnownR2.ExcPos.ExcU7
open scoped MatrixGroups

private theorem u7lift_sq_eq_one_of_sqzero {L : Type} [Field L] [CharP L 2] {ν : ℕ}
    {X : SL(ν, L)} (hX : ((X : Matrix (Fin ν) (Fin ν) L) - 1) ^ 2 = 0) : X ^ 2 = 1 := by
  apply Subtype.ext
  have h := hX
  rw [pow_two] at h ⊢
  calc (X : Matrix (Fin ν) (Fin ν) L) * (X : Matrix (Fin ν) (Fin ν) L)
      = ((X : Matrix (Fin ν) (Fin ν) L) - 1 + 1) *
          ((X : Matrix (Fin ν) (Fin ν) L) - 1 + 1) := by rw [sub_add_cancel]
    _ = ((X : Matrix (Fin ν) (Fin ν) L) - 1) * ((X : Matrix (Fin ν) (Fin ν) L) - 1) +
          ((X : Matrix (Fin ν) (Fin ν) L) - 1) + ((X : Matrix (Fin ν) (Fin ν) L) - 1) + 1 := by
        noncomm_ring
    _ = 0 + ((X : Matrix (Fin ν) (Fin ν) L) - 1) +
          ((X : Matrix (Fin ν) (Fin ν) L) - 1) + 1 := by rw [h]
    _ = 1 := by
        have h2 : ((X : Matrix (Fin ν) (Fin ν) L) - 1) +
            ((X : Matrix (Fin ν) (Fin ν) L) - 1) = 0 := by
          ext i j
          exact CharTwo.add_self_eq_zero _
        rw [zero_add, h2, zero_add]

theorem u7lift_eq_of_map_eq {L : Type} [Field L] [CharP L 2] {ν : ℕ} {G : Type*} [Group G]
    (g : SL(ν, L) →* G) (hker : g.ker ≤ Subgroup.center SL(ν, L)) (hν : 1 ≤ ν)
    {x y : SL(ν, L)} (hx : ((x : Matrix (Fin ν) (Fin ν) L) - 1) ^ 2 = 0)
    (hy : ((y : Matrix (Fin ν) (Fin ν) L) - 1) ^ 2 = 0) (hxy : g x = g y) : x = y := by
  haveI : Nonempty (Fin ν) := ⟨⟨0, hν⟩⟩
  have hmem : x * y⁻¹ ∈ g.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have hc : x * y⁻¹ ∈ Subgroup.center SL(ν, L) := hker hmem
  have hx2 : x ^ 2 = 1 := u7lift_sq_eq_one_of_sqzero hx
  have hy2 : y ^ 2 = 1 := u7lift_sq_eq_one_of_sqzero hy
  have hxy' : x = (x * y⁻¹) * y := by group
  have hcomm : Commute (x * y⁻¹) y := (Subgroup.mem_center_iff.1 hc y).symm
  have hc2 : (x * y⁻¹) ^ 2 = 1 := by
    have h1 : ((x * y⁻¹) * y) ^ 2 = 1 := by rw [← hxy']; exact hx2
    rw [hcomm.mul_pow 2, hy2, mul_one] at h1
    exact h1
  obtain ⟨r, _hrpow, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hr2 : r ^ 2 = 1 := by
    have hmat : ((x * y⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) ^ 2 = 1 := by
      have := congrArg (fun A : SL(ν, L) => (A : Matrix (Fin ν) (Fin ν) L)) hc2
      simpa using this
    have h2 : (Matrix.scalar (Fin ν) r) ^ 2 = 1 := by rw [hr, hmat]
    rw [← map_pow, ← map_one (Matrix.scalar (Fin ν))] at h2
    exact Matrix.scalar_inj.mp h2
  have hr1 : r = 1 := by
    have : r ^ 2 = (1 : L) ^ 2 := by rw [hr2, one_pow]
    exact CharTwo.sq_inj.mp this
  have hc1 : x * y⁻¹ = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  rw [hxy', hc1, one_mul]

theorem u7lift_commute_of_map_commute {L : Type} [Field L] [CharP L 2] {ν : ℕ} {G : Type*}
    [Group G] (g : SL(ν, L) →* G) (hker : g.ker ≤ Subgroup.center SL(ν, L)) (hν : 1 ≤ ν)
    {x y : SL(ν, L)} (hy : y ^ 2 = 1) (hc : g x * g y = g y * g x) : x * y = y * x := by
  haveI : Nonempty (Fin ν) := ⟨⟨0, hν⟩⟩
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ g.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hcen : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center SL(ν, L) := hker hmem
  have hcomm : Commute (x * y * x⁻¹ * y⁻¹) y := (Subgroup.mem_center_iff.1 hcen y).symm
  have hcy : (x * y * x⁻¹ * y⁻¹) * y = x * y * x⁻¹ := by group
  have hsq : ((x * y * x⁻¹ * y⁻¹) * y) ^ 2 = 1 := by
    rw [hcy, pow_two]
    calc (x * y * x⁻¹) * (x * y * x⁻¹)
        = x * (y * y) * x⁻¹ := by group
      _ = x * 1 * x⁻¹ := by rw [show y * y = 1 from (pow_two y).symm.trans hy]
      _ = 1 := by group
  have hc2 : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
    rw [hcomm.mul_pow 2, hy, mul_one] at hsq
    exact hsq
  obtain ⟨r, _hrpow, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  have hr2 : r ^ 2 = 1 := by
    have hmat : ((x * y * x⁻¹ * y⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) ^ 2 = 1 := by
      have := congrArg (fun A : SL(ν, L) => (A : Matrix (Fin ν) (Fin ν) L)) hc2
      simpa using this
    have h2 : (Matrix.scalar (Fin ν) r) ^ 2 = 1 := by rw [hr, hmat]
    rw [← map_pow, ← map_one (Matrix.scalar (Fin ν))] at h2
    exact Matrix.scalar_inj.mp h2
  have hr1 : r = 1 := by
    have : r ^ 2 = (1 : L) ^ 2 := by rw [hr2, one_pow]
    exact CharTwo.sq_inj.mp this
  have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  have h1 : x * y * x⁻¹ = y := mul_inv_eq_one.mp hc1
  have h2 : x * y = y * x := by
    have := congrArg (fun z => z * x) h1
    simpa [mul_assoc] using this
  exact h2


theorem excSwappedZ_lift {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀) (a : Fin Tag.E6.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (f : ℕ) {σQ : GGL ≃+* GGL}
    {ψ : SL(6, GGL) →* ModGL Tag.E6 GGL} {σf : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ}
    {z : ModGL Tag.E6 GGL} (hfrob : ∀ c, σQ c = c ^ 2 ^ f) (hf1 : 1 ≤ f) (hψ : IsSLFrame ψ σf)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σf)
    (hz : z ∈ torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots (rootCharHom a)))
    (hequiv : ∀ X : SL(6, GGL),
      S.D.step (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹)
    (hker : ψ.ker ≤ Subgroup.center SL(6, GGL))
    (hconj : ∀ u ∈ torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots (rootCharHom a)),
      ∃ M : GL (Fin 6) GGL, ∀ X : SL(6, GGL),
        u * ((MulAut.conj z).toMonoidHom.comp ψ) X * u⁻¹ =
          ((MulAut.conj z).toMonoidHom.comp ψ) (conjSLn M X))
    {A : Subgroup (ModGL Tag.E6 GGL)} (hA : ExcSwappedZ S a i f A) :
    ∃ T : Subgroup SL(6, GGL), IsTvGroup T ∧ IsSwappedTv (stdUnitary σQ.toRingHom) T ∧
      A = (((T ⊔ T.map (stdUnitary σQ.toRingHom)) ⊓
        (stdUnitary σQ.toRingHom).eqLocus (MonoidHom.id SL(6, GGL))).map
          ((MulAut.conj z).toMonoidHom.comp ψ)) := by
  classical
  let Φ : SL(6, GGL) →* SL(6, GGL) := stdUnitary σQ.toRingHom
  let ψ' : SL(6, GGL) →* ModGL Tag.E6 GGL := (MulAut.conj z).toMonoidHom.comp ψ
  have hFψ' : ∀ X : SL(6, GGL), S.D.step (ψ' X) = ψ' (Φ X) := fun X => hequiv X
  have hmap_dot : ∀ (v w : Fin 6 → GGL),
      (fun i => σQ (v i)) ⬝ᵥ (fun i => σQ (w i)) = σQ (v ⬝ᵥ w) := by
    intro v w
    simp only [dotProduct, ← map_mul, ← map_sum]
  have hker' : ψ'.ker ≤ Subgroup.center SL(6, GGL) := by
    intro X hX
    apply hker
    rw [MonoidHom.mem_ker] at hX ⊢
    have h : z * ψ X * z⁻¹ = 1 := hX
    have h' : z⁻¹ * (z * ψ X * z⁻¹) * z = 1 := by rw [h, mul_one, inv_mul_cancel]
    have : z⁻¹ * (z * ψ X * z⁻¹) * z = ψ X := by group
    rwa [this] at h'
  obtain ⟨hAcard, hAΓ, α, w, hα, hw, hstab, hcomm, hAle⟩ := hA
  have hα' : α ∈ frameRoots σf := by rw [← hΨ]; exact hα
  obtain ⟨x, y, hxy, hαeq⟩ := hα'
  obtain ⟨ε, hε⟩ := hψ.transv x y hxy
  have hdot_single : (Pi.single y (1 : GGL)) ⬝ᵥ (Pi.single x (1 : GGL)) = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hxy.symm]
  have hroot : rootSubgroup Tag.E6 GGL α =
      (tvGroup (Pi.single x (1 : GGL)) (Pi.single y (1 : GGL))).map ψ := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_map]
      rw [mem_rootSubgroup] at hg
      obtain ⟨c, hc⟩ := hg
      refine ⟨Matrix.SpecialLinearGroup.transvection hxy (ε⁻¹ * c), ?_, ?_⟩
      · rw [mem_tvGroup_single hxy]
        exact ⟨ε⁻¹ * c, rfl⟩
      · rw [hε (ε⁻¹ * c), ← hc, hαeq]
        congr 1
        show (ε : GGL) * (((ε⁻¹ : GGLˣ) : GGL) * c) = c
        rw [← mul_assoc, show (ε : GGL) * ((ε⁻¹ : GGLˣ) : GGL) = 1 by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_mul]
    · intro g hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨X, hX, rfl⟩ := hg
      rw [mem_tvGroup_single hxy] at hX
      obtain ⟨t, rfl⟩ := hX
      rw [hε t, mem_rootSubgroup]
      exact ⟨ε * t, by rw [hαeq]⟩
  set V : Subgroup (ModGL Tag.E6 GGL) := excCurve α w with hV
  set u : ModGL Tag.E6 GGL := w * z⁻¹ with hu_def
  have hu : u ∈ torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots (rootCharHom a)) :=
    mul_mem hw (inv_mem hz)
  obtain ⟨M, hM⟩ := hconj u hu
  have hconjψ : ∀ X : SL(6, GGL), w * ψ X * w⁻¹ = ψ' (conjSLn M X) := by
    intro X
    have h1 : w * ψ X * w⁻¹ = u * ψ' X * u⁻¹ := by
      rw [hu_def]
      show w * ψ X * w⁻¹ = (w * z⁻¹) * (z * ψ X * z⁻¹) * (w * z⁻¹)⁻¹
      group
    rw [h1, hM X]
  set T : Subgroup SL(6, GGL) :=
    (tvGroup (Pi.single x (1 : GGL)) (Pi.single y (1 : GGL))).map (conjSLn M) with hT
  have hcurve : V = T.map ψ' := by
    have hfun : (MulAut.conj w).toMonoidHom.comp ψ = ψ'.comp (conjSLn M) :=
      MonoidHom.ext hconjψ
    rw [hV, hT]
    show (rootSubgroup Tag.E6 GGL α).map (MulAut.conj w).toMonoidHom =
      ((tvGroup (Pi.single x (1 : GGL)) (Pi.single y (1 : GGL))).map (conjSLn M)).map ψ'
    rw [hroot, Subgroup.map_map, Subgroup.map_map, ← hfun]
  have hsqzero : ∀ {v φ : Fin 6 → GGL} (h : φ ⬝ᵥ v = 0) {X : SL(6, GGL)},
      X ∈ tvGroup v φ → ((X : Matrix (Fin 6) (Fin 6) GGL) - 1) ^ 2 = 0 := by
    intro v φ h X hX
    obtain ⟨t, ht⟩ := (mem_tvGroup_iff h).mp hX
    have hN : Matrix.vecMulVec v φ * Matrix.vecMulVec v φ = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]
    have hsub : (tvMat v φ t : Matrix (Fin 6) (Fin 6) GGL) - 1 = t • Matrix.vecMulVec v φ := by
      rw [tvMat]; abel
    rw [ht, hsub, pow_two, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, smul_zero]
  have hψ'inj2 : ∀ {v φ v' φ' : Fin 6 → GGL} (h : φ ⬝ᵥ v = 0) (h' : φ' ⬝ᵥ v' = 0)
      {X Y : SL(6, GGL)}, X ∈ tvGroup v φ → Y ∈ tvGroup v' φ' → ψ' X = ψ' Y → X = Y := by
    intro v φ v' φ' h h' X Y hX hY heq
    exact u7lift_eq_of_map_eq ψ' hker' (by norm_num : 1 ≤ 6)
      (hsqzero h hX) (hsqzero h' hY) heq
  have hmap_inj : ∀ {T₁ T₂ : Subgroup SL(6, GGL)}, IsTvGroup T₁ → IsTvGroup T₂ →
      T₁.map ψ' = T₂.map ψ' → T₁ = T₂ := by
    intro T₁ T₂ hT₁ hT₂ heq
    obtain ⟨v₁, φ₁, _hv₁, _hφ₁, hdot₁, rfl⟩ := hT₁
    obtain ⟨v₂, φ₂, _hv₂, _hφ₂, hdot₂, rfl⟩ := hT₂
    apply le_antisymm
    · intro X hX
      have hX' : ψ' X ∈ (tvGroup v₂ φ₂).map ψ' := by
        rw [← heq]; exact ⟨X, hX, rfl⟩
      rw [Subgroup.mem_map] at hX'
      obtain ⟨Y, hY, hYX⟩ := hX'
      rw [hψ'inj2 hdot₁ hdot₂ hX hY hYX.symm]
      exact hY
    · intro X hX
      have hX' : ψ' X ∈ (tvGroup v₁ φ₁).map ψ' := by
        rw [heq]; exact ⟨X, hX, rfl⟩
      rw [Subgroup.mem_map] at hX'
      obtain ⟨Y, hY, hYX⟩ := hX'
      rw [hψ'inj2 hdot₂ hdot₁ hX hY hYX.symm]
      exact hY
  have hT_tv : T = tvGroup ((M : Matrix (Fin 6) (Fin 6) GGL).mulVec (Pi.single x (1 : GGL)))
      (Matrix.vecMul (Pi.single y (1 : GGL))
        ((M⁻¹ : GL (Fin 6) GGL) : Matrix (Fin 6) (Fin 6) GGL)) := by
    rw [hT]
    exact tvGroup_map_conjSLn hdot_single M
  have hIsTv : IsTvGroup T := by
    refine ⟨_, _, ?_, ?_, ?_, hT_tv⟩
    · intro h0
      have h1 : ((M⁻¹ : GL (Fin 6) GGL) : Matrix (Fin 6) (Fin 6) GGL).mulVec
          ((M : Matrix (Fin 6) (Fin 6) GGL).mulVec (Pi.single x (1 : GGL))) = 0 := by
        rw [h0, Matrix.mulVec_zero]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h1
      have h2 := congrFun h1 x
      rw [Pi.single_eq_same] at h2
      exact one_ne_zero h2
    · intro h0
      have h1 : Matrix.vecMul (Matrix.vecMul (Pi.single y (1 : GGL))
          ((M⁻¹ : GL (Fin 6) GGL) : Matrix (Fin 6) (Fin 6) GGL))
          ((M : GL (Fin 6) GGL) : Matrix (Fin 6) (Fin 6) GGL) = 0 := by
        rw [h0, Matrix.zero_vecMul]
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.vecMul_one] at h1
      have h2 := congrFun h1 y
      rw [Pi.single_eq_same] at h2
      exact one_ne_zero h2
    · rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.vecMul_one]
      exact hdot_single
  have hIsTv_map : ∀ {T : Subgroup SL(6, GGL)}, IsTvGroup T → IsTvGroup (T.map Φ) := by
    intro T hT
    obtain ⟨v, φ, hv, hφ, hdot, rfl⟩ := hT
    refine ⟨fun i => σQ (φ i), fun i => σQ (v i), ?_, ?_, ?_, ?_⟩
    · intro h; apply hφ; funext i; exact σQ.injective (by simpa using congrFun h i)
    · intro h; apply hv; funext i; exact σQ.injective (by simpa using congrFun h i)
    · rw [hmap_dot v φ, dotProduct_comm, hdot, map_zero]
    · rw [tvGroup_map_stdUnitary hdot σQ]
  have hIsTv_Φ : IsTvGroup (T.map Φ) := hIsTv_map hIsTv
  have hIsTv_ΦΦ : IsTvGroup ((T.map Φ).map Φ) := hIsTv_map hIsTv_Φ
  have hFcomp : S.D.step.comp ψ' = ψ'.comp Φ := MonoidHom.ext hFψ'
  have hFV : V.map S.D.step = (T.map Φ).map ψ' := by
    rw [hcurve]
    calc (T.map ψ').map S.D.step = T.map (S.D.step.comp ψ') :=
          Subgroup.map_map T S.D.step ψ'
      _ = T.map (ψ'.comp Φ) := by rw [hFcomp]
      _ = (T.map Φ).map ψ' := (Subgroup.map_map T ψ' Φ).symm
  have hsw1 : (T.map Φ).map Φ = T := by
    have h2 : ((T.map Φ).map Φ).map ψ' = T.map ψ' := by
      have h3 : (V.map S.D.step).map S.D.step = V := hstab
      rw [hFV] at h3
      rw [Subgroup.map_map (T.map Φ) S.D.step ψ'] at h3
      rw [hFcomp] at h3
      rw [← Subgroup.map_map (T.map Φ) ψ' Φ] at h3
      rw [hcurve] at h3
      exact h3
    exact hmap_inj hIsTv_ΦΦ hIsTv h2
  have hIsTv' : IsTvGroup T := hIsTv
  obtain ⟨v, φ, hv, hφ, hdot, hT_eq⟩ := hIsTv
  have hdotΦ : (fun i => σQ (v i)) ⬝ᵥ (fun i => σQ (φ i)) = 0 := by
    rw [hmap_dot v φ, dotProduct_comm, hdot, map_zero]
  have hTmapΦ : T.map Φ = tvGroup (fun i => σQ (φ i)) (fun i => σQ (v i)) := by
    rw [hT_eq, tvGroup_map_stdUnitary hdot σQ]
  have hsw2 : ∀ x ∈ T, ∀ y ∈ T.map Φ, x * y = y * x := by
    intro x hx y hy
    have hxV : ψ' x ∈ V := by rw [hcurve]; exact ⟨x, hx, rfl⟩
    have hyVF : ψ' y ∈ V.map S.D.step := by rw [hFV]; exact ⟨y, hy, rfl⟩
    have hcomm' : ψ' x * ψ' y = ψ' y * ψ' x := hcomm _ hxV _ hyVF
    have hy' : y ∈ tvGroup (fun i => σQ (φ i)) (fun i => σQ (v i)) := by
      rw [← hTmapΦ]; exact hy
    have hy2 : y ^ 2 = 1 := u7lift_sq_eq_one_of_sqzero (hsqzero hdotΦ hy')
    exact u7lift_commute_of_map_commute ψ' hker' (by norm_num : 1 ≤ 6) hy2 hcomm'
  have hΓ : S.Γ ≤ S.D.model := by
    show ⁅S.D.model, S.D.model⁆ ≤ S.D.model
    exact Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
      S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.mul_mem h₁ h₂) (S.D.model.inv_mem h₁))
        (S.D.model.inv_mem h₂)
  have h2f : 2 ≤ 2 ^ f := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf1
    simpa using h
  have hsw3 : T ≠ T.map Φ := by
    intro hEq
    have hVF : V.map S.D.step = V := by rw [hFV, ← hEq, ← hcurve]
    have hAleV : A ≤ V := by
      have h := hAle
      rw [hVF, sup_idem] at h
      exact h
    have hAleFix : A ≤ (T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ' := by
      intro a ha
      rw [Subgroup.mem_map]
      have haV : a ∈ V := hAleV ha
      rw [hcurve] at haV
      rw [Subgroup.mem_map] at haV
      obtain ⟨b, hb, hba⟩ := haV
      refine ⟨b, ?_, hba⟩
      rw [Subgroup.mem_inf]
      refine ⟨hb, ?_⟩
      show Φ b = b
      have hFa : S.D.step a = a := ((LangDatum.mem_model S.D).1 (hΓ (hAΓ ha))).2
      have hFa' : ψ' (Φ b) = ψ' b := by
        have h := hFa
        rw [← hba, hFψ' b] at h
        exact h
      have hΦb : Φ b ∈ T ⊔ T.map Φ := by
        have h1 : Φ b ∈ (T ⊔ T.map Φ).map Φ :=
          Subgroup.mem_map_of_mem Φ (Subgroup.mem_sup_left hb)
        rwa [Subgroup.map_sup, hsw1, sup_comm] at h1
      have hc_mem : b⁻¹ * Φ b ∈ T ⊔ T.map Φ :=
        mul_mem (inv_mem (Subgroup.mem_sup_left hb)) hΦb
      have hc_ker : b⁻¹ * Φ b ∈ ψ'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hFa', inv_mul_cancel]
      have hc_center : b⁻¹ * Φ b ∈ Subgroup.center SL(6, GGL) := hker' hc_ker
      have hc_eq : b⁻¹ * Φ b = 1 := by
        rw [hTmapΦ, hT_eq] at hc_mem
        exact eq_one_of_mem_sup_of_mem_center (by norm_num : 2 ≤ 6) hdot hdotΦ
          (by rw [← hT_eq, ← hTmapΦ]; exact hsw2) hc_mem hc_center
      have hΦbb : Φ b = b := by
        have h : b⁻¹ * Φ b = b⁻¹ * b := by rw [hc_eq, inv_mul_cancel]
        exact mul_left_cancel h
      exact hΦbb
    have hst : (tvGroup v φ).map Φ = tvGroup v φ := by rw [← hT_eq]; exact hEq.symm
    have hcard_fix : Nat.card ↥(T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) ≤ 2 ^ f := by
      have h := (card_fixed_stable_le σQ hfrob h2f hv hφ hdot hst).2
      rwa [← hT_eq] at h
    have hcard_map : Nat.card ↥((T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ') ≤
        Nat.card ↥(T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) := by
      rw [hT_eq]
      haveI : Finite ↥(tvGroup v φ ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) :=
        (card_fixed_stable_le σQ hfrob h2f hv hφ hdot hst).1
      have hsurj : Function.Surjective
          (fun x : ↥(tvGroup v φ ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) =>
            (⟨ψ' x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
              ↥((tvGroup v φ ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ'))) := by
        intro y
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
      exact Nat.card_le_card_of_surjective _ hsurj
    have hfin_fix : Finite ↥(T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) := by
      rw [hT_eq]
      exact (card_fixed_stable_le σQ hfrob h2f hv hφ hdot hst).1
    have hfin_fix_map : Finite ↥((T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ') := by
      haveI := hfin_fix
      exact Finite.of_surjective
        (fun x : ↥(T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) =>
          (⟨ψ' x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
            ↥((T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ')))
        (by intro y; obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
            exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
    have hle_card : Nat.card ↥A ≤ Nat.card ↥(T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) := by
      haveI := hfin_fix_map
      calc Nat.card ↥A ≤ Nat.card ↥((T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ') :=
            Subgroup.card_le_of_le hAleFix
        _ ≤ Nat.card ↥(T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) := hcard_map
    have hle : (2 ^ f) ^ 2 ≤ 2 ^ f := by
      calc (2 ^ f) ^ 2 = Nat.card ↥A := hAcard.symm
        _ ≤ Nat.card ↥(T ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) := hle_card
        _ ≤ 2 ^ f := hcard_fix
    have hlt : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith [h2f]
    exact absurd hle (not_le.mpr hlt)
  have hsw : IsSwappedTv Φ T := ⟨hsw1, hsw2, hsw3⟩
  obtain ⟨v₀, φ₀, hv₀, hφ₀, hv₀ne, hφ₀ne, hdot₀, hT_eq₀⟩ :=
    exists_rational_of_stable σQ hIsTv' hsw1
  have hdotΦ₀ : (fun i => σQ (v₀ i)) ⬝ᵥ (fun i => σQ (φ₀ i)) = 0 := by
    rw [hmap_dot v₀ φ₀, dotProduct_comm, hdot₀, map_zero]
  have hTmapΦ₀ : T.map Φ = tvGroup (fun i => σQ (φ₀ i)) (fun i => σQ (v₀ i)) := by
    rw [hT_eq₀, tvGroup_map_stdUnitary hdot₀ σQ]
  have hsw' : IsSwappedTv Φ (tvGroup v₀ φ₀) := by rwa [← hT_eq₀]
  have hcard_Ã : Nat.card ↥((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) ≤
      (2 ^ f) ^ 2 := by
    have h := (card_fixed_swapped_le σQ hfrob h2f hv₀ hφ₀ hv₀ne hφ₀ne hdot₀ hsw').2
    rw [tvGroup_map_stdUnitary hdot₀ σQ] at h
    rwa [hTmapΦ₀, hT_eq₀]
  have hfin_Ã : Finite ↥((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) := by
    have h := (card_fixed_swapped_le σQ hfrob h2f hv₀ hφ₀ hv₀ne hφ₀ne hdot₀ hsw').1
    rw [tvGroup_map_stdUnitary hdot₀ σQ] at h
    rwa [hTmapΦ₀, hT_eq₀]
  have hAle' : A ≤ ((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ' := by
    intro a ha
    have haV : a ∈ V ⊔ V.map S.D.step := hAle ha
    rw [hFV, hcurve, ← Subgroup.map_sup] at haV
    rw [Subgroup.mem_map] at haV
    obtain ⟨b, hb, hba⟩ := haV
    refine Subgroup.mem_map.mpr ⟨b, ?_, hba⟩
    rw [Subgroup.mem_inf]
    refine ⟨hb, ?_⟩
    show Φ b = b
    have hFa : S.D.step a = a := ((LangDatum.mem_model S.D).1 (hΓ (hAΓ ha))).2
    have hFa' : ψ' (Φ b) = ψ' b := by
      have h := hFa
      rw [← hba, hFψ' b] at h
      exact h
    have hΦb : Φ b ∈ T ⊔ T.map Φ := by
      have h1 : Φ b ∈ (T ⊔ T.map Φ).map Φ := Subgroup.mem_map_of_mem Φ hb
      rwa [Subgroup.map_sup, hsw1, sup_comm] at h1
    have hc_mem : b⁻¹ * Φ b ∈ T ⊔ T.map Φ := mul_mem (inv_mem hb) hΦb
    have hc_ker : b⁻¹ * Φ b ∈ ψ'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hFa', inv_mul_cancel]
    have hc_center : b⁻¹ * Φ b ∈ Subgroup.center SL(6, GGL) := hker' hc_ker
    have hc_eq : b⁻¹ * Φ b = 1 := by
      rw [hTmapΦ₀, hT_eq₀] at hc_mem
      exact eq_one_of_mem_sup_of_mem_center (by norm_num : 2 ≤ 6) hdot₀ hdotΦ₀
        (by rw [← hT_eq₀, ← hTmapΦ₀]; exact hsw.2.1) hc_mem hc_center
    have hΦbb : Φ b = b := by
      have h : b⁻¹ * Φ b = b⁻¹ * b := by rw [hc_eq, inv_mul_cancel]
      exact mul_left_cancel h
    exact hΦbb
  have hcard_Ãmap : Nat.card ↥(((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ') ≤
      Nat.card ↥((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) := by
    haveI := hfin_Ã
    have hsurj : Function.Surjective
        (fun x : ↥((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) =>
          (⟨ψ' x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
            ↥(((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ'))) := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact Nat.card_le_card_of_surjective _ hsurj
  have hcard_le : Nat.card ↥(((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ') ≤
      Nat.card ↥A := by
    rw [hAcard]
    exact le_trans hcard_Ãmap hcard_Ã
  have hfin_map : Finite ↥(((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ') := by
    haveI := hfin_Ã
    exact Finite.of_surjective
      (fun x : ↥((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))) =>
        (⟨ψ' x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥(((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(6, GGL))).map ψ')))
      (by intro y; obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
          exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
  haveI := hfin_map
  exact ⟨T, hIsTv', hsw, Subgroup.eq_of_le_of_card_ge hAle' hcard_le⟩

end CFSG.StandardType.LieKnownR2.ExcPos
