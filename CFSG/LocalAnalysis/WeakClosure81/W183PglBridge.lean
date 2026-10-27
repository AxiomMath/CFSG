module

public import CFSG.LocalAnalysis.WeakClosure81.W183PglExt
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModules
public import CFSG.Quasithin.Background.F6SQTK
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

@[expose] def W183PglAdj : Subgroup (Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
  MonoidHom.ker (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)).toMultiplicative

theorem w183Pgl_mem_adj {X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))} :
    X ∈ W183PglAdj ↔ Matrix.trace (Multiplicative.toAdd X) = 0 := by
  simp [W183PglAdj, MonoidHom.mem_ker]

theorem w183Pgl_equiv_L {W : Type} [Group W] (h : F6.IsL2 7 1 W) :
    Nonempty (W ≃* GL (Fin 3) (ZMod 2)) := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨e7⟩⟩ := h
  have hKF : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hKcard, pow_one]
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  obtain ⟨eGL⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨((e7.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))).trans eGL.symm⟩

@[expose] noncomputable def w183PglLin :
    GL (Fin 3) (ZMod 2) ≃* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem w183PglLin_apply (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    w183PglLin g v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v :=
  rfl

@[expose] def W183PglTraceZero : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) (ZMod 2) (ZMod 2))

theorem w183Pgl_dual_equiv :
    ∃ ψ : Module.Dual (ZMod 2) (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
      ∀ (g : GL (Fin 3) (ZMod 2)) (f : Module.Dual (ZMod 2) (Fin 3 → ZMod 2)),
        ψ (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.dualRep (Fin 3 → ZMod 2) (w183PglLin g)
            f) =
          ((w183PglTau g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ψ f := by
  let b := Pi.basisFun (ZMod 2) (Fin 3)
  refine ⟨b.dualBasis.equivFun, fun g f => ?_⟩
  have hψ : ∀ f : Module.Dual (ZMod 2) (Fin 3 → ZMod 2), ∀ i,
      b.dualBasis.equivFun f i = f (Pi.single i 1) := by
    intro f i
    simp [b]
  have hsingle : ∀ (x : Fin 3 → ZMod 2) (j : Fin 3),
      (Pi.single j (x j) : Fin 3 → ZMod 2) =
        x j • (Pi.single j (1 : ZMod 2) : Fin 3 → ZMod 2) := by
    intro x j
    ext k
    by_cases h : k = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  have hev : ∀ (f : Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) (x : Fin 3 → ZMod 2),
      f x = x ⬝ᵥ b.dualBasis.equivFun f := by
    intro f x
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp [map_sum, dotProduct, hψ, hsingle]
  have hsymm : ∀ x : Fin 3 → ZMod 2, (w183PglLin g).symm x =
      ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x := by
    intro x
    have h1 : (w183PglLin g).symm = w183PglLin g⁻¹ := by
      ext y
      simp
    rw [h1, w183PglLin_apply]
  ext i
  rw [hψ, Matrix.GeneralLinearGroup.coe_inverseTranspose]
  change f ((w183PglLin g).symm (Pi.single i 1)) = _
  rw [hsymm, hev f]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem w183Pgl_adj_equiv :
    ∃ ψ : CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZeroEnd (Fin 3 → ZMod 2) ≃ₗ[ZMod 2]
        W183PglTraceZero,
      ∀ (g : GL (Fin 3) (ZMod 2))
        (X : CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZeroEnd (Fin 3 → ZMod 2)),
        ((ψ (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.adjRep (Fin 3 → ZMod 2)
            (w183PglLin g) X) : W183PglTraceZero) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((ψ X : W183PglTraceZero) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
              ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  let T : ((Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃ₗ[ZMod 2]
      Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix'
  have htr : ∀ X : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2),
      LinearMap.trace (ZMod 2) (Fin 3 → ZMod 2) X = Matrix.trace (T X) := by
    intro X
    rw [LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 3)),
      LinearMap.toMatrix_eq_toMatrix']
  have hmap : (traceZeroEnd (Fin 3 → ZMod 2)).map T.toLinearMap = W183PglTraceZero := by
    ext M
    simp only [Submodule.mem_map, W183PglTraceZero, LinearMap.mem_ker, traceZeroEnd]
    constructor
    · rintro ⟨X, hX, rfl⟩
      change Matrix.trace (T X) = 0
      rw [← htr]
      exact hX
    · intro hM
      refine ⟨T.symm M, ?_, T.apply_symm_apply M⟩
      rw [htr, T.apply_symm_apply]
      exact hM
  refine ⟨LinearEquiv.ofSubmodules T _ _ hmap, fun g X => ?_⟩
  have hT : ∀ h : GL (Fin 3) (ZMod 2),
      T ((w183PglLin h : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
        (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) =
          (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro h
    have : ((w183PglLin h : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
        (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) =
          Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      ext v
      simp [w183PglLin_apply]
    rw [this]
    exact LinearMap.toMatrix'_toLin' _
  have hsymm : (w183PglLin g).symm = w183PglLin g⁻¹ := by
    ext y
    simp
  have hadj := adjRep_apply (w183PglLin g) X
  change T ((adjRep (Fin 3 → ZMod 2) (w183PglLin g) X : traceZeroEnd (Fin 3 → ZMod 2)) :
      Module.End (ZMod 2) (Fin 3 → ZMod 2)) = _ * T (X : Module.End (ZMod 2) (Fin 3 → ZMod 2)) * _
  rw [hadj]
  change LinearMap.toMatrix' _ = _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp]
  have h1 := hT g
  have h2 := hT g⁻¹
  rw [← hsymm] at h2
  change LinearMap.toMatrix' _ = _ at h1
  change LinearMap.toMatrix' _ = _ at h2
  rw [h1, h2, Matrix.mul_assoc]

theorem w183Pgl_classify_additive {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (σ : GL (Fin 3) (ZMod 2) →* (E ≃ₗ[ZMod 2] E))
    (hnt : ∃ (g : GL (Fin 3) (ZMod 2)) (x : E), σ g x ≠ x)
    (hirr : ∀ N : Submodule (ZMod 2) E, (∀ (g : GL (Fin 3) (ZMod 2)), ∀ x ∈ N, σ g x ∈ N) →
      N = ⊥ ∨ N = ⊤) :
    (∃ φ : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), ∀ (g : GL (Fin 3) (ZMod 2)) (x : E),
        φ (σ g x) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ φ x) ∨
      (∃ φ : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), ∀ (g : GL (Fin 3) (ZMod 2)) (x : E),
        φ (σ g x) =
          ((w183PglTau g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ φ x) ∨
      (∃ φ : E ≃ₗ[ZMod 2] W183PglTraceZero, ∀ (g : GL (Fin 3) (ZMod 2)) (x : E),
        ((φ (σ g x) : W183PglTraceZero) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((φ x : W183PglTraceZero) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
              ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  classical
  let ρ : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) E :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp (σ.comp w183PglLin.symm.toMonoidHom)
  have hρ : ∀ (g : GL (Fin 3) (ZMod 2)) (x : E), ρ (w183PglLin g) x = σ g x := by
    intro g x
    simp [ρ]
  have hρirr : ρ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := fun N => ?_ }
    · obtain ⟨g, x, hx⟩ := hnt
      intro h
      have hx0 : x ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
      rw [← h] at hx0
      have hx1 : x = 0 := hx0
      apply hx
      rw [hx1, map_zero]
    · have hN := hirr N.toSubmodule (fun g x hx => by
        have := N.apply_mem_toSubmodule (w183PglLin g) hx
        rwa [hρ] at this)
      rcases hN with h | h
      · left
        exact Subrepresentation.ext h
      · right
        exact Subrepresentation.ext h
  haveI : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :=
    Module.finite_of_finite (ZMod 2)
  haveI : Fintype (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by simp
  rcases exists_equiv_model hfr ρ hρirr with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exfalso
    obtain ⟨g, x, hx⟩ := hnt
    have h := LinearMap.congr_fun (e.isIntertwining' (w183PglLin g)) x
    simp only [LinearMap.comp_apply] at h
    rw [hρ, trivRep_apply] at h
    exact hx (e.toLinearEquiv.injective h)
  · refine Or.inl ⟨e.toLinearEquiv, fun g x => ?_⟩
    have h := LinearMap.congr_fun (e.isIntertwining' (w183PglLin g)) x
    simp only [LinearMap.comp_apply] at h
    rw [hρ, natRep_apply, w183PglLin_apply] at h
    exact h
  · obtain ⟨ψ, hψ⟩ := w183Pgl_dual_equiv
    refine Or.inr (Or.inl ⟨e.toLinearEquiv.trans ψ, fun g x => ?_⟩)
    have h := LinearMap.congr_fun (e.isIntertwining' (w183PglLin g)) x
    simp only [LinearMap.comp_apply] at h
    rw [hρ] at h
    have h' : e.toLinearEquiv (σ g x) = dualRep (Fin 3 → ZMod 2) (w183PglLin g)
        (e.toLinearEquiv x) := h
    change ψ (e.toLinearEquiv (σ g x)) = _
    rw [h']
    exact hψ g _
  · obtain ⟨ψ, hψ⟩ := w183Pgl_adj_equiv
    refine Or.inr (Or.inr ⟨e.toLinearEquiv.trans ψ, fun g x => ?_⟩)
    have h := LinearMap.congr_fun (e.isIntertwining' (w183PglLin g)) x
    simp only [LinearMap.comp_apply] at h
    rw [hρ] at h
    have h' : e.toLinearEquiv (σ g x) = adjRep (Fin 3 → ZMod 2) (w183PglLin g)
        (e.toLinearEquiv x) := h
    change ((ψ (e.toLinearEquiv (σ g x)) : W183PglTraceZero) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
    rw [h']
    exact hψ g _

theorem w183Pgl_irreducible_classify {E : Type} [CommGroup E] [Finite E] (hE : ∀ x : E, x ^ 2 = 1)
    (σ : GL (Fin 3) (ZMod 2) →* MulAut E)
    (hnt : ∃ (g : GL (Fin 3) (ZMod 2)) (x : E), σ g x ≠ x)
    (hirr : ∀ J : Subgroup E, (∀ g, ∀ j ∈ J, σ g j ∈ J) → J = ⊥ ∨ J = ⊤) :
    (∃ φ : E ≃* W183PglVec, ∀ (g : GL (Fin 3) (ZMod 2)) (x : E),
        Multiplicative.toAdd (φ (σ g x)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (φ x)) ∨
      (∃ φ : E ≃* W183PglVec, ∀ (g : GL (Fin 3) (ZMod 2)) (x : E),
        Multiplicative.toAdd (φ (σ g x)) =
          ((w183PglTau g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (φ x)) ∨
      (∃ φ : E ≃* W183PglAdj, ∀ (g : GL (Fin 3) (ZMod 2)) (x : E),
        Multiplicative.toAdd (φ (σ g x) : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            Multiplicative.toAdd (φ x : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) *
              ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  classical
  haveI hmod : Module (ZMod 2) (Additive E) :=
    AddCommGroup.zmodModule (fun x => by
      rw [← ofMul_toMul x, ← ofMul_pow]
      simp [hE])
  have hsmul : ∀ (f : Additive E →+ Additive E) (c : ZMod 2) (x : Additive E),
      f (c • x) = c • f x := by
    intro f c x
    have hc : c = ((c.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val c).symm
    rw [hc, Nat.cast_smul_eq_nsmul (ZMod 2), Nat.cast_smul_eq_nsmul (ZMod 2), map_nsmul]
  let σl : GL (Fin 3) (ZMod 2) →* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun g =>
        { MulEquiv.toAdditive (σ g) with
          map_smul' := fun c x => hsmul (MulEquiv.toAdditive (σ g)).toAddMonoidHom c x }
      map_one' := by
        ext x
        simp
      map_mul' := fun g h => by
        ext x
        simp }
  have hσl : ∀ (g : GL (Fin 3) (ZMod 2)) (x : E),
      σl g (Additive.ofMul x) = Additive.ofMul (σ g x) := fun g x => rfl
  have hnt' : ∃ (g : GL (Fin 3) (ZMod 2)) (x : Additive E), σl g x ≠ x := by
    obtain ⟨g, x, hx⟩ := hnt
    refine ⟨g, Additive.ofMul x, fun h => hx ?_⟩
    rw [hσl] at h
    exact Additive.ofMul.injective h
  have hirr' : ∀ N : Submodule (ZMod 2) (Additive E), (∀ (g : GL (Fin 3) (ZMod 2)),
      ∀ x ∈ N, σl g x ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let J : Subgroup E := AddSubgroup.toSubgroup N.toAddSubgroup
    have hJ : ∀ g, ∀ j ∈ J, σ g j ∈ J := fun g j hj => hN g (Additive.ofMul j) hj
    rcases hirr J hJ with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hxJ : Additive.toMul x ∈ J := hx
      rw [h] at hxJ
      have h1 : Additive.toMul x = 1 := hxJ
      rw [Submodule.mem_bot]
      exact Additive.toMul.injective h1
    · right
      rw [eq_top_iff]
      intro x _
      have hxJ : Additive.toMul x ∈ J := by
        rw [h]
        exact Subgroup.mem_top _
      exact hxJ
  rcases w183Pgl_classify_additive σl hnt' hirr' with ⟨φ, hφ⟩ | ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · left
    refine ⟨AddEquiv.toMultiplicativeRight φ.toAddEquiv, fun g x => ?_⟩
    exact hφ g (Additive.ofMul x)
  · right
    left
    refine ⟨AddEquiv.toMultiplicativeRight φ.toAddEquiv, fun g x => ?_⟩
    exact hφ g (Additive.ofMul x)
  · right
    right
    have htz : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
        M ∈ W183PglTraceZero ↔ Matrix.trace M = 0 := by
      intro M
      simp [W183PglTraceZero, LinearMap.mem_ker]
    let ι : Multiplicative ↥W183PglTraceZero ≃* ↥W183PglAdj :=
      { toFun := fun v => ⟨Multiplicative.ofAdd ((Multiplicative.toAdd v : ↥W183PglTraceZero) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)),
          w183Pgl_mem_adj.2 ((htz _).1 (Multiplicative.toAdd v).2)⟩
        invFun := fun X => Multiplicative.ofAdd
          ⟨Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))),
            (htz _).2 (w183Pgl_mem_adj.1 X.2)⟩
        left_inv := fun v => rfl
        right_inv := fun X => rfl
        map_mul' := fun v w => rfl }
    refine ⟨(AddEquiv.toMultiplicativeRight φ.toAddEquiv).trans ι, fun g x => ?_⟩
    exact hφ g (Additive.ofMul x)

variable {I : Type} [CommGroup I]

private theorem w183Pgl_quot_action (σ : GL (Fin 3) (ZMod 2) →* MulAut I) :
    ∃ σb : GL (Fin 3) (ZMod 2) →* MulAut (I ⧸ W183PglFixed σ),
      ∀ (g : GL (Fin 3) (ZMod 2)) (i : I),
        σb g (QuotientGroup.mk i) = QuotientGroup.mk (σ g i) := by
  have hmap : ∀ g : GL (Fin 3) (ZMod 2),
      (W183PglFixed σ).map (σ g).toMonoidHom = W183PglFixed σ := fun g => by
    ext i
    constructor
    · rintro ⟨c, hc, rfl⟩
      change σ g c ∈ W183PglFixed σ
      have hc' : σ g c = c := hc g
      rw [hc']
      exact hc
    · intro hi
      exact ⟨i, hi, hi g⟩
  refine ⟨{ toFun := fun g => QuotientGroup.congr (W183PglFixed σ) (W183PglFixed σ) (σ g) (hmap g)
            map_one' := ?_
            map_mul' := ?_ }, fun g i => QuotientGroup.congr_mk _ _ (σ g) (hmap g) i⟩
  · refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H i => simp [QuotientGroup.congr_mk]
  · intro g h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H i =>
      have e1 := QuotientGroup.congr_mk (W183PglFixed σ) (W183PglFixed σ) (σ (g * h))
        (hmap (g * h)) i
      have e2 := QuotientGroup.congr_mk (W183PglFixed σ) (W183PglFixed σ) (σ h) (hmap h) i
      have e3 := QuotientGroup.congr_mk (W183PglFixed σ) (W183PglFixed σ) (σ g) (hmap g)
        ((σ h) i)
      change QuotientGroup.congr (W183PglFixed σ) (W183PglFixed σ) (σ (g * h)) (hmap (g * h))
          (QuotientGroup.mk i) =
        QuotientGroup.congr (W183PglFixed σ) (W183PglFixed σ) (σ g) (hmap g)
          (QuotientGroup.congr (W183PglFixed σ) (W183PglFixed σ) (σ h) (hmap h)
            (QuotientGroup.mk i))
      rw [e1, e2, e3, map_mul, MulAut.mul_apply]

theorem w183Pgl_top_classify [Finite I] (hI : ∀ x : I, x ^ 2 = 1)
    (σ : GL (Fin 3) (ZMod 2) →* MulAut I) (hnt : ∃ i : I, i ≠ 1)
    (hgen : ∀ i : I, i ∈ Subgroup.closure
      {x : I | ∃ (g : GL (Fin 3) (ZMod 2)) (j : I), x = σ g j * j⁻¹})
    (hirr : ∀ J : Subgroup I, (∀ g, ∀ j ∈ J, σ g j ∈ J) → W183PglFixed σ ≤ J →
      J = W183PglFixed σ ∨ J = ⊤) :
    (∃ π : I →* W183PglVec, Function.Surjective π ∧ (∀ i : I, π i = 1 → ∀ g, σ g i = i) ∧
        ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i)) ∨
      (∃ π : I →* W183PglVec, Function.Surjective π ∧ (∀ i : I, π i = 1 → ∀ g, σ g i = i) ∧
        ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
          ((w183PglTau g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (π i)) ∨
      (∃ π : I →* W183PglAdj, Function.Surjective π ∧ (∀ i : I, π i = 1 → ∀ g, σ g i = i) ∧
        ∀ (g : GL (Fin 3) (ZMod 2)) (i : I),
          Multiplicative.toAdd (π (σ g i) : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) =
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
              Multiplicative.toAdd (π i : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) *
                ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  obtain ⟨σb, hσb⟩ := w183Pgl_quot_action σ
  have hEexp : ∀ x : I ⧸ W183PglFixed σ, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H i => rw [← QuotientGroup.mk_pow, hI i]; rfl
  have hker : ∀ i : I, (QuotientGroup.mk i : I ⧸ W183PglFixed σ) = 1 → ∀ g, σ g i = i :=
    fun i hi => (QuotientGroup.eq_one_iff i).1 hi
  have hEnt : ∃ (g : GL (Fin 3) (ZMod 2)) (x : I ⧸ W183PglFixed σ), σb g x ≠ x := by
    by_contra hcon
    have htriv : ∀ (g : GL (Fin 3) (ZMod 2)) (x : I ⧸ W183PglFixed σ), σb g x = x :=
      fun g x => by
        by_contra h
        exact hcon ⟨g, x, h⟩
    have hcomm : ∀ (g : GL (Fin 3) (ZMod 2)) (j : I), σ g j * j⁻¹ ∈ W183PglFixed σ := by
      intro g j
      have h := htriv g (QuotientGroup.mk j)
      rw [hσb] at h
      have h' := (QuotientGroup.eq.1 h)
      have h3 : σ g j * j⁻¹ = ((σ g j)⁻¹ * j)⁻¹ := by
        rw [_root_.mul_inv_rev, inv_inv, mul_comm]
      rw [h3]
      exact (W183PglFixed σ).inv_mem h'
    have hfix : ∀ i : I, i ∈ W183PglFixed σ := fun i =>
      (Subgroup.closure_le _).2 (by rintro x ⟨g, j, rfl⟩; exact hcomm g j) (hgen i)
    obtain ⟨i, hi⟩ := hnt
    refine hi ((Subgroup.closure_le (⊥ : Subgroup I)).2 ?_ (hgen i))
    rintro x ⟨g, j, rfl⟩
    have := (hfix j) g
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hEirr : ∀ J : Subgroup (I ⧸ W183PglFixed σ),
      (∀ g, ∀ j ∈ J, σb g j ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hJ' : ∀ g, ∀ j ∈ J.comap (QuotientGroup.mk' (W183PglFixed σ)),
        σ g j ∈ J.comap (QuotientGroup.mk' (W183PglFixed σ)) := by
      intro g j hj
      simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hj ⊢
      rw [← hσb]
      exact hJ g _ hj
    have hCJ : W183PglFixed σ ≤ J.comap (QuotientGroup.mk' (W183PglFixed σ)) := by
      intro c hc
      simp only [Subgroup.mem_comap, QuotientGroup.mk'_apply]
      rw [(QuotientGroup.eq_one_iff c).2 hc]
      exact J.one_mem
    have hJeq := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (W183PglFixed σ)) J
    rcases hirr _ hJ' hCJ with h | h
    · left
      rw [← hJeq, h, QuotientGroup.map_mk'_self]
    · right
      rw [← hJeq, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rcases w183Pgl_irreducible_classify hEexp σb hEnt hEirr with ⟨φ, hφ⟩ | ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · refine Or.inl ⟨φ.toMonoidHom.comp (QuotientGroup.mk' (W183PglFixed σ)),
      φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
    · intro i hi
      exact hker i ((MulEquiv.map_eq_one_iff φ).1 hi)
    · intro g i
      change Multiplicative.toAdd (φ (QuotientGroup.mk (σ g i))) = _
      rw [← hσb, hφ]
      rfl
  · refine Or.inr (Or.inl ⟨φ.toMonoidHom.comp (QuotientGroup.mk' (W183PglFixed σ)),
      φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩)
    · intro i hi
      exact hker i ((MulEquiv.map_eq_one_iff φ).1 hi)
    · intro g i
      change Multiplicative.toAdd (φ (QuotientGroup.mk (σ g i))) = _
      rw [← hσb, hφ]
      rfl
  · refine Or.inr (Or.inr ⟨φ.toMonoidHom.comp (QuotientGroup.mk' (W183PglFixed σ)),
      φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩)
    · intro i hi
      exact hker i ((MulEquiv.map_eq_one_iff φ).1 hi)
    · intro g i
      change Multiplicative.toAdd (φ (QuotientGroup.mk (σ g i)) :
        Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) = _
      rw [← hσb, hφ]
      rfl

theorem w183Pgl_natural_abstract [Finite I] (hI : ∀ x : I, x ^ 2 = 1)
    (σ : GL (Fin 3) (ZMod 2) →* MulAut I) (hnt : ∃ i : I, i ≠ 1)
    (hgen : ∀ i : I, i ∈ Subgroup.closure
      {x : I | ∃ (g : GL (Fin 3) (ZMod 2)) (j : I), x = σ g j * j⁻¹})
    (hirr : ∀ J : Subgroup I, (∀ g, ∀ j ∈ J, σ g j ∈ J) → W183PglFixed σ ≤ J →
      J = W183PglFixed σ ∨ J = ⊤)
    (hq₁ : ∃ x y : GL (Fin 3) (ZMod 2), W183PglAxis x y ∧ W183PglQuad σ x y)
    (hq₂ : ∃ x y : GL (Fin 3) (ZMod 2), W183PglAxis x y ∧
      W183PglQuad (σ.comp w183PglTau.toMonoidHom) x y) :
    (∃ φ : I ≃* W183PglVec, ∀ (g : GL (Fin 3) (ZMod 2)) (i : I),
        Multiplicative.toAdd (φ (σ g i)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (φ i)) ∨
      (∃ φ : I ≃* W183PglVec, ∀ (g : GL (Fin 3) (ZMod 2)) (i : I),
        Multiplicative.toAdd (φ (σ g i)) =
          ((w183PglTau g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (φ i)) := by
  rcases w183Pgl_top_classify hI σ hnt hgen hirr with ⟨π, hπ, hker, hπσ⟩ | ⟨π, hπ, hker, hπσ⟩ |
    ⟨π, hπ, hker, hπσ⟩
  · obtain ⟨x, y, hxy, hq⟩ := hq₁
    have hinj := w183Pgl_natural_inj hI σ π hπ hπσ hker hgen hxy hq
    exact Or.inl ⟨MulEquiv.ofBijective π ⟨hinj, hπ⟩, hπσ⟩
  · obtain ⟨x, y, hxy, hq⟩ := hq₂
    have hπσ' : ∀ (g : GL (Fin 3) (ZMod 2)) (i : I),
        Multiplicative.toAdd (π ((σ.comp w183PglTau.toMonoidHom) g i)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i) := by
      intro g i
      have h := hπσ (w183PglTau g) i
      rw [Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose] at h
      exact h
    have hker' : ∀ i : I, π i = 1 → ∀ g, (σ.comp w183PglTau.toMonoidHom) g i = i :=
      fun i hi g => hker i hi _
    have hgen' : ∀ i : I, i ∈ Subgroup.closure
        {x : I | ∃ (g : GL (Fin 3) (ZMod 2)) (j : I),
          x = (σ.comp w183PglTau.toMonoidHom) g j * j⁻¹} := by
      intro i
      refine Subgroup.closure_mono ?_ (hgen i)
      rintro x ⟨g, j, rfl⟩
      refine ⟨w183PglTau.symm g, j, ?_⟩
      simp
    have hinj := w183Pgl_natural_inj hI (σ.comp w183PglTau.toMonoidHom) π hπ hπσ' hker' hgen'
      hxy hq
    exact Or.inr ⟨MulEquiv.ofBijective π ⟨hinj, hπ⟩, hπσ⟩
  · exfalso
    obtain ⟨x, y, hxy, hq⟩ := hq₁
    obtain ⟨X, hXtr, hX⟩ := w183Pgl_adj_not_quadratic (w183Pgl_axis_klein hxy)
    obtain ⟨i, hi⟩ := hπ ⟨Multiplicative.ofAdd X, w183Pgl_mem_adj.2 (by simpa using hXtr)⟩
    have hqi := hq x y (Or.inl rfl) (Or.inr (Or.inl rfl)) i
    have hPi : Multiplicative.toAdd
        (π i : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) = X := by
      rw [hi]
      rfl
    have hP : ∀ a b : I, Multiplicative.toAdd
        (π (a * b⁻¹) : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) =
          Multiplicative.toAdd (π a : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) -
            Multiplicative.toAdd (π b : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
      intro a b
      rw [map_mul, map_inv]
      simp [toAdd_mul, toAdd_inv, sub_eq_add_neg]
    have h1 := congrArg (fun z : I =>
      Multiplicative.toAdd (π z : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))) hqi
    rw [hπσ y, hP, hπσ x, hPi] at h1
    exact hX h1

end CFSG.LocalAnalysis.WeakClosure81

end
