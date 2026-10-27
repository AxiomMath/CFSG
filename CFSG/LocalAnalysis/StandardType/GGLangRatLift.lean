module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLift
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped TensorProduct

noncomputable def wRestrict {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) :
    ↥(Submodule.span ℤ Ψ) →ₗ[ℤ] ↥(Submodule.span ℤ Ψ) :=
  LinearMap.restrict
    ({ toFun := fun x => w • x, map_add' := smul_add w, map_smul' := fun c x => smul_comm w c x } :
      (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ))
    (p := Submodule.span ℤ Ψ) (q := Submodule.span ℤ Ψ)
    (fun x hx => (Submodule.span_le (p := (Submodule.span ℤ Ψ).comap
      ({ toFun := fun x => w • x, map_add' := smul_add w, map_smul' := fun c x => smul_comm w c x } :
        (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ)))).2
      (fun γ hγ => Submodule.subset_span (hw γ hγ)) hx)

abbrev TSc {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] : Type :=
  ↥(Submodule.span ℤ Ψ) ⊗[ℤ] Additive Lˣ

noncomputable def langRatPiT
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] :
    TSc Ψ L →ₗ[ℤ] Additive (Fin τ.rank → Lˣ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ
      (fun (γ : ↥(Submodule.span ℤ Ψ)) (u : Additive Lˣ) =>
        Additive.ofMul (fun l : Fin τ.rank =>
          (Additive.toMul u) ^ iform (γ : Fin τ.rank → ℤ) (Pi.single l 1)))
      (fun γ γ' u => by
        refine congrArg Additive.ofMul (funext fun l => ?_)
        show (Additive.toMul u) ^ iform ((γ : Fin τ.rank → ℤ) + (γ' : Fin τ.rank → ℤ))
            (Pi.single l 1) = _ * _
        rw [iform_add_left, zpow_add] <;> rfl)
      (fun c γ u => by
        refine congrArg Additive.ofMul (funext fun l => ?_)
        show (Additive.toMul u) ^ iform (c • (γ : Fin τ.rank → ℤ)) (Pi.single l 1) =
          ((Additive.toMul u) ^ iform (γ : Fin τ.rank → ℤ) (Pi.single l 1)) ^ c
        rw [iform_smul_left, zpow_mul'] <;> rfl)
      (fun γ u u' => by
        refine congrArg Additive.ofMul (funext fun l => ?_)
        show (Additive.toMul u * Additive.toMul u') ^ iform (γ : Fin τ.rank → ℤ) (Pi.single l 1) =
          _ * _
        rw [mul_zpow] <;> rfl)
      (fun c γ u => by
        refine congrArg Additive.ofMul (funext fun l => ?_)
        show (Additive.toMul u ^ c) ^ iform (γ : Fin τ.rank → ℤ) (Pi.single l 1) =
          ((Additive.toMul u) ^ iform (γ : Fin τ.rank → ℤ) (Pi.single l 1)) ^ c
        rw [← zpow_mul, ← zpow_mul, mul_comm] <;> rfl))

noncomputable def langRatSigmaT {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q : ℕ) : TSc Ψ L →ₗ[ℤ] TSc Ψ L :=
  TensorProduct.map (wRestrict Ψ w hw) ((q : ℤ) • LinearMap.id)

theorem coe_wRestrict {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (x : ↥(Submodule.span ℤ Ψ)) :
    ((wRestrict Ψ w hw x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = w • (x : Fin τ.rank → ℤ) := by
  rfl

theorem langRatSigmaT_tmul {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L]
    (w : WeylGroup τ) (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q : ℕ) (x : ↥(Submodule.span ℤ Ψ))
    (v : Additive Lˣ) :
    langRatSigmaT Ψ L w hw q (x ⊗ₜ[ℤ] v) = wRestrict Ψ w hw x ⊗ₜ[ℤ] ((q : ℤ) • v) := by
  rfl

theorem toMul_langRatPiT_tmul
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] (x : ↥(Submodule.span ℤ Ψ))
    (v : Additive Lˣ) :
    Additive.toMul (langRatPiT Ψ L (x ⊗ₜ[ℤ] v)) =
      fun l : Fin τ.rank => Additive.toMul v ^ iform (x : Fin τ.rank → ℤ) (Pi.single l 1) := by
  rfl

theorem exists_sigma_fixed_lift {A : Type*} [AddCommGroup A] (σ : Module.End ℤ A) (K : AddSubgroup A)
    (hσK : ∀ z ∈ K, σ z ∈ K) (n : ℕ) (c : ℤ) (hK : ∀ z ∈ K, (σ ^ n) z = c • z) (a : A)
    (ha : σ a - a ∈ K) : ∃ k : A, σ k = k ∧ k - (c - 1) • a ∈ K := by
  set u := σ a - a with hu
  have hpow : ∀ m : ℕ, (σ ^ m) u ∈ K := by
    intro m
    induction m with
    | zero => simpa using ha
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hσK _ ih
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, (σ ^ k) u ∈ K := fun m =>
    K.sum_mem fun k _ => hpow k
  have htel : ∀ m : ℕ, σ (∑ k ∈ Finset.range m, (σ ^ k) u) - ∑ k ∈ Finset.range m, (σ ^ k) u =
      (σ ^ m) u - u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, map_add, pow_succ' σ m, Module.End.mul_apply]
      calc σ (∑ k ∈ Finset.range m, (σ ^ k) u) + σ ((σ ^ m) u) -
            (∑ k ∈ Finset.range m, (σ ^ k) u + (σ ^ m) u)
          = (σ (∑ k ∈ Finset.range m, (σ ^ k) u) - ∑ k ∈ Finset.range m, (σ ^ k) u) +
            σ ((σ ^ m) u) - (σ ^ m) u := by abel
        _ = σ ((σ ^ m) u) - u := by rw [ih]; abel
  refine ⟨(c - 1) • a - ∑ k ∈ Finset.range n, (σ ^ k) u, ?_, ?_⟩
  · have h1 := htel n
    rw [hK u ha] at h1
    have h2 : σ ((c - 1) • a - ∑ k ∈ Finset.range n, (σ ^ k) u) -
        ((c - 1) • a - ∑ k ∈ Finset.range n, (σ ^ k) u) = 0 := by
      rw [map_sub, map_zsmul]
      calc (c - 1) • σ a - σ (∑ k ∈ Finset.range n, (σ ^ k) u) -
            ((c - 1) • a - ∑ k ∈ Finset.range n, (σ ^ k) u)
          = (c - 1) • (σ a - a) - (σ (∑ k ∈ Finset.range n, (σ ^ k) u) -
            ∑ k ∈ Finset.range n, (σ ^ k) u) := by rw [smul_sub]; abel
        _ = 0 := by rw [h1, ← hu, sub_smul, one_smul]; abel
    exact sub_eq_zero.1 h2
  · have : (c - 1) • a - ∑ k ∈ Finset.range n, (σ ^ k) u - (c - 1) • a =
        -∑ k ∈ Finset.range n, (σ ^ k) u := by abel
    rw [this]
    exact K.neg_mem (hsum n)

@[expose] def LangRatLatticeLift :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → ∀ w : WeylGroup τ, S.D.n = canonicalRep (coxeterSystem τ) L w →
    ∀ a b : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      ∀ (i : KernelComponent (rootCharHom b)) (hw : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i,
          w • γ ∈ rationalRoots S.ρ (rootCharHom b) i),
        ∃ x : TSc (rationalRoots S.ρ (rootCharHom b) i) L,
          langRatSigmaT _ L w hw S.D.q x = x ∧ ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i,
            rootChar (Additive.toMul (langRatPiT _ L x)) γ = rootChar a γ ^ ((S.D.q ^ componentOrbitLength S.ρ
              (componentRoots (rootCharHom b) i)) ^ 2 - 1)

@[expose] def LangRatTorusFixedMemKind
    (k : TwistKind) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → S.IsAlgebraic → ∀ w : WeylGroup τ,
    S.D.n = canonicalRep (coxeterSystem τ) L w →
    ∀ b : Fin τ.rank → Lˣ, rootDiagUnit τ b ∈ S.D.torus → ∀ i : KernelComponent (rootCharHom b),
      twistKind S.ρ (rootCharHom b) i = k →
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) →
      ∀ (hw : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, w • γ ∈ rationalRoots S.ρ (rootCharHom b) i)
        (x : TSc (rationalRoots S.ρ (rootCharHom b) i) L), langRatSigmaT _ L w hw S.D.q x = x →
          rootDiagUnit τ (Additive.toMul (langRatPiT _ L x)) ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i

@[expose] def LangRatTorusFixedMem :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → S.IsAlgebraic → ∀ w : WeylGroup τ,
    S.D.n = canonicalRep (coxeterSystem τ) L w →
    ∀ b : Fin τ.rank → Lˣ, rootDiagUnit τ b ∈ S.D.torus → ∀ i : KernelComponent (rootCharHom b),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) →
      ∀ (hw : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, w • γ ∈ rationalRoots S.ρ (rootCharHom b) i)
        (x : TSc (rationalRoots S.ρ (rootCharHom b) i) L), langRatSigmaT _ L w hw S.D.q x = x →
          rootDiagUnit τ (Additive.toMul (langRatPiT _ L x)) ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i

@[expose] def LangRatCentreSq :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → ∀ w : WeylGroup τ, S.D.n = canonicalRep (coxeterSystem τ) L w →
    ∀ b : Fin τ.rank → Lˣ, rootDiagUnit τ b ∈ S.D.torus →
      ∀ (i : KernelComponent (rootCharHom b)) (hw : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i,
          w • γ ∈ rationalRoots S.ρ (rootCharHom b) i) (z : TSc (rationalRoots S.ρ (rootCharHom b) i) L),
        (∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, rootChar (Additive.toMul (langRatPiT _ L z)) γ = 1) →
          ((langRatSigmaT _ L w hw S.D.q : Module.End ℤ (TSc (rationalRoots S.ρ (rootCharHom b) i) L)) ^
              (2 * componentOrbitLength S.ρ (componentRoots (rootCharHom b) i))) z =
            ((S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) ^ 2 : ℤ) • z

theorem langRatRootStep_holds :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
      (τ = .E7 ∨ τ = .E8) → ∀ c : Fin τ.rank → Lˣ, ∃ c' : Fin τ.rank → Lˣ,
        S.D.step (rootDiagUnit τ c) = rootDiagUnit τ c' ∧
          ∀ γ, IsRoot τ γ → rootChar c' (S.ρ γ) = rootChar c γ ^ S.D.q := by
  intro τ L _ _ p₀ S hτ c
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  obtain ⟨w, hn⟩ := S.D.n_weyl
  refine ⟨weylTuple w (fun j => c j ^ S.D.q), ?_, fun γ hγ => ?_⟩
  · have h1 : S.D.Φ (rootDiagUnit τ c) = rootDiagUnit τ (fun j => c j ^ S.D.q) := by
      rw [hΦ, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit]
      congr 1
      funext j
      exact S.units_map_frob hFr hΦ hn (c j)
    show S.D.n * S.D.Φ (rootDiagUnit τ c) * S.D.n⁻¹ = _
    rw [h1, hn]
    exact canonicalRep_conj_rootDiagUnit w _
  · rw [S.rho_eq_smul hτ' hn hγ, rootChar_weylTuple, inv_smul_smul]
    exact rootChar_pow c S.D.q γ

theorem langRatCompTorusLift_of_lift_fixed
    (h2 : LangRatLatticeLift) (h3 : LangRatTorusFixedMem) :
    LangRatCompTorusLift := by
  intro τ L _ _ _ p₀ S hτ hAlg a b ha hb i hqs
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  have hw : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, w • γ ∈ rationalRoots S.ρ (rootCharHom b) i := by
    intro γ hγ
    have h := rationalRoots_mapsTo (ρ := S.ρ) i hγ
    rwa [S.rho_eq_smul hτ' hn (isRoot_of_mem_rationalRoots S i hγ)] at h
  obtain ⟨x, hx, hxa⟩ := h2 τ L p₀ S hτ w hn a b ha hb i hw
  exact ⟨Additive.toMul (langRatPiT _ L x), h3 τ L p₀ S hτ hAlg w hn b hb i hqs hw x hx, hxa⟩

theorem langRatTorusFixedMem_of_kinds
    (hi : LangRatTorusFixedMemKind .inner)
    (hs : LangRatTorusFixedMemKind .suN) (hd : LangRatTorusFixedMemKind .twoD)
    (he : LangRatTorusFixedMemKind .exc) : LangRatTorusFixedMem := by
  intro τ L _ _ _ p₀ S hτ hAlg w hn b hb i hqs hw x hx
  cases hk : twistKind S.ρ (rootCharHom b) i with
  | inner => exact hi τ L p₀ S hτ hAlg w hn b hb i hk hqs hw x hx
  | suN => exact hs τ L p₀ S hτ hAlg w hn b hb i hk hqs hw x hx
  | twoD => exact hd τ L p₀ S hτ hAlg w hn b hb i hk hqs hw x hx
  | exc => exact he τ L p₀ S hτ hAlg w hn b hb i hk hqs hw x hx

end CFSG.StandardType.LangRat
