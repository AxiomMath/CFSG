module

public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE


section Generic

theorem iterate_lang {G : Type*} [Group G] (Φ : G →* G) {g₀ n₀ : G} (hn : Φ n₀ = n₀)
    (hg : Φ g₀ = g₀ * n₀) (j : ℕ) : (⇑Φ)^[j] g₀ = g₀ * n₀ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, hg, map_pow, hn]
    group

theorem iterate_F0 {G : Type*} [Group G] (Φ : G →* G) {n₀ : G} (hn : Φ n₀ = n₀) (j : ℕ)
    (u : G) : (fun v => n₀ * Φ v * n₀⁻¹)^[j] u = n₀ ^ j * (⇑Φ)^[j] u * (n₀ ^ j)⁻¹ := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, iterate_map_mul,
      iterate_map_mul, iterate_map_inv]
    have h1 : (⇑Φ)^[j] n₀ = n₀ := Function.iterate_fixed hn j
    rw [h1]
    group

end Generic

section Basic

variable {τ : Tag} {K L : Type} [Field K] [Field L] [Algebra K L]

@[expose] def psiTilde (τ : Tag) (K L : Type) [Field K] [Field L] [Algebra K L] (g₀ : ModGL τ L)
    (c : adjointGroup τ K) : adjointGroup τ K →* ModGL τ L :=
  (MulAut.conj g₀⁻¹).toMonoidHom.comp ((adjEmb τ K L).comp (MulAut.conj c).toMonoidHom)

theorem psiTilde_apply (g₀ : ModGL τ L) (c y : adjointGroup τ K) :
    psiTilde τ K L g₀ c y = g₀⁻¹ * adjEmb τ K L (c * y * c⁻¹) * g₀ := by
  simp [psiTilde, MulAut.conj_apply]

theorem psiTilde_injective (g₀ : ModGL τ L) (c : adjointGroup τ K) :
    Function.Injective (psiTilde τ K L g₀ c) := by
  intro a b hab
  rw [psiTilde_apply, psiTilde_apply] at hab
  have h1 := mul_left_cancel (mul_right_cancel hab)
  have h2 := adjEmb_injective h1
  have := congrArg (fun z => c⁻¹ * z * c) h2
  simpa [mul_assoc] using this

theorem entrywise_adjEmb {Φ₀ : L →+* L} {σ : K ≃+* K}
    (hσ : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c)) (z : adjointGroup τ K) :
    Units.map (entrywiseHom Φ₀) (adjEmb τ K L z) = adjEmb τ K L (entrywiseAdjointAut τ σ z) := by
  have hcomp : Φ₀.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom :=
    RingHom.ext fun c => hσ c
  have e : Units.map (entrywiseHom Φ₀) (adjEmb τ K L z) =
      baseChangeGL Φ₀ (baseChangeGL (algebraMap K L) (z : ModGL τ K)) := by
    rw [adjEmb_apply]
    exact Units.ext rfl
  rw [e, baseChangeGL_baseChangeGL, hcomp, ← baseChangeGL_baseChangeGL, adjEmb_apply]
  congr 1

theorem psiTilde_entrywise {Φ₀ : L →+* L} {σ : K ≃+* K}
    (hσ : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c))
    {n₀ g₀ : ModGL τ L} (hg : Units.map (entrywiseHom Φ₀) g₀ = g₀ * n₀)
    {c : adjointGroup τ K} (hc : entrywiseAdjointAut τ σ c = c) (y : adjointGroup τ K) :
    n₀ * Units.map (entrywiseHom Φ₀) (psiTilde τ K L g₀ c y) * n₀⁻¹ =
      psiTilde τ K L g₀ c (entrywiseAdjointAut τ σ y) := by
  rw [psiTilde_apply, psiTilde_apply, map_mul, map_mul, map_inv, hg, entrywise_adjEmb hσ,
    map_mul (entrywiseAdjointAut τ σ), map_mul (entrywiseAdjointAut τ σ),
    map_inv (entrywiseAdjointAut τ σ), hc]
  group

end Basic

section Frobenius

variable {τ : Tag} {L : Type} [Field L]

theorem units_map_entrywiseHom_iterateFrobenius_mul {ℓ : ℕ} [ExpChar L ℓ] (f k : ℕ)
    (u : ModGL τ L) :
    Units.map (entrywiseHom (iterateFrobenius L ℓ (f * k))) u =
      (⇑(Units.map (entrywiseHom (iterateFrobenius L ℓ f))))^[k] u := by
  induction k generalizing u with
  | zero =>
    rw [Nat.mul_zero, iterateFrobenius_zero, Function.iterate_zero, id_eq]
    exact Units.ext (entrywise_id _)
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih,
      show f * (k + 1) = f + f * k by ring, iterateFrobenius_add]
    refine Units.ext ?_
    change entrywise _ (u : Module.End L (RootModule τ L)) = entrywise _
      (entrywise _ (u : Module.End L (RootModule τ L)))
    rw [entrywise_entrywise]

end Frobenius

end CFSG.RankThree.PartOne.KLCE
