module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCentreStmts
public import CFSG.LocalAnalysis.StandardType.GGLangRatFixedChassis
public import Certificates.Certificate13659
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.LieType.Chevalley.OrthogonalUnionBruhat
import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.LocalAnalysis.StandardType.GGLangRatCentreFactor
import CFSG.LocalAnalysis.StandardType.GGLangRatCentreWeyl
import CFSG.LocalAnalysis.StandardType.GGLangRatCentreSqInner
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped TensorProduct

section Lists

private theorem langRatCS_smul_sum {τ : Tag} (c : ℤ) (x : Fin τ.rank → ℤ)
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) :
    c • (l.map fun p => iform x p.1 • p.2).sum =
      ((l.map fun p => (p.1, c • p.2)).map fun p => iform x p.1 • p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, smul_add] at ih ⊢
    rw [ih, smul_comm]

private theorem langRatCS_weyl_smul_sum {τ : Tag} (u : WeylGroup τ) (x : Fin τ.rank → ℤ)
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) :
    u • (l.map fun p => iform x p.1 • p.2).sum =
      ((l.map fun p => (p.1, u • p.2)).map fun p => iform x p.1 • p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, smul_add] at ih ⊢
    rw [ih, smul_comm]

private theorem langRatCS_sum_sub {τ : Tag} (g : WeylGroup τ) (x : Fin τ.rank → ℤ)
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) :
    ((l.map fun p => (p.1, g • p.2 - p.2)).map fun p => iform x p.1 • p.2).sum =
      ((l.map fun p => (p.1, g • p.2)).map fun p => iform x p.1 • p.2).sum -
        (l.map fun p => iform x p.1 • p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, smul_sub] at ih ⊢
    rw [ih]
    abel

private theorem langRatCS_sum_add_left {τ : Tag}
    (x y : Fin τ.rank → ℤ)
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) :
    (l.map fun p => iform (x + y) p.1 • p.2).sum =
      (l.map fun p => iform x p.1 • p.2).sum + (l.map fun p => iform y p.1 • p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, iform_add_left, add_smul] at ih ⊢
    rw [ih]
    abel

private theorem langRatCS_sum_smul_left {τ : Tag}
    (c : ℤ) (x : Fin τ.rank → ℤ)
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) :
    (l.map fun p => iform (c • x) p.1 • p.2).sum = c • (l.map fun p => iform x p.1 • p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, iform_smul_left, smul_add, mul_smul] at ih ⊢
    rw [ih]

private theorem langRatCS_flatMap_sum {ι : Type} {τ : Tag} (x : Fin τ.rank → ℤ)
    (ls : ι → List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) (k : ι) :
    ∀ J : List ι, J.Nodup → k ∈ J → (∀ j ∈ J, j ≠ k → ∀ p ∈ ls j, iform x p.1 = 0) →
      ((J.flatMap ls).map fun p => iform x p.1 • p.2).sum =
        ((ls k).map fun p => iform x p.1 • p.2).sum := by
  intro J
  induction J with
  | nil => intro _ hk; simp at hk
  | cons a J ih =>
    intro hnd hk horth
    rw [List.flatMap_cons, List.map_append, List.sum_append]
    by_cases hak : a = k
    · subst hak
      have hJ : ((J.flatMap ls).map fun p => iform x p.1 • p.2).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
        obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.1 hp
        have hjne : j ≠ a := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hj)
        simp [horth j (List.mem_cons_of_mem _ hj) hjne p hpj]
      rw [hJ, add_zero]
    · have hk' : k ∈ J := (List.mem_cons.1 hk).resolve_left (fun h => hak h.symm)
      have h0 : ((ls a).map fun p => iform x p.1 • p.2).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
        simp [horth a List.mem_cons_self hak p hp]
      rw [h0, zero_add]
      exact ih (List.nodup_cons.1 hnd).2 hk'
        (fun j hj hjk => horth j (List.mem_cons_of_mem _ hj) hjk)

end Lists

section Span

private theorem langRatCS_smul_mem_span {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (u : WeylGroup τ)
    (hu : ∀ γ ∈ Ψ, u • γ ∈ Ψ) {x : Fin τ.rank → ℤ} (hx : x ∈ Submodule.span ℤ Ψ) :
    u • x ∈ Submodule.span ℤ Ψ := by
  induction hx using Submodule.span_induction with
  | mem γ hγ => exact Submodule.subset_span (hu γ hγ)
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

private theorem langRatCS_smul_eq_on_span {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (u u' : WeylGroup τ)
    (h : ∀ γ ∈ Ψ, u • γ = u' • γ) {x : Fin τ.rank → ℤ} (hx : x ∈ Submodule.span ℤ Ψ) :
    u • x = u' • x := by
  induction hx using Submodule.span_induction with
  | mem γ hγ => exact h γ hγ
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add, smul_add, ha, hb]
  | smul c a _ ha => rw [smul_comm u c a, smul_comm u' c a, ha]

end Span

private theorem langRatCS_component_factor {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8)
    (hB2 : LangRatSqInnerOrDet) {Ψ' : Set (Fin τ.rank → ℤ)}
    (hΨ' : IsRootComponent Ψ') (w : WeylGroup τ) (m : ℕ)
    (hbij : Set.BijOn (fun x : Fin τ.rank → ℤ => (w ^ m) • x) Ψ' Ψ') :
    ∃ l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)),
      (∀ p ∈ l, p.1 ∈ Ψ' ∧ p.2 ∈ Submodule.span ℤ Ψ') ∧
        ∀ x ∈ Submodule.span ℤ Ψ',
          (4 : ℤ) • ((w ^ (2 * m)) • x - x) = (l.map fun p => iform x p.1 • p.2).sum := by
  have hA2 := langRatWeylFactor_holds
  have hB1 := langRatFactorOfDet_holds
  have hmaps2 : ∀ γ ∈ Ψ', (w ^ (2 * m)) • γ ∈ Ψ' := by
    intro γ hγ
    have h1 := hbij.mapsTo (hbij.mapsTo hγ)
    simpa [← mul_smul, ← pow_add, two_mul] using h1
  have hiso : ∀ γ ∈ Ψ', ∀ δ ∈ Ψ', iform ((w ^ m) • γ) ((w ^ m) • δ) = iform γ δ :=
    fun γ _ δ _ => iform_smul _ γ δ
  have hneg : ∀ γ ∈ Ψ', (w ^ m) • (-γ) = -((w ^ m) • γ) := fun γ _ => smul_neg _ _
  rcases hB2 τ hτ Ψ' hΨ' (fun x => (w ^ m) • x) hbij hiso hneg with hin | hdet
  · obtain ⟨u, hu, hσu⟩ := hin
    obtain ⟨l, hl, hrep⟩ := hA2 τ hτ Ψ' hΨ'.isRoot u hu
    refine ⟨l.map fun p => (p.1, (4 : ℤ) • p.2), ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨(hl q hq).1, Submodule.smul_mem _ _ (hl q hq).2⟩
    · intro x hx
      have h1 : ∀ γ ∈ Ψ', (w ^ (2 * m)) • γ = u • γ := by
        intro γ hγ
        have := hσu γ hγ
        simpa [← mul_smul, ← pow_add, two_mul] using this
      have h2 := langRatCS_smul_eq_on_span (w ^ (2 * m)) u h1 hx
      rw [h2, ← langRatCS_smul_sum, ← hrep x hx]
  · obtain ⟨l, hl, hrep⟩ := hB1 τ hτ Ψ' hΨ' hdet
    refine ⟨l.map fun p => (p.1, (w ^ (2 * m)) • p.2 - p.2), ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨(hl q hq).1, Submodule.sub_mem _
        (langRatCS_smul_mem_span _ hmaps2 (hl q hq).2) (hl q hq).2⟩
    · intro x hx
      rw [langRatCS_sum_sub, ← langRatCS_weyl_smul_sum, ← hrep x hx, smul_sub, smul_comm]

private theorem langRatCS_pooled {τ : Tag}
    (w : WeylGroup τ) (n m : ℕ) (Ψ : Set (Fin τ.rank → ℤ))
    (Ψk : ℕ → Set (Fin τ.rank → ℤ)) (hcover : ∀ γ ∈ Ψ, ∃ k < m, γ ∈ Ψk k)
    (hsub : ∀ k, Ψk k ⊆ Ψ)
    (horth : ∀ k < m, ∀ k' < m, k ≠ k' → ∀ γ ∈ Ψk k, ∀ δ ∈ Ψk k', iform γ δ = 0)
    (l : ℕ → List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)))
    (hl : ∀ k, ∀ p ∈ l k, p.1 ∈ Ψk k ∧ p.2 ∈ Submodule.span ℤ (Ψk k))
    (hrep : ∀ k, ∀ x ∈ Submodule.span ℤ (Ψk k),
      (4 : ℤ) • ((w ^ n) • x - x) = ((l k).map fun p => iform x p.1 • p.2).sum) :
    LangRatRootFactor Ψ (fun x => (4 : ℤ) • ((w ^ n) • x - x)) := by
  refine ⟨(List.range m).flatMap l, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, _, hpk⟩ := List.mem_flatMap.1 hp
    exact ⟨hsub k (hl k p hpk).1, Submodule.span_mono (hsub k) (hl k p hpk).2⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem γ hγ =>
      obtain ⟨k, hk, hγk⟩ := hcover γ hγ
      have h1 := hrep k γ (Submodule.subset_span hγk)
      have horth' : ∀ j ∈ List.range m, j ≠ k → ∀ p ∈ l j, iform γ p.1 = 0 := by
        intro j hj hjk p hp
        exact horth k hk j (List.mem_range.1 hj) (Ne.symm hjk) γ hγk p.1 (hl j p hp).1
      rw [langRatCS_flatMap_sum γ l k (List.range m) (List.nodup_range) (List.mem_range.2 hk)
        horth']
      exact h1
    | zero =>
      have h0 : ∀ y : Fin τ.rank → ℤ, iform (0 : Fin τ.rank → ℤ) y = 0 := fun y => by
        simp [iform]
      simp only [smul_zero, sub_zero, h0, zero_smul, List.map_const', List.sum_replicate,
        List.length_flatMap]
    | add a b _ _ ha hb =>
      beta_reduce at ha hb ⊢
      rw [smul_add, add_sub_add_comm, smul_add, ha, hb, langRatCS_sum_add_left]
    | smul c a _ ha =>
      beta_reduce at ha ⊢
      rw [smul_comm (w ^ n) c a, ← smul_sub, smul_comm (4 : ℤ) c, ha, langRatCS_sum_smul_left]

private theorem langRatCS_tensor_scalar {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (W : M →ₗ[ℤ] M) (z : M ⊗[ℤ] N) (Q : ℤ) (hQ : (4 : ℤ) ∣ Q)
    (hz : TensorProduct.map ((4 : ℤ) • (W - 1)) (LinearMap.id : N →ₗ[ℤ] N) z = 0) :
    Q • TensorProduct.map W (LinearMap.id : N →ₗ[ℤ] N) z = Q • z := by
  obtain ⟨c, rfl⟩ := hQ
  have h1 : (4 : ℤ) • TensorProduct.map W (LinearMap.id : N →ₗ[ℤ] N) z = (4 : ℤ) • z := by
    have h2 : TensorProduct.map ((4 : ℤ) • (W - 1)) (LinearMap.id : N →ₗ[ℤ] N) z =
        (4 : ℤ) • (TensorProduct.map W (LinearMap.id : N →ₗ[ℤ] N) z - z) := by
      show (LinearMap.rTensor N ((4 : ℤ) • (W - 1))) z = _
      rw [LinearMap.rTensor_smul, LinearMap.rTensor_sub, Module.End.one_eq_id,
        LinearMap.rTensor_id]
      rfl
    rw [h2, smul_sub, sub_eq_zero] at hz
    exact hz
  rw [mul_comm, mul_smul, mul_smul, h1]

private theorem langRatCS_orbit
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) {b : Fin τ.rank → Lˣ}
    (hb : rootDiagUnit τ b ∈ S.D.torus) (i : KernelComponent (rootCharHom b)) (m : ℕ)
    (hm : m = componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) :
    ∃ Ψk : ℕ → Set (Fin τ.rank → ℤ),
      (∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, ∃ k < m, γ ∈ Ψk k) ∧
      (∀ k, Ψk k ⊆ rationalRoots S.ρ (rootCharHom b) i) ∧
      (∀ k, IsRootComponent (Ψk k)) ∧
      (∀ k, Set.BijOn (fun x : Fin τ.rank → ℤ => (w ^ m) • x) (Ψk k) (Ψk k)) ∧
      (∀ k < m, ∀ k' < m, k ≠ k' → ∀ γ ∈ Ψk k, ∀ δ ∈ Ψk k', iform γ δ = 0) := by
  classical
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  obtain ⟨hm0, hmper, hmmin⟩ := outer_componentOrbitLength_spec S hb i
  rw [← hm] at hm0 hmper hmmin
  have hmaps : Set.MapsTo (S.ρ : (Fin τ.rank → ℤ) → _) (rationalRoots S.ρ (rootCharHom b) i)
      (rationalRoots S.ρ (rootCharHom b) i) := rationalRoots_mapsTo i
  have hρΨ : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, S.ρ γ = w • γ := fun γ hγ =>
    S.rho_eq_smul hτ' hn (isRoot_of_mem_rationalRoots S i hγ)
  have hiter : ∀ k, ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i,
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ = (w ^ k) • γ := by
    intro k
    induction k with
    | zero => intro γ _; simp
    | succ k ih =>
      intro γ hγ
      rw [Function.iterate_succ_apply', hρΨ _ ((hmaps.iterate k) hγ), ih γ hγ, pow_succ', mul_smul]
  have hsub : ∀ k, (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i ⊆
      rationalRoots S.ρ (rootCharHom b) i := by
    rintro k _ ⟨δ, hδ, rfl⟩
    exact ⟨k, δ, hδ, rfl⟩
  have hdistinct : ∀ k k', k < k' → k' < m →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i ≠
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k'] '' componentRoots (rootCharHom b) i := by
    intro k k' hkk' hk' heq
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkk'
    have hk'eq : k' = k + (d + 1) := by omega
    subst hk'eq
    have h1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[k] ''
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[d + 1] '' componentRoots (rootCharHom b) i) =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k + (d + 1)] '' componentRoots (rootCharHom b) i := by
      rw [Function.iterate_add (S.ρ : (Fin τ.rank → ℤ) → _) k (d + 1), Set.image_comp]
    have h2 := Function.Injective.image_injective (S.ρ.injective.iterate k) (heq.trans h1.symm)
    exact hmmin (d + 1) (Nat.succ_pos d) (by omega) h2.symm
  refine ⟨fun k => (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i, ?_,
    hsub, ?_, ?_, ?_⟩
  · rintro γ ⟨k, δ, hδ, rfl⟩
    refine ⟨k % m, Nat.mod_lt _ hm0, ?_⟩
    show _ ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[k % m] '' componentRoots (rootCharHom b) i
    rw [← iterate_image_period S hmper k]
    exact ⟨δ, hδ, rfl⟩
  · intro k
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hb i k
    show IsRootComponent ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i)
    rw [← hj]
    exact isRootComponent_componentRoots j
  · intro k
    have himg : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] ''
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i) =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i := by
      rw [← Set.image_comp, ← Function.iterate_add, Nat.add_comm, Function.iterate_add,
        Set.image_comp, hmper]
    have heq : (fun x : Fin τ.rank → ℤ => (w ^ m) • x) ''
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i) =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i :=
      (Set.image_congr fun x hx => (hiter m x (hsub k hx)).symm).trans himg
    refine ⟨Set.mapsTo_iff_image_subset.2 heq.le, fun x _ y _ hxy => MulAction.injective (w ^ m) hxy, heq.ge⟩
  · intro k hk k' hk' hkk' γ hγ δ hδ
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hb i k
    obtain ⟨j', hj'⟩ := outer_iterate_image_component S hb i k'
    have hjj' : j ≠ j' := by
      intro h
      subst h
      rcases lt_or_gt_of_ne hkk' with hlt | hlt
      · exact hdistinct k k' hlt hk' (hj.symm.trans hj')
      · exact hdistinct k' k hlt hk (hj'.symm.trans hj)
    have hγ' : γ ∈ componentRoots (rootCharHom b) j := by rw [hj]; exact hγ
    have hδ' : δ ∈ componentRoots (rootCharHom b) j' := by rw [hj']; exact hδ
    exact iform_eq_zero_of_mem_componentRoots hjj' hγ' hδ'

theorem langRatCentreSq_of_stageD
    (hB2 : LangRatSqInnerOrDet) : LangRatCentreSq := by
  have hA1 := langRatCentreOfFactor_holds
  intro τ L _ _ hchar p₀ S hτ w hn b hb i hw z hz
  obtain ⟨hm0, -, -⟩ := outer_componentOrbitLength_spec S hb i
  set m := componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) with hm
  obtain ⟨Ψk, hcover, hsub, hcomp, hbij, horth⟩ := langRatCS_orbit S hτ hn hb i m hm
  choose l hl hrep using fun k =>
    langRatCS_component_factor hτ hB2 (hcomp k) w m (hbij k)
  have hfac := langRatCS_pooled w (2 * m) m _ Ψk hcover hsub horth l hl hrep
  have hh : ∀ x : ↥(Submodule.span ℤ (rationalRoots S.ρ (rootCharHom b) i)),
      ((((4 : ℤ) • ((wRestrict _ w hw) ^ (2 * m) - 1)) x :
        ↥(Submodule.span ℤ (rationalRoots S.ρ (rootCharHom b) i))) : Fin τ.rank → ℤ) =
        (4 : ℤ) • ((w ^ (2 * m)) • (x : Fin τ.rank → ℤ) - (x : Fin τ.rank → ℤ)) := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
      langRatWRestrict_pow_coe, Module.End.one_apply]
  have hz0 := hA1 τ L _ _ ((4 : ℤ) • ((wRestrict _ w hw) ^ (2 * m) - 1)) hfac hh z hz
  have h2q : 2 ∣ S.D.q := (CharP.cast_eq_zero_iff L 2 S.D.q).1 S.hqpow.2
  have h4 : (4 : ℤ) ∣ (S.D.q : ℤ) ^ (2 * m) := by
    have h2 : (2 : ℤ) ∣ (S.D.q : ℤ) := by exact_mod_cast h2q
    exact dvd_trans (by norm_num : (4 : ℤ) ∣ 2 ^ 2)
      (dvd_trans (pow_dvd_pow_of_dvd h2 2) (pow_dvd_pow _ (by omega)))
  rw [langRatSigmaT_pow_apply, langRatCS_tensor_scalar _ z _ h4 hz0]
  congr 1
  ring

theorem langRatCentreSq_holds :
    LangRatCentreSq :=
  langRatCentreSq_of_stageD langRatSqInnerOrDet_holds

end CFSG.StandardType.LangRat
