module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameBlock

public section

open Polynomial Module

namespace CFSG.StandardType

namespace SpNS

section Frame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

theorem block_pow_isometry {D : Type} [AddCommGroup D] [Module K D] {c : D →ₗ[K] D}
    {P : Submodule K V} (Ψ : D ≃ₗ[K] P)
    (hΨ : ∀ d d', B (Ψ (c d)) (Ψ (c d')) = B (Ψ d) (Ψ d')) (m : ℕ) (d d' : D) :
    B (Ψ ((c ^ m) d)) (Ψ ((c ^ m) d')) = B (Ψ d) (Ψ d') := by
  induction m generalizing d d' with
  | zero => rfl
  | succ m ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hΨ]

theorem bilin_add_add_of_orth (hrefl : B.IsRefl) {P : Submodule K V} {p p' q q' : V}
    (hp : p ∈ P) (hp' : p' ∈ P) (hq : q ∈ B.orthogonal P) (hq' : q' ∈ B.orthogonal P) :
    B (p + q) (p' + q') = B p p' + B q q' := by
  rw [LinearMap.map_add₂, map_add, map_add,
    LinearMap.BilinForm.mem_orthogonal_iff.mp hq' p hp,
    hrefl _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp hq p' hp')]
  ring

theorem restrict_nondegenerate_orthogonal (hrefl : B.IsRefl) (hnd : B.Nondegenerate)
    {P : Submodule K V} (hc : IsCompl P (B.orthogonal P)) :
    (B.restrict (B.orthogonal P)).Nondegenerate := by
  have hrefl' : (B.restrict (B.orthogonal P)).IsRefl := fun a b h => hrefl a b h
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl').2 fun m hm => ?_
  refine Subtype.ext (hnd.1 m fun n => ?_)
  have hn : n ∈ P ⊔ B.orthogonal P := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hn
  rw [map_add, hrefl _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp m.2 p hp), zero_add]
  exact hm ⟨q, hq⟩

theorem orthogonal_invariant_of_pow {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {x : Module.End K V} (hxℓ : x ^ ℓ = 1)
    (hxB : ∀ u w, B (x u) (x w) = B u w) {P : Submodule K V} (hP : ∀ v ∈ P, x v ∈ P) :
    ∀ v ∈ B.orthogonal P, x v ∈ B.orthogonal P := by
  have hpow : ∀ m : ℕ, ∀ v ∈ P, (x ^ m) v ∈ P := by
    intro m
    induction m with
    | zero => exact fun v hv => hv
    | succ m ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hP _ (ih v hv)
  exact orthogonal_invariant (y' := x ^ (ℓ - 1)) (pow_pred_mul hℓ hxℓ) (bilin_pow_pow hxB _)
    (hpow (ℓ - 1))

end Frame

section Ind

variable {K : Type} [Field K] {ℓ : ℕ} {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] [Nontrivial D] {c : D →ₗ[K] D}

theorem exists_spFrame (hD : SpBlockExists K ℓ D c) (hℓ : 1 ≤ ℓ) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (S : Set (Module.End K V)) (hAlt : B.IsAlt) (hnd : B.Nondegenerate)
    (hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x') (hSp : ∀ x ∈ S, x ^ ℓ = 1)
    (hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w) :
    ∃ (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ) (Φ : ((ι → D) × (κ → K)) ≃ₗ[K] V),
      (∀ x ∈ S, ∃ k : ι → ℕ, ∀ d w, x (Φ (d, w)) = Φ (fun i => (c ^ k i) (d i), w)) ∧
      ∀ (k : ι → ℕ) (d d' : ι → D) (w w' : κ → K),
        B (Φ (fun i => (c ^ k i) (d i), w)) (Φ (fun i => (c ^ k i) (d' i), w')) =
          B (Φ (d, w)) (Φ (d', w')) := by
  induction hn : finrank K V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_cases hS1 : ∀ x ∈ S, x = 1
  · have hE : ∀ f f' : Empty → D, f = f' := fun f f' => Subsingleton.elim f f'
    refine ⟨Empty, Fin (finrank K V), inferInstance, inferInstance,
      LinearEquiv.uniqueProd.trans (Module.finBasis K V).equivFun.symm,
      fun x hx => ⟨Empty.elim, fun d w => ?_⟩, fun k d d' w w' => ?_⟩
    · rw [hS1 x hx, Module.End.one_apply, hE (fun i => (c ^ Empty.elim i) (d i)) d]
    · rw [hE (fun i => (c ^ k i) (d i)) d, hE (fun i => (c ^ k i) (d' i)) d']
  push Not at hS1
  obtain ⟨P, Ψ, hPnd, hΨB, hΨS⟩ := hD V B S hAlt hnd hSc hSp hSB hS1
  have hrefl : B.IsRefl := hAlt.isRefl
  set Q := B.orthogonal P with hQ
  have hcompl : IsCompl P Q :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hPnd
  have hSP : ∀ x ∈ S, ∀ v ∈ P, x v ∈ P := by
    intro x hx v hv
    obtain ⟨a, ha⟩ := hΨS x hx
    have h1 := ha (Ψ.symm ⟨v, hv⟩)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [show v = ((⟨v, hv⟩ : P) : V) from rfl, h1]
    exact (Ψ _).2
  have hSQ : ∀ x ∈ S, ∀ v ∈ Q, x v ∈ Q := fun x hx =>
    orthogonal_invariant_of_pow hℓ (hSp x hx) (hSB x hx) (hSP x hx)
  have hQnd : (B.restrict Q).Nondegenerate := restrict_nondegenerate_orthogonal hrefl hnd hcompl
  have hfr := Submodule.finrank_add_eq_of_isCompl hcompl
  have hPpos : 0 < finrank K P := by
    rw [← LinearEquiv.finrank_eq Ψ]
    exact Module.finrank_pos
  let r : S → Module.End K Q := fun x => x.1.restrict (hSQ x.1 x.2)
  obtain ⟨ι', κ', _, _, Φ', hΦ'S, hΦ'B⟩ := ih (finrank K Q) (by omega) (B.restrict Q)
    (Set.range r) (fun z => hAlt z) hQnd
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
      exact OrdPNS.restrict_commute' (hSc x.1 x.2 x'.1 x'.2) _ _)
    (by
      rintro _ ⟨x, rfl⟩
      exact OrdPNS.restrict_pow_eq_one (hSp x.1 x.2) _)
    (by
      rintro _ ⟨x, rfl⟩ u w
      exact hSB x.1 x.2 u w) rfl
  set Φ : (((Unit ⊕ ι') → D) × (κ' → K)) ≃ₗ[K] V :=
    ((LinearEquiv.sumArrowLequivProdArrow Unit ι' K D).prodCongr
      (LinearEquiv.refl K (κ' → K))).trans ((LinearEquiv.prodAssoc K _ _ _).trans
      (((LinearEquiv.funUnique Unit K D).prodCongr (LinearEquiv.refl K _)).trans
        ((Ψ.prodCongr Φ').trans (Submodule.prodEquivOfIsCompl P Q hcompl)))) with hΦ
  have hΦapp : ∀ d w, Φ (d, w) = (Ψ (d (Sum.inl ())) : V) + (Φ' (d ∘ Sum.inr, w) : V) :=
    fun d w => rfl
  refine ⟨Unit ⊕ ι', κ', inferInstance, inferInstance, Φ, fun x hx => ?_,
    fun k d d' w w' => ?_⟩
  · obtain ⟨a, ha⟩ := hΨS x hx
    obtain ⟨k', hk'⟩ := hΦ'S (r ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
    refine ⟨Sum.elim (fun _ => a) k', fun d w => ?_⟩
    have e : x (Φ' (d ∘ Sum.inr, w) : V) =
        (Φ' (fun j => (c ^ k' j) (d (Sum.inr j)), w) : V) := congrArg Subtype.val (hk' _ w)
    rw [hΦapp, hΦapp, map_add, ha, e]
    rfl
  · rw [hΦapp, hΦapp, hΦapp, hΦapp,
      bilin_add_add_of_orth hrefl (Ψ _).2 (Ψ _).2 (Φ' _).2 (Φ' _).2,
      bilin_add_add_of_orth hrefl (Ψ _).2 (Ψ _).2 (Φ' _).2 (Φ' _).2]
    congr 1
    · exact block_pow_isometry Ψ hΨB (k (Sum.inl ())) _ _
    · exact hΦ'B (k ∘ Sum.inr) (d ∘ Sum.inr) (d' ∘ Sum.inr) w w'

end Ind

end SpNS

end CFSG.StandardType
