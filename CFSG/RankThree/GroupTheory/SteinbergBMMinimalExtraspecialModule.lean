module

public import CFSG.RankThree.GroupTheory.SteinbergCEExtraspecialMinusModule
public import Mathlib.Algebra.Central.End
import Mathlib.LinearAlgebra.Eigenspace.Pi

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory
open scoped commutatorElement TensorProduct

variable {S : Type*} [Group S]

theorem pow_le_finrank_of_invariant [Finite S] {n : ℕ} (hS : IsExtraspecialPGroup 2 S)
    (hcard : Nat.card S = 2 ^ (1 + 2 * n)) {z : S} (hz : center S = zpowers z) {L V : Type*}
    [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (h2 : (2 : L) ≠ 0)
    (ρ : Representation L S V) (W : Submodule L V) (hW : W ≠ ⊥)
    (hinv : ∀ s : S, ∀ w ∈ W, ρ s w ∈ W) (hzW : ∀ w ∈ W, ρ z w = -w) :
    2 ^ n ≤ Module.finrank L W := by
  let ρW : Representation L S W :=
    { toFun := fun s => (ρ s).restrict (hinv s)
      map_one' := LinearMap.ext fun w => Subtype.ext (by
        change ρ 1 (w : V) = w
        rw [map_one, Module.End.one_apply])
      map_mul' := fun s t => LinearMap.ext fun w => Subtype.ext (by
        change ρ (s * t) (w : V) = ρ s (ρ t w)
        rw [map_mul, Module.End.mul_apply]) }
  have hρWz : ρW z = -1 := LinearMap.ext fun w => Subtype.ext (by
    change ρ z (w : V) = -(w : V)
    exact hzW w w.2)
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  exact (extraspecial_two_minus_module_bound hS hcard hz h2 ρW hρWz).1

theorem minimal_extraspecial_module_scalar_centralizer [Finite S] {n : ℕ}
    (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 2 ^ (1 + 2 * n)) {z : S}
    (hz : center S = zpowers z) {K : Type*} [Field K] (hK : ringChar K ≠ 2) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hdim : Module.finrank K V = 2 ^ n)
    (ρ : Representation K S V) (hρ : Function.Injective ρ) :
    ρ z = -1 ∧
      (∀ (L : Type*) [Field L] [Algebra K L] (W : Submodule L (L ⊗[K] V)),
        (∀ s : S, ∀ w ∈ W, (ρ s).baseChange L w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      centralizer (Set.range ρ.asGroupHom) =
        (Units.map (algebraMap K (Module.End K V)).toMonoidHom).range ∧
      (Finite K → ∀ H : Subgroup (Module.End K V)ˣ,
        H ≤ centralizer (Set.range ρ.asGroupHom) → IsCyclic H) := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hz2, hcomm⟩ := extraspecial_commutator_eq_one_or hS hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzc : z ∈ center S := hz ▸ mem_zpowers z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; positivity)
  have hρzz : ρ z * ρ z = 1 := by rw [← map_mul, hzz, map_one]
  have hρz1 : ρ z ≠ 1 := fun h => hz1 (hρ (h.trans (map_one ρ).symm))
  have hρz : ρ z = -1 := by
    set Vm := Module.End.eigenspace (ρ z) (-1) with hVm
    have hdiff : ∀ v, -v + ρ z v ∈ Vm := by
      intro v
      rw [Module.End.mem_eigenspace_iff, map_add, map_neg, ← Module.End.mul_apply, hρzz,
        Module.End.one_apply, neg_one_smul, neg_add, neg_neg, add_comm]
    have hVm_ne : Vm ≠ ⊥ := by
      intro h
      apply hρz1
      apply LinearMap.ext
      intro v
      have hw := hdiff v
      rw [h, Submodule.mem_bot] at hw
      rw [Module.End.one_apply]
      exact (neg_add_eq_zero.mp hw).symm
    have hinv : ∀ s : S, ∀ v ∈ Vm, ρ s v ∈ Vm := by
      intro s v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, ← map_mul, ← mem_center_iff.mp hzc s, map_mul,
        Module.End.mul_apply, hv, map_smul]
    have hle := pow_le_finrank_of_invariant hS hcard hz h2 ρ Vm hVm_ne hinv fun w hw => by
      rw [(Module.End.mem_eigenspace_iff.mp hw), neg_one_smul]
    have htop : Vm = ⊤ := Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le _) (hdim ▸ hle))
    apply LinearMap.ext
    intro v
    have hv : v ∈ Vm := htop ▸ Submodule.mem_top
    rw [(Module.End.mem_eigenspace_iff.mp hv), neg_one_smul, LinearMap.neg_apply,
      Module.End.one_apply]
  refine ⟨hρz, ?_, ?_⟩
  ·
    intro L _ _ W hW
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    right
    let ρL : Representation L S (L ⊗[K] V) :=
      (Module.End.baseChangeHom K L V).toRingHom.toMonoidHom.comp ρ
    have hρL : ∀ s : S, ρL s = (ρ s).baseChange L := fun _ => rfl
    have h2L : (2 : L) ≠ 0 := by
      intro h
      apply h2
      have h' : algebraMap K L 2 = 0 := by rw [map_ofNat]; exact h
      exact (algebraMap K L).injective (h'.trans (map_zero _).symm)
    have hle := pow_le_finrank_of_invariant hS hcard hz h2L ρL W hW0 (fun s w hw => hW s w hw)
      fun w _ => by
        rw [hρL, hρz, LinearMap.baseChange_neg, LinearMap.baseChange_one, LinearMap.neg_apply,
          Module.End.one_apply]
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
      (by rw [Module.finrank_baseChange, hdim]; exact hle))
  have hzinv : z⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hz2, pow_orderOf_eq_one]
  have hK1 : (1 : K) ≠ -1 := fun h => h2 (by
    rw [show (2 : K) = 1 + 1 by norm_num]
    nth_rewrite 2 [h]
    ring)
  have hρ1 : ∀ g : S, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  set χ : S → S → K := fun t s => if s * t = t * s then 1 else -1
  have hconjrep : ∀ s t : S, endConj ρ s (ρ t) = χ t s • ρ t := by
    intro s t
    have hst : s * t * s⁻¹ = ⁅s, t⁆ * t := by rw [commutatorElement_def]; group
    rw [endConj_apply, ← map_mul, ← map_mul, hst, map_mul]
    rcases hcomm s t with h | h
    · have hc : s * t = t * s := commutatorElement_eq_one_iff_mul_comm.mp h
      simp [χ, hc, h]
    · have hc : ¬ s * t = t * s := fun h' =>
        hz1 (h ▸ commutatorElement_eq_one_iff_mul_comm.mpr h')
      simp [χ, hc, h, hρz]
  have hendz : endConj ρ z = 1 := by
    apply LinearMap.ext
    intro f
    rw [endConj_apply, hzinv, hρz, Module.End.one_apply]
    simp
  have hend1 : endConj ρ 1 = 1 := by
    apply LinearMap.ext
    intro f
    rw [endConj_apply, inv_one, map_one, one_mul, mul_one, Module.End.one_apply]
  have hendc : ∀ s s' : S, Commute (endConj ρ s) (endConj ρ s') := by
    intro s s'
    have hss : s * s' = ⁅s, s'⁆ * (s' * s) := by rw [commutatorElement_def]; group
    change endConj ρ s * endConj ρ s' = endConj ρ s' * endConj ρ s
    rw [← endConj_mul, ← endConj_mul, hss, endConj_mul]
    rcases hcomm s s' with h | h
    · rw [h, hend1, one_mul]
    · rw [h, hendz, one_mul]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun s => endConj ρ s) (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hendc j i) φ)
  set Q := S ⧸ center S
  let : Fintype Q := Fintype.ofFinite Q
  set rep : Q → S := fun q => Quotient.out q
  have hinjχ : Function.Injective fun q : Q => χ (rep q) := by
    intro q q' hqq
    have hχ : ∀ s, χ (rep q) s = χ (rep q') s := fun s => congrFun hqq s
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change ((rep q : S) : Q) = ((rep q' : S) : Q)
    rw [QuotientGroup.eq, mem_center_iff]
    intro s
    have hs := hχ s
    simp only [χ] at hs
    by_cases h1 : s * rep q = rep q * s
    · have h2' : s * rep q' = rep q' * s := by
        by_contra h2'
        rw [ite_eq_left h1, ite_eq_right h2'] at hs
        exact hK1 hs
      have hc1 : Commute s (rep q) := h1
      have hc2 : Commute s (rep q') := h2'
      exact (hc1.inv_right.mul_right hc2).eq
    · have h2' : ¬ s * rep q' = rep q' * s := by
        intro h2'
        rw [ite_eq_right h1, ite_eq_left h2'] at hs
        exact hK1 hs.symm
      have e1 : ⁅s, rep q⁆ = z := (hcomm s _).resolve_left fun h =>
        h1 (commutatorElement_eq_one_iff_mul_comm.mp h)
      have e2 : ⁅s, rep q'⁆ = z := (hcomm s _).resolve_left fun h =>
        h2' (commutatorElement_eq_one_iff_mul_comm.mp h)
      rw [commutatorElement_def] at e1 e2
      have e1' : s * rep q * s⁻¹ = z * rep q := by rw [← e1]; group
      have e2' : s * rep q' * s⁻¹ = z * rep q' := by rw [← e2]; group
      calc s * ((rep q)⁻¹ * rep q') = (s * rep q * s⁻¹)⁻¹ * (s * rep q' * s⁻¹) * s := by group
        _ = (rep q)⁻¹ * rep q' * s := by rw [e1', e2']; group
  have hlin : LinearIndependent K fun q : Q => ρ (rep q) := by
    refine (hind.comp hinjχ).linearIndependent _ (fun q => ?_) (fun q => ?_)
    · simp only [Function.comp_apply, Submodule.mem_iInf]
      intro s
      apply Module.End.eigenspace_le_maxGenEigenspace
      rw [Module.End.mem_eigenspace_iff]
      exact hconjrep s (rep q)
    · intro h
      have h1 := hρ1 (rep q)
      rw [h, zero_mul] at h1
      exact zero_ne_one h1
  have hcardQ : Fintype.card Q = 2 ^ (2 * n) := by
    have h := card_eq_card_quotient_mul_card_subgroup (center S)
    rw [hS.2.2.2, hcard, ← Nat.card_eq_fintype_card] at *
    rw [pow_add, pow_one, mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm
  have hspan : Submodule.span K (Set.range fun q : Q => ρ (rep q)) = ⊤ := by
    refine hlin.span_eq_top_of_card_eq_finrank' ?_
    rw [hcardQ, Module.finrank_linearMap K K V V, hdim, two_mul, pow_add]
  have hscalar : ∀ f : Module.End K V, (∀ s : S, f * ρ s = ρ s * f) →
      ∃ c : K, algebraMap K (Module.End K V) c = f := by
    intro f hf
    have hall : ∀ g ∈ Submodule.span K (Set.range fun q : Q => ρ (rep q)), g * f = f * g := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨q, rfl⟩ := hx
        exact (hf _).symm
      | zero => rw [zero_mul, mul_zero]
      | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
      | smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
    have hmem : f ∈ Subalgebra.center K (Module.End K V) := by
      rw [Subalgebra.mem_center_iff]
      intro g
      exact hall g (hspan ▸ Submodule.mem_top)
    rw [Algebra.IsCentral.center_eq_bot] at hmem
    exact Algebra.mem_bot.mp hmem
  have hC : centralizer (Set.range ρ.asGroupHom) =
      (Units.map (algebraMap K (Module.End K V)).toMonoidHom).range := by
    ext u
    constructor
    · intro hu
      have hf : ∀ s : S, (u : Module.End K V) * ρ s = ρ s * u := fun s => by
        have h := congrArg Units.val (mem_centralizer_iff.mp hu (ρ.asGroupHom s) ⟨s, rfl⟩)
        rw [Units.val_mul, Units.val_mul, Representation.asGroupHom_apply] at h
        exact h.symm
      obtain ⟨c, hc⟩ := hscalar u hf
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hc
        exact u.ne_zero hc.symm
      refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
      rw [Units.coe_map, Units.val_mk0]
      exact hc
    · rintro ⟨c, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.coe_map]
      exact (Algebra.commutes _ _).symm
  refine ⟨hC, fun hKfin H hH => ?_⟩
  set φ := Units.map (algebraMap K (Module.End K V)).toMonoidHom with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Units.ext
    have h := congrArg Units.val hab
    rw [hφ, Units.coe_map, Units.coe_map] at h
    exact (algebraMap K (Module.End K V)).injective h
  rw [hC] at hH
  let f : H →* Kˣ := (MonoidHom.ofInjective hφinj).symm.toMonoidHom.comp (inclusion hH)
  exact isCyclic_of_injective f ((MonoidHom.ofInjective hφinj).symm.injective.comp
    (inclusion_injective hH))

end CFSG.RankThree.GroupTheory.SteinbergBM
