module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentRot
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open QuadraticMap Module
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.StandardType.OmNsRootGen SpCoord

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}
variable {U : Fin 4 → Submodule K V} {e : Fin 4 → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)}

private theorem tau_mulSingle_apply
    {τ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥(orthDerived Q)}
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e c)
    (c : Fin 4) (a : Multiplicative (ZMod 3)) :
    τ (Pi.mulSingle c a) = (e c) ^ (Multiplicative.toAdd a).val := by
  change τ (Pi.mulSingle c (Multiplicative.ofAdd (Multiplicative.toAdd a))) =
    (e c) ^ (Multiplicative.toAdd a).val
  rw [SpCoord.mulSingle_ofAdd_eq_pow, map_pow, hτ c]

private theorem pow_maps_to (hF : IsPlaneFrame Q 3 U e E) (c : Fin 4) (k : ℕ) :
    ∀ x ∈ U c, (((e c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ^ k) x ∈ U c := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ, LinearEquiv.mul_apply]
      exact ih _ (hF.maps_to c x hx)

public theorem fixedSpace_tau_eq_polarPerp (hF : IsPlaneFrame Q 3 U e E) (hp : Nat.Prime 3)
    {τ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥(orthDerived Q)}
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e c)
    (hact : ∀ f c, ∀ x ∈ U c,
      ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V) x =
        (((e c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ^ (Multiplicative.toAdd (f c)).val) x)
    (f : Fin 4 → Multiplicative (ZMod 3)) :
    fixedSpace ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V) =
      polarPerp Q (⨆ c ∈ (Finset.univ.filter (fun c => f c ≠ 1)), U c) := by
  classical
  set S : Finset (Fin 4) := Finset.univ.filter (fun c => f c ≠ 1) with hS
  ext v
  constructor
  ·
    intro hv
    rw [mem_fixedSpace] at hv
    set g : V →ₗ[K] V := ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap with hg
    have hgapply : ∀ x : V, g x = ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V) x := fun _ => rfl
    have hperpc : ∀ c, f c ≠ 1 → v ∈ polarPerp Q (U c) := by
      intro c hc
      have hord : orderOf ((e c : ↥(orthDerived Q)) : V ≃ₗ[K] V) = 3 := by
        rw [Subgroup.orderOf_coe, hF.orderOf_eq c]
      have hne1 : ((e c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ^
          (Multiplicative.toAdd (f c)).val ≠ 1 := by
        intro h1
        have hk0 : Multiplicative.toAdd (f c) ≠ 0 := by
          intro h0
          apply hc
          rw [show f c = Multiplicative.ofAdd (Multiplicative.toAdd (f c)) from rfl, h0]
          rfl
        have hkpos : 0 < (Multiplicative.toAdd (f c)).val := by
          rw [Nat.pos_iff_ne_zero]
          intro h
          exact hk0 ((ZMod.val_eq_zero _).mp h)
        have hklt : (Multiplicative.toAdd (f c)).val < 3 := ZMod.val_lt _
        have hdvd : orderOf ((e c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∣
            (Multiplicative.toAdd (f c)).val :=
          orderOf_dvd_iff_pow_eq_one.mpr h1
        rw [hord] at hdvd
        omega
      have hfix : ∀ x ∈ U c, ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V) x = x → x = 0 := by
        intro x hx hxfix
        have hx' : x ∈ fixedSpace
            (((e c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ^
              (Multiplicative.toAdd (f c)).val) := by
          rw [mem_fixedSpace, ← hact f c x hx]
          exact hxfix
        rw [fixedSpace_eq_of_mem_zpowers hp hord (Subgroup.npow_mem_zpowers _ _) hne1,
          hF.fixedSpace_eq_polarPerp c] at hx'
        exact (Submodule.disjoint_def.mp (isCompl_polarPerp (hF.nondeg c)).disjoint) x hx hx'
      have hmaps : ∀ x ∈ U c, (g - 1) x ∈ U c := by
        intro x hx
        rw [LinearMap.sub_apply, Module.End.one_apply, hgapply, hact f c x hx]
        exact (U c).sub_mem (pow_maps_to hF c _ x hx) hx
      set φ : Module.End K ↥(U c) := (g - 1).restrict hmaps with hφ
      have hφinj : Function.Injective φ := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨x, hx⟩ hx0
        have h1 : (g - 1) x = 0 := by
          have h2 := congrArg Subtype.val hx0
          simpa [hφ] using h2
        rw [LinearMap.sub_apply, Module.End.one_apply] at h1
        have h2 : g x = x := sub_eq_zero.mp h1
        exact Subtype.ext (hfix x hx (by rw [← hgapply x]; exact h2))
      have hφsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.mp hφinj
      have hgO : ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q := by
        have hle : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
          rw [orthDerived]
          exact (Subgroup.commutator_le_sup _ _).trans (sup_idem _).le
        exact hle (τ f).2
      have hvinv : (((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V)).symm v = v := by
        apply ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V).injective
        rw [LinearEquiv.apply_symm_apply, hv]
      refine mem_polarPerp_iff.mpr fun m hm => ?_
      obtain ⟨⟨x, hx⟩, hxm⟩ := hφsurj ⟨m, hm⟩
      have hm' : g x - x = m := by
        have h2 := congrArg Subtype.val hxm
        simpa [hφ, LinearMap.restrict_apply, LinearMap.sub_apply] using h2
      have hpol : polar Q (g x) v = polar Q x v := by
        have h3 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO x
          ((((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V)).symm v)
        rw [LinearEquiv.apply_symm_apply, hvinv] at h3
        rw [hgapply x]
        exact h3
      rw [← hm', QuadraticMap.polar_sub_left, hpol, sub_self]
    have hsup : ∀ s : Finset (Fin 4), s ⊆ S → v ∈ polarPerp Q (s.sup U) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro _
          refine mem_polarPerp_iff.mpr fun y hy => ?_
          rw [Finset.sup_empty] at hy
          rw [Submodule.mem_bot] at hy
          rw [hy]
          exact QuadraticMap.polar_zero_left Q v
      | insert a s ha ih =>
          intro hs
          rw [Finset.sup_insert]
          refine mem_polarPerp_iff.mpr fun y hy => ?_
          rcases Submodule.mem_sup.mp hy with ⟨y1, hy1, y2, hy2, rfl⟩
          rw [QuadraticMap.polar_add_left]
          have haS : f a ≠ 1 := by simpa [hS] using hs (Finset.mem_insert_self a s)
          have h1 : polar Q y1 v = 0 :=
            mem_polarPerp_iff.mp (hperpc a haS) y1 hy1
          have h2 : polar Q y2 v = 0 :=
            mem_polarPerp_iff.mp (ih fun c hc => hs (Finset.mem_insert_of_mem hc)) y2 hy2
          rw [h1, h2, add_zero]
    rw [← Finset.sup_eq_iSup]
    exact hsup S (subset_refl S)
  ·
    intro hv
    rw [mem_fixedSpace]
    have hfac : ∀ c : Fin 4,
        ((τ (Pi.mulSingle c (f c)) : ↥(orthDerived Q)) : V ≃ₗ[K] V) v = v := by
      intro c
      by_cases hc : f c = 1
      · rw [hc, Pi.mulSingle_one, map_one]
        rfl
      · have hcS : c ∈ S := by simp [hS, hc]
        have hvperp : v ∈ polarPerp Q (U c) :=
          mem_polarPerp_iff.mpr fun y hy =>
            mem_polarPerp_iff.mp hv y (le_iSup₂ (f := fun c (_ : c ∈ S) => U c) c hcS hy)
        rw [tau_mulSingle_apply hτ c (f c), Subgroup.coe_pow]
        exact pow_apply_eq_self (hF.apply_of_perp c v hvperp) _
    have hprod : ∀ s : Finset (Fin 4), (∀ c ∈ s,
        ((τ (Pi.mulSingle c (f c)) : ↥(orthDerived Q)) : V ≃ₗ[K] V) v = v) →
        ((τ (s.prod fun c => Pi.mulSingle c (f c)) : ↥(orthDerived Q)) : V ≃ₗ[K] V) v = v := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | insert a s ha ih =>
          intro h
          rw [Finset.prod_insert ha, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
            ih fun c hc => h c (Finset.mem_insert_of_mem hc)]
          exact h a (Finset.mem_insert_self a s)
    have hfprod : f = S.prod (fun c => Pi.mulSingle c (f c)) := by
      funext j
      rw [Finset.prod_apply]
      by_cases hj : j ∈ S
      · rw [Finset.prod_eq_single j]
        · rw [Pi.mulSingle_apply, if_pos rfl]
        · intro c _ hcj
          rw [Pi.mulSingle_apply, if_neg (fun h => hcj h.symm)]
        · intro hj'
          exact absurd hj hj'
      · have hfj : f j = 1 := by simpa [hS] using hj
        rw [hfj]
        refine (Finset.prod_eq_one fun c hc => ?_).symm
        rw [Pi.mulSingle_apply, if_neg]
        exact fun h => hj (h ▸ hc)
    rw [hfprod]
    exact hprod S fun c hc => hfac c

public theorem finrank_fixedSpace_tau (hF : IsPlaneFrame Q 3 U e E) (hp : Nat.Prime 3)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 2 * 4)
    {τ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥(orthDerived Q)}
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e c)
    (hact : ∀ f c, ∀ x ∈ U c,
      ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V) x =
        (((e c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ^ (Multiplicative.toAdd (f c)).val) x)
    (f : Fin 4 → Multiplicative (ZMod 3)) :
    Module.finrank K (fixedSpace ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V)) =
      2 * (Finset.univ.filter (fun c => f c = 1)).card := by
  classical
  have hfilter : (Finset.univ.filter (fun c => ¬ f c ≠ 1)) =
      (Finset.univ.filter (fun c => f c = 1)) := by
    refine Finset.filter_congr ?_
    intro c _
    exact not_not
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4))) (p := fun c => f c ≠ 1)
  rw [hfilter] at hcard
  have hcardU : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
  rw [fixedSpace_tau_eq_polarPerp hF hp hτ hact f, finrank_polarPerp hQ, hdim,
    hF.toIsPlaneSystem.finrank_biSup]
  omega

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

open CFSG.StandardType

public theorem six_le_card_fix_omPlusRefl (f : Fin 4 → Multiplicative (ZMod 3))
    (hf : (Finset.univ.filter (fun a => f a = 1)).card = 0 ∨
      (Finset.univ.filter (fun a => f a = 1)).card = 3) :
    6 ≤ (Finset.univ.filter (fun y : OmPlusIdx 4 => omPlusRefl 3 y f = f)).card := by
  revert hf
  revert f
  decide +kernel

end CFSG.StandardType.E6QTwo

end
