module

import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.StandardType.ZS.Subquotient
public import CFSG.LocalAnalysis.StandardType.ZS.Support

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem movedSpace_eq_ker_add_one_of_mul_self {K : Type*} [Field K] {E : Type*}
    [AddCommGroup E] [Module K E] {t : E ≃ₗ[K] E} (h2 : (2 : K) ≠ 0) (ht : t * t = 1) :
    HardMathSupport.Kantor79.movedSpace t = LinearMap.ker ((t : E →ₗ[K] E) + 1) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub]
    have htt : (t : E →ₗ[K] E) ((t : E →ₗ[K] E) v) = v := by
      have h := congrArg (fun e : E ≃ₗ[K] E => e v) ht
      simpa [LinearEquiv.mul_apply] using h
    rw [htt]
    abel
  · intro hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hx
    refine ⟨-((2 : K)⁻¹) • x, ?_⟩
    change (t : E →ₗ[K] E) (-((2 : K)⁻¹) • x) - (-((2 : K)⁻¹) • x) = x
    rw [map_smul, hx]
    have hsum : ((2 : K)⁻¹ + (2 : K)⁻¹) = 1 := by
      rw [← two_mul]
      exact mul_inv_cancel₀ h2
    have h1 : (-((2 : K)⁻¹)) • (-x) = (2 : K)⁻¹ • x := by simp
    have h2' : (-((2 : K)⁻¹)) • x = -((2 : K)⁻¹ • x) := by simp
    rw [h1, h2', sub_neg_eq_add, ← add_smul, hsum, one_smul]

private theorem closure_sub_mem {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
    {S : Set (E ≃ₗ[K] E)} {X : Submodule K E} (hS : ∀ t ∈ S, ∀ v, t v - v ∈ X) :
    ∀ g ∈ Subgroup.closure S, ∀ v, g v - v ∈ X := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht => exact hS t ht
  | one => intro v; simp
  | mul a b _ _ iha ihb =>
      intro v
      rw [LinearEquiv.mul_apply]
      rw [show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
      exact X.add_mem (iha (b v)) (ihb v)
  | inv a _ iha =>
      intro v
      have h1 := iha (a⁻¹ v)
      have h2 : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
        rw [show a (a⁻¹ v) = v from LinearEquiv.apply_symm_apply a v]
        abel
      rw [h2]
      exact X.neg_mem h1

private theorem pow_prime_eq_self_of_invol {G : Type*} [Group G] {u : G} {n : ℕ}
    (hmod : n ≡ 1 [MOD 2]) (hu : u * u = 1) : u ^ n = u := by
  have := pow_eq_pow_of_modEq hmod (show u ^ 2 = 1 by rwa [pow_two])
  simpa using this

private abbrev negV (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  HardMathSupport.Kantor79.commutatorSpace F

private abbrev negC (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U := centralizerSpace F

private abbrev negW (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U := negV F ⊓ negC F

private abbrev negR (F : Subgroup (U ≃ₗ[ZMod p] U)) : Set (U ≃ₗ[ZMod p] U) :=
  {t | t ∈ F ∧ IsRefl p t}

private abbrev negS (F : Subgroup (U ≃ₗ[ZMod p] U)) (E : Submodule (ZMod p) U) :
    Set (U ≃ₗ[ZMod p] U) := {t | t ∈ F ∧ IsRefl p t ∧ HardMathSupport.Kantor79.movedSpace t ≤ E}

private structure NegSetup (F : Subgroup (U ≃ₗ[ZMod p] U)) (l m : ℕ) where
  hp : p ≠ 2
  hVF : Module.finrank (ZMod p) (negV F) = l + 1
  hWfin : Module.finrank (ZMod p) ↥(negW F) = 1
  z : U ≃ₗ[ZMod p] U
  hzF : z ∈ F
  hneg_z : ∀ v ∈ negV F, z v + v ∈ negC F
  h2 : (2 : ZMod p) ≠ 0
  hm : p = 2 * m + 1
  hpmod : p ≡ 1 [MOD 2]
  hVinv : ∀ g ∈ F, ∀ v ∈ negV F, g v ∈ negV F
  hVmap : ∀ g ∈ F, (negV F).map (g : U →ₗ[ZMod p] U) = negV F
  hCfix : ∀ g ∈ F, ∀ v ∈ negC F, g v = v
  hWfix : ∀ g ∈ F, ∀ v ∈ negW F, g v = v
  hWinv : ∀ g ∈ F, ∀ v ∈ negW F, g v ∈ negW F
  hWmap : ∀ g ∈ F, (negW F).map (g : U →ₗ[ZMod p] U) = negW F
  hsubV : ∀ g ∈ F, ∀ v, g v - v ∈ negV F

private theorem negSetup_exists (hp : p ≠ 2) {F : Subgroup (U ≃ₗ[ZMod p] U)} {l m : ℕ}
    (hVF : Module.finrank (ZMod p) (negV F) = l + 1)
    (hWfin : Module.finrank (ZMod p) ↥(negW F) = 1)
    (hneg : ∃ z ∈ F, ∀ v ∈ negV F, z v + v ∈ negC F) (hm : p = 2 * m + 1) :
    Nonempty (NegSetup F l m) := by
  obtain ⟨z, hzF, hneg_z⟩ := hneg
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hpmod : p ≡ 1 [MOD 2] := by rw [Nat.ModEq]; omega
  have hVinv : ∀ g ∈ F, ∀ v ∈ negV F, g v ∈ negV F :=
    fun g hg v hv => apply_mem_commutatorSpace hg hv
  have hVmap : ∀ g ∈ F, (negV F).map (g : U →ₗ[ZMod p] U) = negV F :=
    fun g hg => map_eq_self_of_invariant hVinv hg
  have hCfix : ∀ g ∈ F, ∀ v ∈ negC F, g v = v :=
    fun g hg v hv => (mem_centralizerSpace.mp hv) g hg
  have hWfix : ∀ g ∈ F, ∀ v ∈ negW F, g v = v := fun g hg v hv => hCfix g hg v hv.2
  have hWinv : ∀ g ∈ F, ∀ v ∈ negW F, g v ∈ negW F := by
    intro g hg v hv
    exact ⟨hVinv g hg v hv.1, by rw [hCfix g hg v hv.2]; exact hv.2⟩
  have hWmap : ∀ g ∈ F, (negW F).map (g : U →ₗ[ZMod p] U) = negW F :=
    fun g hg => map_eq_self_of_invariant hWinv hg
  have hsubV : ∀ g ∈ F, ∀ v, g v - v ∈ negV F :=
    fun g hg v => Submodule.subset_span ⟨g, hg, v, rfl⟩
  exact ⟨⟨hp, hVF, hWfin, z, hzF, hneg_z, h2, hm, hpmod, hVinv, hVmap, hCfix, hWfix,
    hWinv, hWmap, hsubV⟩⟩

section

variable {F : Subgroup (U ≃ₗ[ZMod p] U)} {l m : ℕ} [Module.Finite (ZMod p) U]

private noncomputable def negPhi (D : NegSetup F l m) :
    F →* (Subquot (negW F) (negV F) ≃ₗ[ZMod p] Subquot (negW F) (negV F)) :=
  subquotHom F (negW F) (negV F) D.hWmap D.hVmap

private def negZ1 (D : NegSetup F l m) : F := ⟨D.z ^ p, F.pow_mem D.hzF p⟩

private def negY (D : NegSetup F l m) (σF : F) : F := (σF * negZ1 D) ^ p

private def negTau (D : NegSetup F l m) (σF : F) : F := negZ1 D * negY D σF

omit [Module.Finite (ZMod p) U] in
private theorem negCongruence (D : NegSetup F l m) (f g : F) :
    negPhi D f = negPhi D g ↔
      ∀ v ∈ negV F, (f : U ≃ₗ[ZMod p] U) v - (g : U ≃ₗ[ZMod p] U) v ∈ negW F := by
  change subquotHom F (negW F) (negV F) D.hWmap D.hVmap f =
      subquotHom F (negW F) (negV F) D.hWmap D.hVmap g ↔
    ∀ v ∈ negV F, (f : U ≃ₗ[ZMod p] U) v - (g : U ≃ₗ[ZMod p] U) v ∈ negW F
  constructor
  · intro h v hv
    have hk : subquotHom F (negW F) (negV F) D.hWmap D.hVmap (f * g⁻¹) = 1 := by
      rw [map_mul, map_inv, h]
      exact mul_inv_cancel _
    have hmem := (subquotEquiv_eq_one_iff (D.hWmap (f * g⁻¹) (f * g⁻¹).2)
      (D.hVmap (f * g⁻¹) (f * g⁻¹).2)).mp hk
    have hgv : (g : U ≃ₗ[ZMod p] U) v ∈ negV F := D.hVinv g g.2 v hv
    have := hmem ((g : U ≃ₗ[ZMod p] U) v) hgv
    simpa [LinearEquiv.mul_apply] using this
  · intro h
    have hk : subquotHom F (negW F) (negV F) D.hWmap D.hVmap (f * g⁻¹) = 1 := by
      change subquotEquiv (negW F) (negV F) (f * g⁻¹) (D.hWmap (f * g⁻¹) (f * g⁻¹).2)
        (D.hVmap (f * g⁻¹) (f * g⁻¹).2) = 1
      rw [subquotEquiv_eq_one_iff]
      intro w hw
      have hgw : (g : U ≃ₗ[ZMod p] U)⁻¹ w ∈ negV F := by
        have hm : w ∈ (negV F).map (g : U →ₗ[ZMod p] U) := by rw [D.hVmap g g.2]; exact hw
        obtain ⟨u, hu, hgu⟩ := Submodule.mem_map.mp hm
        have : (g : U ≃ₗ[ZMod p] U)⁻¹ w = u := by rw [← hgu]; simp
        rw [this]; exact hu
      have := h ((g : U ≃ₗ[ZMod p] U)⁻¹ w) hgw
      simpa [LinearEquiv.mul_apply] using this
    rw [map_mul, map_inv] at hk
    exact mul_inv_eq_one.mp hk

omit [Module.Finite (ZMod p) U] in
private theorem negSq_fix (D : NegSetup F l m) : ∀ v ∈ negV F, D.z (D.z v) = v := by
  intro v hv
  have h1 : D.z v + v ∈ negC F := D.hneg_z v hv
  have h2' : D.z (D.z v + v) = D.z v + v := (mem_centralizerSpace.mp h1) D.z D.hzF
  rw [map_add] at h2'
  have h3 : D.z (D.z v) + D.z v = v + D.z v := by rw [h2', add_comm (D.z v) v]
  exact add_right_cancel h3

omit [Module.Finite (ZMod p) U] in
private theorem negPowSq (D : NegSetup F l m) : (D.z ^ p) * (D.z ^ p) = 1 := by
  have h2fix := negSq_fix D
  have hz2w : ∀ w ∈ negV F, ((D.z : U ≃ₗ[ZMod p] U) ^ 2) w = w := by
    intro w hw; rw [pow_two, LinearEquiv.mul_apply]; exact h2fix w hw
  have hker : negPhi D ⟨(D.z : U ≃ₗ[ZMod p] U) ^ 2, F.pow_mem D.hzF 2⟩ = 1 := by
    have h := (negCongruence D ⟨(D.z : U ≃ₗ[ZMod p] U) ^ 2, F.pow_mem D.hzF 2⟩
      (1 : F)).mpr (fun w hw => by
        have hw' := hz2w w hw
        simp [hw'])
    simpa using h
  have hzp2 : (⟨(D.z : U ≃ₗ[ZMod p] U) ^ 2, F.pow_mem D.hzF 2⟩ : F) ^ p = 1 :=
    pow_prime_eq_one_of_subquotHom_eq_one D.hp D.hWmap D.hVmap D.hWfix D.hsubV hker
  have h := congrArg (fun x : F => (x : U ≃ₗ[ZMod p] U)) hzp2
  have h' : ((D.z : U ≃ₗ[ZMod p] U) ^ 2) ^ p = 1 := by simpa using h
  have hpow : ((D.z : U ≃ₗ[ZMod p] U) ^ 2) ^ p =
      (D.z : U ≃ₗ[ZMod p] U) ^ p * (D.z : U ≃ₗ[ZMod p] U) ^ p := by
    rw [← pow_mul, ← pow_add, two_mul]
  rwa [hpow] at h'

omit [Module.Finite (ZMod p) U] in
private theorem negPowApply (D : NegSetup F l m) : ∀ v ∈ negV F, (D.z ^ p) v = D.z v := by
  have h2fix := negSq_fix D
  have hz2w : ∀ w ∈ negV F, ((D.z : U ≃ₗ[ZMod p] U) ^ 2) w = w := by
    intro w hw; rw [pow_two, LinearEquiv.mul_apply]; exact h2fix w hw
  have hpow_fix : ∀ k, ∀ v ∈ negV F, (((D.z : U ≃ₗ[ZMod p] U) ^ 2) ^ k) v = v := by
    intro k
    induction k with
    | zero => intro v _; simp
    | succ k ih =>
        intro v hv
        rw [pow_succ, LinearEquiv.mul_apply]
        rw [ih (((D.z : U ≃ₗ[ZMod p] U) ^ 2) v) (by rw [hz2w v hv]; exact hv)]
        exact hz2w v hv
  intro v hv
  have hpz : (D.z : U ≃ₗ[ZMod p] U) ^ p = (D.z : U ≃ₗ[ZMod p] U) ^ (2 * m + 1) :=
    congrArg (fun n => (D.z : U ≃ₗ[ZMod p] U) ^ n) D.hm
  have hpow : (D.z : U ≃ₗ[ZMod p] U) ^ p = ((D.z : U ≃ₗ[ZMod p] U) ^ 2) ^ m * D.z := by
    rw [hpz, pow_add, pow_one, ← pow_mul]
  calc (D.z ^ p) v = ((D.z : U ≃ₗ[ZMod p] U) ^ p) v := rfl
    _ = ((((D.z : U ≃ₗ[ZMod p] U) ^ 2) ^ m * D.z)) v := by rw [hpow]
    _ = (((D.z : U ≃ₗ[ZMod p] U) ^ 2) ^ m) (D.z v) := by rw [LinearEquiv.mul_apply]
    _ = D.z v := hpow_fix m (D.z v) (D.hVinv D.z D.hzF v hv)

omit [Module.Finite (ZMod p) U] in
private theorem negPowAddMem (D : NegSetup F l m) :
    ∀ v ∈ negV F, (D.z ^ p) v + v ∈ negW F := by
  intro v hv
  exact ⟨(negV F).add_mem (D.hVinv (D.z ^ p) (F.pow_mem D.hzF p) v hv) hv,
    by rw [negPowApply D v hv]; exact D.hneg_z v hv⟩

omit [Module.Finite (ZMod p) U] in
private theorem negE_eq (D : NegSetup F l m) (hz1_inv : (D.z ^ p) * (D.z ^ p) = 1) :
    HardMathSupport.Kantor79.movedSpace (D.z ^ p) =
      LinearMap.ker (((D.z ^ p : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1) :=
  movedSpace_eq_ker_add_one_of_mul_self D.h2 hz1_inv

omit [Module.Finite (ZMod p) U] in
private theorem negE_inf_W (D : NegSetup F l m) (hz1_inv : (D.z ^ p) * (D.z ^ p) = 1) :
    HardMathSupport.Kantor79.movedSpace (D.z ^ p) ⊓ negW F = ⊥ := by
  have hE_eq := negE_eq D hz1_inv
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  obtain ⟨hxE, hxW⟩ := Submodule.mem_inf.mp hx
  have hneg : (D.z ^ p) x = -x := by
    have hx' := hxE
    rw [hE_eq, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hx'
    simpa using add_eq_zero_iff_eq_neg.mp hx'
  have hfix : (D.z ^ p) x = x := D.hCfix (D.z ^ p) (F.pow_mem D.hzF p) x hxW.2
  have h2x : (2 : ZMod p) • x = 0 := by
    have hxneg : x = -x := hfix.symm.trans hneg
    rw [two_smul]; nth_rewrite 1 [hxneg]; rw [neg_add_cancel]
  exact (smul_eq_zero.mp h2x).resolve_left D.h2

omit [Module.Finite (ZMod p) U] in
private theorem neg_ker_sub_le_W (D : NegSetup F l m) :
    negV F ⊓ LinearMap.ker (((D.z ^ p : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) ≤ negW F := by
  intro x hx
  obtain ⟨hxV, hxker⟩ := Submodule.mem_inf.mp hx
  have hxfix : (D.z ^ p) x = x := by
    have hx' := hxker
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx'
    simpa using hx'
  have h2x : (2 : ZMod p) • x ∈ negW F := by
    have h := negPowAddMem D x hxV
    have h2x' : (2 : ZMod p) • x = (D.z ^ p) x + x := by rw [two_smul, hxfix]
    rwa [← h2x'] at h
  exact ((negW F).smul_mem_iff D.h2).mp h2x

private theorem negE_finrank_le (D : NegSetup F l m) (hz1_inv : (D.z ^ p) * (D.z ^ p) = 1) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace (D.z ^ p)) ≤ l := by
  have hE_le_V : HardMathSupport.Kantor79.movedSpace (D.z ^ p) ≤ negV F :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (F.pow_mem D.hzF p)
  have hE_inf_W := negE_inf_W D hz1_inv
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.movedSpace (D.z ^ p)) (negW F)
  rw [hE_inf_W, finrank_bot, add_zero, D.hWfin] at hsum
  have hsup_le : HardMathSupport.Kantor79.movedSpace (D.z ^ p) ⊔ negW F ≤ negV F :=
    sup_le hE_le_V inf_le_left
  have hfin_sup : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.movedSpace (D.z ^ p) ⊔ negW F) ≤ l + 1 :=
    (Submodule.finrank_mono hsup_le).trans_eq D.hVF
  omega

omit [Module.Finite (ZMod p) U] in
private theorem negClosure_le_F (E : Submodule (ZMod p) U) :
    Subgroup.closure (negS F E) ≤ F :=
  (Subgroup.closure_le F).mpr (fun _ ht => ht.1)

omit [Module.Finite (ZMod p) U] in
private theorem negClosure_reflGen (E : Submodule (ZMod p) U) :
    ReflGen p (Subgroup.closure (negS F E)) := by
  change Subgroup.closure (negS F E) =
    Subgroup.closure {t | t ∈ Subgroup.closure (negS F E) ∧ IsRefl p t}
  refine le_antisymm ?_ ?_
  · apply (Subgroup.closure_le _).mpr
    rintro t ⟨htF, htR, htE⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨htF, htR, htE⟩, htR⟩
  · apply (Subgroup.closure_le _).mpr
    rintro t ⟨htF₁, _⟩
    exact htF₁

omit [Module.Finite (ZMod p) U] in
private theorem negClosure_commutator_le (E : Submodule (ZMod p) U) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (negS F E)) ≤ E := by
  rw [commutatorSpace_le_iff]
  intro g hg v
  exact closure_sub_mem (X := E) (fun t ht v => ht.2.2 ⟨v, by simp⟩) g hg v

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_phi (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) (hσmod : ¬ ∀ v ∈ negV F, σ v - v ∈ negW F) :
    IsRefl p (negPhi D ⟨σ, hσF⟩) := by
  have hbar : subquotEquiv (negW F) (negV F) σ (D.hWmap σ hσF) (D.hVmap σ hσF) =
      negPhi D ⟨σ, hσF⟩ := rfl
  rcases isRefl_subquotEquiv_or_eq_one hσ_refl (D.hWmap σ hσF) (D.hVmap σ hσF) with
    hrefl | hone
  · rwa [hbar] at hrefl
  · exfalso
    have hcon : negPhi D ⟨σ, hσF⟩ = 1 := by rw [← hbar]; exact hone
    exact hσmod (fun v hv => (negCongruence D ⟨σ, hσF⟩ (1 : F)).mp
      (by rw [map_one]; exact hcon) v hv)

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_rel (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F) :
    ∀ v ∈ negV F, ((D.z ^ p) * σ * (D.z ^ p)) v - σ v ∈ negW F := by
  intro v hv
  have hz1F : D.z ^ p ∈ F := F.pow_mem D.hzF p
  have h1 : (D.z ^ p) (σ ((D.z ^ p) v)) + σ ((D.z ^ p) v) ∈ negW F :=
    negPowAddMem D (σ ((D.z ^ p) v)) (D.hVinv σ hσF _ (D.hVinv (D.z ^ p) hz1F v hv))
  have h2w : σ ((D.z ^ p) v) + σ v ∈ negW F := by
    have h := negPowAddMem D v hv
    have := D.hWinv σ hσF ((D.z ^ p) v + v) h
    rwa [map_add] at this
  have hsub := (negW F).sub_mem h1 h2w
  have heq : ((D.z ^ p) (σ ((D.z ^ p) v)) + σ ((D.z ^ p) v)) -
      (σ ((D.z ^ p) v) + σ v) = (D.z ^ p) (σ ((D.z ^ p) v)) - σ v := by abel
  rw [heq] at hsub
  simpa [LinearEquiv.mul_apply] using hsub

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_z1σ (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F) :
    negPhi D (negZ1 D) * negPhi D ⟨σ, hσF⟩ * negPhi D (negZ1 D) = negPhi D ⟨σ, hσF⟩ := by
  rw [← map_mul, ← map_mul]
  exact (negCongruence D _ _).mpr (fun v hv => by
    simpa [negZ1, LinearEquiv.mul_apply] using negRefl_rel D hσF v hv)

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_comm (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F) :
    negPhi D (negZ1 D) * negPhi D ⟨σ, hσF⟩ = negPhi D ⟨σ, hσF⟩ * negPhi D (negZ1 D) := by
  have hz_inv : negPhi D (negZ1 D) * negPhi D (negZ1 D) = 1 := by
    rw [← map_mul, show negZ1 D * negZ1 D = 1 from Subtype.ext (negPowSq D), map_one]
  have h := congrArg (fun x => x * negPhi D (negZ1 D)) (negRefl_z1σ D hσF)
  simpa [mul_assoc, hz_inv] using h

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_u_inv (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) :
    negPhi D (⟨σ, hσF⟩ * negZ1 D) * negPhi D (⟨σ, hσF⟩ * negZ1 D) = 1 := by
  have hσF_mul : (⟨σ, hσF⟩ : F) * ⟨σ, hσF⟩ = 1 := Subtype.ext (by simpa using hσ_refl.1)
  have hzF_mul : negZ1 D * negZ1 D = 1 := Subtype.ext (negPowSq D)
  have hφσ_inv : negPhi D ⟨σ, hσF⟩ * negPhi D ⟨σ, hσF⟩ = 1 := by
    rw [← map_mul, hσF_mul, map_one]
  have hφz_inv : negPhi D (negZ1 D) * negPhi D (negZ1 D) = 1 := by
    rw [← map_mul, hzF_mul, map_one]
  have hcomm := negRefl_comm D hσF
  rw [map_mul]
  calc (negPhi D ⟨σ, hσF⟩ * negPhi D (negZ1 D)) * (negPhi D ⟨σ, hσF⟩ * negPhi D (negZ1 D))
      = negPhi D ⟨σ, hσF⟩ * (negPhi D (negZ1 D) * negPhi D ⟨σ, hσF⟩) * negPhi D (negZ1 D) := by
        group
    _ = negPhi D ⟨σ, hσF⟩ * (negPhi D ⟨σ, hσF⟩ * negPhi D (negZ1 D)) * negPhi D (negZ1 D) := by
        rw [hcomm]
    _ = (negPhi D ⟨σ, hσF⟩ * negPhi D ⟨σ, hσF⟩) * (negPhi D (negZ1 D) * negPhi D (negZ1 D)) := by
        group
    _ = 1 := by rw [hφσ_inv, hφz_inv, one_mul]

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_y_inv (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) : negY D ⟨σ, hσF⟩ * negY D ⟨σ, hσF⟩ = 1 := by
  have hu_inv := negRefl_u_inv D hσF hσ_refl
  have hφu2 : negPhi D ((⟨σ, hσF⟩ * negZ1 D : F) ^ 2) = 1 := by rw [map_pow, pow_two, hu_inv]
  have hk : ((⟨σ, hσF⟩ * negZ1 D : F) ^ 2) ^ p = 1 :=
    pow_prime_eq_one_of_subquotHom_eq_one D.hp D.hWmap D.hVmap D.hWfix D.hsubV hφu2
  have hpow_eq : ((⟨σ, hσF⟩ * negZ1 D : F) ^ 2) ^ p =
      ((⟨σ, hσF⟩ * negZ1 D : F) ^ p) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [show negY D ⟨σ, hσF⟩ = (⟨σ, hσF⟩ * negZ1 D : F) ^ p from rfl, ← pow_two, ← hpow_eq]
  exact hk

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_y_comm (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) : negZ1 D * negY D ⟨σ, hσF⟩ = negY D ⟨σ, hσF⟩ * negZ1 D := by
  have hσF_mul : (⟨σ, hσF⟩ : F) * ⟨σ, hσF⟩ = 1 := Subtype.ext (by simpa using hσ_refl.1)
  have hzF_mul : negZ1 D * negZ1 D = 1 := Subtype.ext (negPowSq D)
  have hy_inv := negRefl_y_inv D hσF hσ_refl
  have hzF_inv : (negZ1 D)⁻¹ = negZ1 D := inv_eq_of_mul_eq_one_left hzF_mul
  have hconj : negZ1 D * negY D ⟨σ, hσF⟩ * negZ1 D =
      (negZ1 D * (⟨σ, hσF⟩ * negZ1 D) * negZ1 D) ^ p := by
    have h := (conj_pow (a := negZ1 D) (b := (⟨σ, hσF⟩ * negZ1 D : F)) (i := p)).symm
    rwa [hzF_inv] at h
  have hz1u : negZ1 D * (⟨σ, hσF⟩ * negZ1 D) * negZ1 D = negZ1 D * ⟨σ, hσF⟩ := by
    calc negZ1 D * (⟨σ, hσF⟩ * negZ1 D) * negZ1 D =
          negZ1 D * ⟨σ, hσF⟩ * (negZ1 D * negZ1 D) := by group
      _ = negZ1 D * ⟨σ, hσF⟩ := by rw [hzF_mul, mul_one]
  have hzu_inv : negZ1 D * ⟨σ, hσF⟩ = (⟨σ, hσF⟩ * negZ1 D : F)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hσF_mul, hzF_inv]
  have hfin : negZ1 D * negY D ⟨σ, hσF⟩ * negZ1 D = negY D ⟨σ, hσF⟩ := by
    rw [hconj, hz1u, hzu_inv, inv_pow]
    exact inv_eq_of_mul_eq_one_left hy_inv
  calc negZ1 D * negY D ⟨σ, hσF⟩
      = negZ1 D * negY D ⟨σ, hσF⟩ * (negZ1 D * negZ1 D) := by rw [hzF_mul, mul_one]
    _ = (negZ1 D * negY D ⟨σ, hσF⟩ * negZ1 D) * negZ1 D := by group
    _ = negY D ⟨σ, hσF⟩ * negZ1 D := by rw [hfin]

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_y_phi (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) : negPhi D (negY D ⟨σ, hσF⟩) = negPhi D (⟨σ, hσF⟩ * negZ1 D) := by
  have hu_inv := negRefl_u_inv D hσF hσ_refl
  rw [show negY D ⟨σ, hσF⟩ = (⟨σ, hσF⟩ * negZ1 D : F) ^ p from rfl, map_pow]
  exact pow_prime_eq_self_of_invol D.hpmod hu_inv

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_tau_inv (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) : negTau D ⟨σ, hσF⟩ * negTau D ⟨σ, hσF⟩ = 1 := by
  have hzF_mul : negZ1 D * negZ1 D = 1 := Subtype.ext (negPowSq D)
  have hy_inv := negRefl_y_inv D hσF hσ_refl
  have hz1y := negRefl_y_comm D hσF hσ_refl
  show (negZ1 D * negY D ⟨σ, hσF⟩) * (negZ1 D * negY D ⟨σ, hσF⟩) = 1
  calc (negZ1 D * negY D ⟨σ, hσF⟩) * (negZ1 D * negY D ⟨σ, hσF⟩)
      = negZ1 D * (negY D ⟨σ, hσF⟩ * negZ1 D) * negY D ⟨σ, hσF⟩ := by group
    _ = negZ1 D * (negZ1 D * negY D ⟨σ, hσF⟩) * negY D ⟨σ, hσF⟩ := by rw [← hz1y]
    _ = (negZ1 D * negZ1 D) * (negY D ⟨σ, hσF⟩ * negY D ⟨σ, hσF⟩) := by group
    _ = 1 := by rw [hzF_mul, hy_inv, one_mul]

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_tau_phi (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) : negPhi D (negTau D ⟨σ, hσF⟩) = negPhi D ⟨σ, hσF⟩ := by
  have hφy := negRefl_y_phi D hσF hσ_refl
  have hφu_eq : negPhi D (⟨σ, hσF⟩ * negZ1 D) = negPhi D ⟨σ, hσF⟩ * negPhi D (negZ1 D) :=
    map_mul _ _ _
  have hz1σ := negRefl_z1σ D hσF
  show negPhi D (negZ1 D * negY D ⟨σ, hσF⟩) = negPhi D ⟨σ, hσF⟩
  rw [map_mul, hφy, hφu_eq, ← mul_assoc, hz1σ]

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_tau_refl (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) (hσmod : ¬ ∀ v ∈ negV F, σ v - v ∈ negW F) :
    IsRefl p ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) := by
  have hτ_inv := negRefl_tau_inv D hσF hσ_refl
  have hφτ := negRefl_tau_phi D hσF hσ_refl
  have hφσ_refl := negRefl_phi D hσF hσ_refl hσmod
  have hτ_inv_ambient : ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) *
      ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) = 1 := by
    have h := congrArg (fun x : F => (x : U ≃ₗ[ZMod p] U)) hτ_inv
    simpa using h
  have hφτ_refl : IsRefl p (negPhi D (negTau D ⟨σ, hσF⟩)) := by rw [hφτ]; exact hφσ_refl
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace
      ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U)) = 1 :=
    finrank_movedSpace_of_isRefl_subquot D.hp hτ_inv_ambient
      (D.hWmap (negTau D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) (negTau D ⟨σ, hσF⟩).2)
      (D.hVmap (negTau D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) (negTau D ⟨σ, hσF⟩).2)
      (D.hWfix (negTau D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) (negTau D ⟨σ, hσF⟩).2)
      (D.hsubV (negTau D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) (negTau D ⟨σ, hσF⟩).2) hφτ_refl.2
  exact ⟨hτ_inv_ambient, hfin⟩

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_L_inv (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) :
    ∀ x ∈ HardMathSupport.Kantor79.movedSpace ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U),
      (D.z ^ p) x ∈ HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) := by
  have hz1_inv := negPowSq D
  have hz1y := negRefl_y_comm D hσF hσ_refl
  rintro x ⟨v, rfl⟩
  have hcomm_ambient : (D.z ^ p) * ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) =
      ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) * (D.z ^ p) := by
    have h1 : (D.z ^ p) * ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) =
        (negY D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) := by
      show (D.z ^ p) * ((D.z ^ p) * (negY D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U)) =
        (negY D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U)
      rw [← mul_assoc, hz1_inv, one_mul]
    have h2 : ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) * (D.z ^ p) =
        (negY D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) := by
      have hy : (negY D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) * (D.z ^ p) =
          (D.z ^ p) * (negY D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U) := by
        have := congrArg (fun x : F => (x : U ≃ₗ[ZMod p] U)) hz1y
        simpa [negZ1] using this.symm
      show ((D.z ^ p) * (negY D ⟨σ, hσF⟩ : U ≃ₗ[ZMod p] U)) * (D.z ^ p) = _
      rw [mul_assoc, hy, ← mul_assoc, hz1_inv, one_mul]
    rw [h1, h2]
  have hz1τ : (D.z ^ p) (((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) v) =
      ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) ((D.z ^ p) v) := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hcomm_ambient
    simpa [LinearEquiv.mul_apply] using this
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  change (D.z ^ p) (((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) v) - (D.z ^ p) v ∈
    HardMathSupport.Kantor79.movedSpace ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U)
  rw [hz1τ]
  exact ⟨(D.z ^ p) v, by simp⟩

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_scalar (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) (hσmod : ¬ ∀ v ∈ negV F, σ v - v ∈ negW F)
    (hL_inv : ∀ x ∈ HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U),
      (D.z ^ p) x ∈ HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U)) :
    ∃ (a : U) (c : ZMod p), a ∈ HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) ∧ a ≠ 0 ∧
      HardMathSupport.Kantor79.movedSpace ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) =
        Submodule.span (ZMod p) {a} ∧ (D.z ^ p) a = c • a ∧ c * c = 1 := by
  have hfin_τ := (negRefl_tau_refl D hσF hσ_refl hσmod).2
  have hLne : HardMathSupport.Kantor79.movedSpace
      ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) ≠ ⊥ := by
    intro hbot
    have hfin_τ' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U)) = 1 := hfin_τ
    rw [hbot, finrank_bot] at hfin_τ'
    exact Nat.zero_ne_one hfin_τ'
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  have hspan : HardMathSupport.Kantor79.movedSpace ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) =
      Submodule.span (ZMod p) {a} := eq_span_singleton_of_mem_of_finrank_eq_one hfin_τ ha ha0
  have hz1a_mem : (D.z ^ p) a ∈ Submodule.span (ZMod p) {a} := by
    rw [← hspan]; exact hL_inv a ha
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz1a_mem
  have hc' : (D.z ^ p) a = c • a := hc.symm
  have hcc : c * c = 1 := by
    have h2c : (D.z ^ p) ((D.z ^ p) a) = (c * c) • a := by rw [hc', map_smul, hc', smul_smul]
    have h1c : (D.z ^ p) ((D.z ^ p) a) = a := by
      have := congrArg (fun e : U ≃ₗ[ZMod p] U => e a) (negPowSq D)
      simpa [LinearEquiv.mul_apply] using this
    rw [h1c] at h2c
    have h3c : (c * c - 1) • a = 0 := by
      rw [sub_smul, one_smul]; nth_rewrite 2 [h2c]; rw [sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3c).resolve_right ha0)
  exact ⟨a, c, ha, ha0, hspan, hc', hcc⟩

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_L_le_E (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) (hσmod : ¬ ∀ v ∈ negV F, σ v - v ∈ negW F)
    (hL_inv : ∀ x ∈ HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U),
      (D.z ^ p) x ∈ HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U)) :
    HardMathSupport.Kantor79.movedSpace ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) ≤
      HardMathSupport.Kantor79.movedSpace (D.z ^ p) := by
  obtain ⟨a, c, ha, ha0, hspan, hc', hcc⟩ := negRefl_scalar D hσF hσ_refl hσmod hL_inv
  rcases sq_eq_one_iff.mp (show c ^ 2 = 1 by rw [pow_two]; exact hcc) with hc1 | hcneg
  · exfalso
    have ha_ker : a ∈ LinearMap.ker (((D.z ^ p : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      change (D.z ^ p) a = a
      rw [hc', hc1, one_smul]
    have haW : a ∈ negW F := neg_ker_sub_le_W D
      ⟨HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (negTau D ⟨σ, hσF⟩).2 ha, ha_ker⟩
    have hL_le_W : HardMathSupport.Kantor79.movedSpace
        ((negTau D ⟨σ, hσF⟩ : F) : U ≃ₗ[ZMod p] U) ≤ negW F := by
      rw [hspan]; exact Submodule.span_le.mpr (by rintro x rfl; exact haW)
    have hφτ1 : negPhi D (negTau D ⟨σ, hσF⟩) = 1 := by
      have h := (negCongruence D (negTau D ⟨σ, hσF⟩) (1 : F)).mpr (fun v hv => by
        simpa using hL_le_W ⟨v, by simp⟩)
      simpa using h
    have hφτ := negRefl_tau_phi D hσF hσ_refl
    rw [hφτ] at hφτ1
    exact hσmod (fun v hv => (negCongruence D ⟨σ, hσF⟩ (1 : F)).mp
      (by rw [map_one]; exact hφτ1) v hv)
  · have ha_ker : a ∈ LinearMap.ker (((D.z ^ p : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1) := by
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
      change (D.z ^ p) a = -a
      rw [hc', hcneg]; simp
    rw [negE_eq D (negPowSq D), hspan]
    exact Submodule.span_le.mpr (by rintro x rfl; exact ha_ker)

omit [Module.Finite (ZMod p) U] in
private theorem negRefl_lift (D : NegSetup F l m) {σ : U ≃ₗ[ZMod p] U} (hσF : σ ∈ F)
    (hσ_refl : IsRefl p σ) (hσmod : ¬ ∀ v ∈ negV F, σ v - v ∈ negW F) :
    ∃ τ ∈ F, IsRefl p τ ∧
      HardMathSupport.Kantor79.movedSpace τ ≤ HardMathSupport.Kantor79.movedSpace (D.z ^ p) ∧
      ∀ v ∈ negV F, τ v - σ v ∈ negW F := by
  have hτ_refl := negRefl_tau_refl D hσF hσ_refl hσmod
  have hL_inv := negRefl_L_inv D hσF hσ_refl
  have hL_le := negRefl_L_le_E D hσF hσ_refl hσmod hL_inv
  have hφτ := negRefl_tau_phi D hσF hσ_refl
  refine ⟨(negTau D ⟨σ, hσF⟩ : F), (negTau D ⟨σ, hσF⟩).2, hτ_refl, hL_le, ?_⟩
  intro v hv
  exact (negCongruence D (negTau D ⟨σ, hσF⟩) ⟨σ, hσF⟩).mp hφτ v hv

omit [Module.Finite (ZMod p) U] in
private theorem negRange_le {φ : F →* (Subquot (negW F) (negV F) ≃ₗ[ZMod p]
      Subquot (negW F) (negV F))} (E : Submodule (ZMod p) U) (hF : ReflGen p F)
    (hR_sub : ∀ (σ : U ≃ₗ[ZMod p] U) (hσ : σ ∈ negR F),
      φ ⟨σ, hσ.1⟩ ∈ Subgroup.map φ ((Subgroup.closure (negS F E)).subgroupOf F)) :
    φ.range ≤ Subgroup.map φ ((Subgroup.closure (negS F E)).subgroupOf F) := by
  have hgenF : Subgroup.closure {x : F | (x : U ≃ₗ[ZMod p] U) ∈ negR F} = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective F)
    rw [MonoidHom.map_closure]
    have hset : (F.subtype '' {x : F | (x : U ≃ₗ[ZMod p] U) ∈ negR F}) = negR F := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hx.1⟩, hx, rfl⟩
    rw [hset, ← hF, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hH' : (Subgroup.map φ ((Subgroup.closure (negS F E)).subgroupOf F)).comap φ = ⊤ := by
    rw [eq_top_iff, ← hgenF]
    apply (Subgroup.closure_le _).mpr
    rintro x hx
    change φ x ∈ Subgroup.map φ ((Subgroup.closure (negS F E)).subgroupOf F)
    have hx' : (⟨(x : U ≃ₗ[ZMod p] U), hx.1⟩ : F) = x := Subtype.ext rfl
    rw [← hx']
    exact hR_sub (x : U ≃ₗ[ZMod p] U) hx
  rintro y ⟨f, rfl⟩
  have hf : f ∈ (Subgroup.map φ ((Subgroup.closure (negS F E)).subgroupOf F)).comap φ := by
    rw [hH']; exact Subgroup.mem_top f
  rwa [Subgroup.mem_comap] at hf

end

theorem exists_reflGen_lift_of_neg (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F : Subgroup (U ≃ₗ[ZMod p] U)} (hF : ReflGen p F)
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hneg : ∃ z ∈ F, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      z v + v ∈ centralizerSpace F) :
    ∃ F₁ : Subgroup (U ≃ₗ[ZMod p] U), F₁ ≤ F ∧ ReflGen p F₁ ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) ≤ l ∧
      ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
        f v - f₁ v ∈ centralizerSpace F := by
  obtain ⟨m, hm⟩ := Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp
  obtain ⟨D⟩ := negSetup_exists hp hVF hW hneg hm
  have hz1_inv : (D.z ^ p) * (D.z ^ p) = 1 := negPowSq D
  have hfin_E_le := negE_finrank_le D hz1_inv
  let E : Submodule (ZMod p) U := HardMathSupport.Kantor79.movedSpace (D.z ^ p)
  let F₁ : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (negS F E)
  have hF₁_le_F : F₁ ≤ F := negClosure_le_F E
  have hF₁_gen : ReflGen p F₁ := negClosure_reflGen E
  have hVF₁_le_E : HardMathSupport.Kantor79.commutatorSpace F₁ ≤ E := negClosure_commutator_le E
  have hfin_F₁_le : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) ≤ l :=
    (Submodule.finrank_mono hVF₁_le_E).trans hfin_E_le
  have hR_sub : ∀ (σ : U ≃ₗ[ZMod p] U) (hσ : σ ∈ negR F),
      negPhi D ⟨σ, hσ.1⟩ ∈ Subgroup.map (negPhi D) (F₁.subgroupOf F) := by
    intro σ hσ
    obtain ⟨hσF, hσ_refl⟩ := hσ
    by_cases hσmod : ∀ v ∈ negV F, σ v - v ∈ negW F
    · have h1 : negPhi D ⟨σ, hσF⟩ = 1 := by
        have := (negCongruence D ⟨σ, hσF⟩ (1 : F)).mpr (fun v hv => by simpa using hσmod v hv)
        simpa using this
      exact Subgroup.mem_map.mpr ⟨1, (F₁.subgroupOf F).one_mem, by rw [map_one, h1]⟩
    · obtain ⟨τ, hτF, hτ_refl, hτ_le, hτ_rel⟩ := negRefl_lift D hσF hσ_refl hσmod
      refine Subgroup.mem_map.mpr ⟨⟨τ, hτF⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.subset_closure ⟨hτF, hτ_refl, hτ_le⟩), ?_⟩
      exact (negCongruence D ⟨τ, hτF⟩ ⟨σ, hσF⟩).mpr hτ_rel
  have hrange_le : (negPhi D).range ≤ Subgroup.map (negPhi D) (F₁.subgroupOf F) :=
    negRange_le E hF hR_sub
  refine ⟨F₁, hF₁_le_F, hF₁_gen, hfin_F₁_le, ?_⟩
  intro f hf
  have hmem : negPhi D ⟨f, hf⟩ ∈ (negPhi D).range := ⟨⟨f, hf⟩, rfl⟩
  have hrange := hrange_le hmem
  rw [Subgroup.mem_map] at hrange
  obtain ⟨f₁, hf₁, hφeq⟩ := hrange
  refine ⟨(f₁ : U ≃ₗ[ZMod p] U), Subgroup.mem_subgroupOf.mp hf₁, ?_⟩
  have hrel := (negCongruence D ⟨f, hf⟩ f₁).mp hφeq.symm
  intro v hv
  exact (hrel v hv).2

end CFSG.StandardType.ZS
