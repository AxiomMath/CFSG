module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

variable {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

structure GGExtCtx (A : Subgroup (V ≃ₗ[ZMod p] V)) (T : Submodule (ZMod p) V)
    (AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)) : Prop where
  disp : ∀ a ∈ A, ∀ v, a v - v ∈ T
  fix : ∀ v, (∀ a ∈ A, a v = v) → v = 0
  inj : ∀ a ∈ A, (∀ v ∈ T, a v = v) → a = 1
  restr : ∀ q, q ∈ AT ↔ ∃ a ∈ A, ∀ w : ↥T, a (w : V) = ((q w : ↥T) : V)

namespace GGExtCtx

variable {A : Subgroup (V ≃ₗ[ZMod p] V)} {T : Submodule (ZMod p) V}
  {AT : Subgroup (↥T ≃ₗ[ZMod p] ↥T)}

theorem apply_mem (X : GGExtCtx A T AT) {a : V ≃ₗ[ZMod p] V} (ha : a ∈ A) {v : V}
    (hv : v ∈ T) : a v ∈ T := by
  simpa using T.add_mem (X.disp a ha v) hv

theorem eq_top_of_neg_mem [Fact p.Prime] (X : GGExtCtx A T AT) (hp : p ≠ 2)
    (hneg : (LinearEquiv.neg (ZMod p) : ↥T ≃ₗ[ZMod p] ↥T) ∈ AT) : T = ⊤ := by
  obtain ⟨z, hzA, hz⟩ := (X.restr _).1 hneg
  have hzT : ∀ w ∈ T, z w = -w := fun w hw => by
    simpa using hz ⟨w, hw⟩
  let u : (ZMod p)ˣ :=
    ZMod.unitOfCoprime 2 ((Nat.coprime_primes Nat.prime_two Fact.out).mpr fun h => hp h.symm)
  have hu : ∀ w : V, u • w = w + w := fun w => by
    rw [Units.smul_def, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, two_smul]
  have hhalf : ∀ w : V, w = -w → w = 0 := by
    intro w hw
    refine (smul_eq_zero_iff_eq u).mp ?_
    rw [hu]
    nth_rewrite 2 [hw]
    exact add_neg_cancel w
  have hcomm : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    have hcA : a * z * a⁻¹ * z⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem ha hzA) (A.inv_mem ha)) (A.inv_mem hzA)
    have hcT : ∀ w ∈ T, (a * z * a⁻¹ * z⁻¹) w = w := by
      intro w hw
      have hzi : z⁻¹ w = -w := by
        have h1 : z (-w) = w := by rw [hzT (-w) (T.neg_mem hw), neg_neg]
        calc z⁻¹ w = z⁻¹ (z (-w)) := by rw [h1]
          _ = -w := z.symm_apply_apply (-w)
      have hmem : a⁻¹ (-w) ∈ T := X.apply_mem (A.inv_mem ha) (T.neg_mem hw)
      show a (z (a⁻¹ (z⁻¹ w))) = w
      rw [hzi, hzT _ hmem, ← map_neg, neg_neg]
      exact a.apply_symm_apply w
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 (X.inj _ hcA hcT))
  have hzz : ∀ v, z (z v) = v := by
    intro v
    have h1 : z (z v - v) = -(z v - v) := hzT _ (X.disp z hzA v)
    rw [map_sub, neg_sub] at h1
    simpa using congrArg (· + z v) h1
  have hneg' : ∀ v, z v = -v := by
    intro v
    have hfix : ∀ a ∈ A, a (v + z v) = v + z v := by
      intro a ha
      have hd : a (v + z v) - (v + z v) ∈ T := X.disp a ha _
      have hza : z (a (v + z v)) = a (z (v + z v)) :=
        (congrArg (fun g => g (v + z v)) (hcomm a ha)).symm
      have hzd : z (a (v + z v) - (v + z v)) = a (v + z v) - (v + z v) := by
        rw [map_sub, hza, map_add, hzz, add_comm (z v) v]
      exact sub_eq_zero.1 (hhalf _ (hzd.symm.trans (hzT _ hd)))
    exact eq_neg_of_add_eq_zero_right (X.fix _ hfix)
  rw [eq_top_iff]
  intro v _
  have h1 : z v - v ∈ T := X.disp z hzA v
  rw [hneg' v] at h1
  have h3 : u • v ∈ T := by
    have h4 : -(-v - v) ∈ T := T.neg_mem h1
    rwa [neg_sub, sub_neg_eq_add, ← hu] at h4
  exact (T.smul_mem_iff' u).mp h3

theorem mem_of_forall_fixed [Fact p.Prime] [Module.Finite (ZMod p) V] (X : GGExtCtx A T AT)
    {B : Subgroup (V ≃ₗ[ZMod p] V)} (hidx : ¬ p ∣ B.relIndex A) {v : V}
    (hv : ∀ b ∈ B, b v = v) : v ∈ T := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) DFunLike.coe_injective
  let B' : Subgroup ↥A := B.subgroupOf A
  letI : Fintype (↥A ⧸ B') := Fintype.ofFinite _
  let f : ↥A ⧸ B' → V := @Quotient.lift ↥A V (QuotientGroup.leftRel B')
    (fun a => (a : V ≃ₗ[ZMod p] V) v) (by
      intro a b hab
      have h1 : a⁻¹ * b ∈ B' := QuotientGroup.leftRel_apply.mp hab
      have h3 : ((a⁻¹ * b : ↥A) : V ≃ₗ[ZMod p] V) v = v := hv _ (Subgroup.mem_subgroupOf.mp h1)
      have h4 : (b : V ≃ₗ[ZMod p] V) v =
          (a : V ≃ₗ[ZMod p] V) (((a⁻¹ * b : ↥A) : V ≃ₗ[ZMod p] V) v) :=
        ((a : V ≃ₗ[ZMod p] V).apply_symm_apply _).symm
      show (a : V ≃ₗ[ZMod p] V) v = (b : V ≃ₗ[ZMod p] V) v
      rw [h4, h3])
  have hf : ∀ (g : ↥A) (q : ↥A ⧸ B'), f (g • q) = (g : V ≃ₗ[ZMod p] V) (f q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H a => rfl
  have hfT : ∀ q, f q - v ∈ T := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a => exact X.disp _ a.2 v
  have hwfix : ∀ a ∈ A, a (∑ q, f q) = ∑ q, f q := by
    intro a ha
    rw [map_sum, ← Equiv.sum_comp (MulAction.toPerm (⟨a, ha⟩ : ↥A)) f]
    exact Finset.sum_congr rfl fun q _ => (hf ⟨a, ha⟩ q).symm
  have hw0 : ∑ q, f q = 0 := X.fix _ hwfix
  have hsum : ∑ q, f q - Fintype.card (↥A ⧸ B') • v ∈ T := by
    have h1 := T.sum_mem (t := Finset.univ) (fun q _ => hfT q)
    rwa [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ] at h1
  have hcard : Fintype.card (↥A ⧸ B') = B.relIndex A := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hw0, zero_sub, hcard] at hsum
  let u : (ZMod p)ˣ :=
    ZMod.unitOfCoprime _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hidx).symm
  have h6 : u • v ∈ T := by
    rw [Units.smul_def, ZMod.coe_unitOfCoprime, Nat.cast_smul_eq_nsmul (ZMod p)]
    simpa using T.neg_mem hsum
  exact (T.smul_mem_iff' u).mp h6

section Restrict

open Subgroup

theorem map_eq (X : GGExtCtx A T AT) {a : V ≃ₗ[ZMod p] V} (ha : a ∈ A) :
    T.map (a : V →ₗ[ZMod p] V) = T := by
  refine le_antisymm ?_ ?_
  · intro w hw
    rw [Submodule.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact X.apply_mem ha hv
  · intro w hw
    rw [Submodule.mem_map]
    exact ⟨a⁻¹ w, X.apply_mem (A.inv_mem ha) hw, a.apply_symm_apply w⟩

noncomputable def restrict (X : GGExtCtx A T AT) (a : ↥A) : ↥T ≃ₗ[ZMod p] ↥T :=
  (a : V ≃ₗ[ZMod p] V).ofSubmodules T T (X.map_eq a.2)

theorem restrict_apply (X : GGExtCtx A T AT) (a : ↥A) (w : ↥T) :
    ((X.restrict a w : ↥T) : V) = (a : V ≃ₗ[ZMod p] V) w := by
  rfl

noncomputable def restrictHom (X : GGExtCtx A T AT) : ↥A →* (↥T ≃ₗ[ZMod p] ↥T) where
  toFun := X.restrict
  map_one' := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [restrict_apply, Subgroup.coe_one]
    rfl
  map_mul' := by
    intro a b
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    simp only [restrict_apply, LinearEquiv.mul_apply, Subgroup.coe_mul]

theorem restrictHom_injective (X : GGExtCtx A T AT) : Function.Injective X.restrictHom := by
  refine (injective_iff_map_eq_one X.restrictHom).2 ?_
  intro a ha
  apply Subtype.ext
  apply X.inj a a.2
  intro v hv
  have h : X.restrict a = 1 := ha
  have h2 := congrArg (fun e : ↥T ≃ₗ[ZMod p] ↥T => ((e ⟨v, hv⟩ : ↥T) : V)) h
  rw [restrict_apply] at h2
  simpa using h2

theorem range_restrictHom (X : GGExtCtx A T AT) : X.restrictHom.range = AT := by
  ext q
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    refine (X.restr q).2 ⟨a, a.2, ?_⟩
    intro w
    have ha' : X.restrict a = q := ha
    have h := congrArg (fun e : ↥T ≃ₗ[ZMod p] ↥T => ((e w : ↥T) : V)) ha'
    rw [restrict_apply] at h
    exact h
  · intro hq
    obtain ⟨a, haA, ha⟩ := (X.restr q).1 hq
    refine ⟨⟨a, haA⟩, ?_⟩
    show X.restrict ⟨a, haA⟩ = q
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [restrict_apply]
    exact ha w

noncomputable def restrictEquiv (X : GGExtCtx A T AT) : ↥A ≃* ↥AT :=
  (MonoidHom.ofInjective X.restrictHom_injective).trans
    (MulEquiv.subgroupCongr X.range_restrictHom)

theorem restrictEquiv_symm_apply (X : GGExtCtx A T AT) (s : ↥AT) (w : ↥T) :
    ((X.restrictEquiv.symm s : ↥A) : V ≃ₗ[ZMod p] V) (w : V) =
      (((s : ↥T ≃ₗ[ZMod p] ↥T) w : ↥T) : V) := by
  have h1 : X.restrictEquiv (X.restrictEquiv.symm s) = s :=
    MulEquiv.apply_symm_apply X.restrictEquiv s
  have h2 : (X.restrictEquiv (X.restrictEquiv.symm s) : ↥T ≃ₗ[ZMod p] ↥T) =
      (s : ↥T ≃ₗ[ZMod p] ↥T) :=
    congrArg (fun e : ↥AT => (e : ↥T ≃ₗ[ZMod p] ↥T)) h1
  have h3 : X.restrict (X.restrictEquiv.symm s) = (s : ↥T ≃ₗ[ZMod p] ↥T) := h2
  rw [← restrict_apply X (X.restrictEquiv.symm s) w, h3]

private theorem sum_range_shift_eq {M : Type*} [AddCommGroup M] (f : ℕ → M) {n : ℕ}
    (hn : f n = f 0) : ∑ k ∈ Finset.range n, f (k + 1) = ∑ k ∈ Finset.range n, f k := by
  have h := Finset.sum_range_sub f n
  rw [hn, sub_self, Finset.sum_sub_distrib] at h
  exact sub_eq_zero.mp h

theorem exists_fixed_sub_mem [Fact p.Prime] (X : GGExtCtx A T AT) {a : V ≃ₗ[ZMod p] V}
    (ha : a ∈ A) {n : ℕ} (hn : a ^ n = 1) (hn0 : (n : ZMod p) ≠ 0) (v : V) :
    ∃ w, a w = w ∧ w - v ∈ T := by
  classical
  set S : V := ∑ k ∈ Finset.range n, (a ^ k) v with hS
  refine ⟨(n : ZMod p)⁻¹ • S, ?_, ?_⟩
  · rw [LinearEquiv.map_smul]
    have hstep : ∀ k, a ((a ^ k) v) = (a ^ (k + 1)) v := by
      intro k
      rw [← LinearEquiv.mul_apply, ← pow_succ']
    have hfix : a S = S := by
      rw [hS, map_sum]
      simp_rw [hstep]
      exact sum_range_shift_eq (fun k => (a ^ k) v) (by simp [hn])
    rw [hfix]
  · have hsum : S - n • v = ∑ k ∈ Finset.range n, ((a ^ k) v - v) := by
      rw [hS, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hmem : S - n • v ∈ T := by
      rw [hsum]
      exact T.sum_mem (t := Finset.range n)
        (fun k _ => X.disp (a ^ k) (A.pow_mem ha k) v)
    have hwv : (n : ZMod p)⁻¹ • S - v = (n : ZMod p)⁻¹ • (S - n • v) := by
      rw [smul_sub, ← Nat.cast_smul_eq_nsmul (ZMod p) n v, smul_smul,
        inv_mul_cancel₀ hn0, one_smul]
    simpa only [hwv] using T.smul_mem (n : ZMod p)⁻¹ hmem

theorem mem_of_forall_fixed_lift [Fact p.Prime] [Module.Finite (ZMod p) V] (X : GGExtCtx A T AT)
    {S : Set (↥T ≃ₗ[ZMod p] ↥T)} (hS : S ⊆ AT) (hidx : ¬ p ∣ (closure S).relIndex AT)
    {v : V} (hv : ∀ s (hs : s ∈ S), ((X.restrictEquiv.symm ⟨s, hS hs⟩ : ↥A) :
      V ≃ₗ[ZMod p] V) v = v) :
    v ∈ T := by
  classical
  set S' : Set ↥AT := AT.subtype ⁻¹' S with hS'def
  set ψ : ↥AT ≃* ↥A := X.restrictEquiv.symm with hψdef
  have hSP : S' ⊆ (MulAction.stabilizer (V ≃ₗ[ZMod p] V) v).comap
      (A.subtype.comp (ψ : ↥AT →* ↥A)) := by
    intro x hx
    have hxS : (x : ↥T ≃ₗ[ZMod p] ↥T) ∈ S := by
      rw [hS'def] at hx
      exact hx
    show A.subtype ((ψ : ↥AT →* ↥A) x) ∈ MulAction.stabilizer (V ≃ₗ[ZMod p] V) v
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def, hψdef]
    change ((X.restrictEquiv.symm x : ↥A) : V ≃ₗ[ZMod p] V) v = v
    have hx' : (⟨(x : ↥T ≃ₗ[ZMod p] ↥T), hS hxS⟩ : ↥AT) = x := Subtype.ext rfl
    rw [← hx']
    exact hv _ hxS
  have hfix' : ∀ b ∈ ((closure S').map (ψ : ↥AT →* ↥A)).map A.subtype, b v = v := by
    intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hxP : x ∈ (MulAction.stabilizer (V ≃ₗ[ZMod p] V) v).comap
        (A.subtype.comp (ψ : ↥AT →* ↥A)) := (Subgroup.closure_le _).mpr hSP hx
    have hxS : ((X.restrictEquiv.symm x : ↥A) : V ≃ₗ[ZMod p] V) v = v := by
      have h := Subgroup.mem_comap.mp hxP
      rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def, hψdef] at h
      exact h
    change ((X.restrictEquiv.symm x : ↥A) : V ≃ₗ[ZMod p] V) v = v
    exact hxS
  have hsub : (((closure S').map (ψ : ↥AT →* ↥A)).map A.subtype).subgroupOf A
      = (closure S').map (ψ : ↥AT →* ↥A) := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
  have hrel : (((closure S').map (ψ : ↥AT →* ↥A)).map A.subtype).relIndex A
      = (closure S').index := by
    change ((((closure S').map (ψ : ↥AT →* ↥A)).map A.subtype).subgroupOf A).index
      = (closure S').index
    rw [hsub, Subgroup.index_map_equiv (closure S') ψ]
  have hS'_image : AT.subtype '' S' = S := by
    rw [hS'def]
    exact Set.image_preimage_eq_of_subset (by
      intro s hs
      exact ⟨⟨s, hS hs⟩, rfl⟩)
  have hT : (closure S).subgroupOf AT = closure S' := by
    rw [← (Subgroup.map_injective AT.subtype_injective).eq_iff]
    rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.closure_le AT).mpr hS),
      MonoidHom.map_closure, hS'_image]
  have hclosed : (closure S').index = (closure S).relIndex AT := by
    change (closure S').index = ((closure S).subgroupOf AT).index
    rw [hT]
  have hidx' : ¬ p ∣ (((closure S').map (ψ : ↥AT →* ↥A)).map A.subtype).relIndex A := by
    rw [hrel, hclosed]
    exact hidx
  exact X.mem_of_forall_fixed (B := ((closure S').map (ψ : ↥AT →* ↥A)).map A.subtype)
    hidx' hfix'

end Restrict

theorem sum_cocycle_eq {b c d g : V ≃ₗ[ZMod p] V} {w : V} (hd : d w = w) {i j : ℕ}
    (hrel : d * g * d⁻¹ = b ^ i * c ^ j) :
    ∑ k ∈ Finset.range i, (b ^ k) (b w - w) +
        (b ^ i) (∑ k ∈ Finset.range j, (c ^ k) (c w - w)) = d (g w - w) := by
  have hb : ∀ k, (b ^ k) (b w - w) = (b ^ (k + 1)) w - (b ^ k) w := by
    intro k
    rw [map_sub, ← LinearEquiv.mul_apply, ← pow_succ]
  have hc : ∀ k, (c ^ k) (c w - w) = (c ^ (k + 1)) w - (c ^ k) w := by
    intro k
    rw [map_sub, ← LinearEquiv.mul_apply, ← pow_succ]
  have hsb : ∑ k ∈ Finset.range i, (b ^ k) (b w - w) = (b ^ i) w - w := by
    simp_rw [hb]
    rw [Finset.sum_range_sub (fun k => (b ^ k) w)]
    simp
  have hsc : ∑ k ∈ Finset.range j, (c ^ k) (c w - w) = (c ^ j) w - w := by
    simp_rw [hc]
    rw [Finset.sum_range_sub (fun k => (c ^ k) w)]
    simp
  have hd' : d⁻¹ w = w := by
    calc d⁻¹ w = d⁻¹ (d w) := by rw [hd]
      _ = w := d.symm_apply_apply w
  have hbc : (b ^ i) ((c ^ j) w - w) = (b ^ i * c ^ j) w - (b ^ i) w := by
    rw [map_sub, ← LinearEquiv.mul_apply]
  have hfinal : (d * g * d⁻¹) w - w = d (g w - w) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hd', map_sub, hd]
  rw [hsb, hsc, hbc, ← hrel]
  rw [show (b ^ i) w - w + ((d * g * d⁻¹) w - (b ^ i) w)
      = (d * g * d⁻¹) w - w from by abel, hfinal]

end GGExtCtx

end CFSG.StandardType

end
