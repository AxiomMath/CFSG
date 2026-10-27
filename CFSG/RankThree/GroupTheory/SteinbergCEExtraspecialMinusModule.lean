module

public import CFSG.Foundations.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi

public section

namespace CFSG.RankThree.GroupTheory

open scoped commutatorElement

variable {S : Type*} [Group S] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def endConj (ρ : Representation K S V) (s : S) : Module.End K (Module.End K V) :=
  LinearMap.mulLeft K (ρ s) ∘ₗ LinearMap.mulRight K (ρ s⁻¹)

theorem endConj_apply (ρ : Representation K S V) (s : S) (f : Module.End K V) :
    endConj ρ s f = ρ s * f * ρ s⁻¹ := by
  simp [endConj, mul_assoc]

theorem extraspecial_commutator_eq_one_or (hS : IsExtraspecialPGroup 2 S) {z : S}
    (hz : Subgroup.center S = Subgroup.zpowers z) :
    orderOf z = 2 ∧ ∀ s t : S, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ = z := by
  have hz2 : orderOf z = 2 := by rw [← Nat.card_zpowers, ← hz, hS.2.2.2]
  refine ⟨hz2, fun s t => ?_⟩
  have h : ⁅s, t⁆ ∈ Subgroup.zpowers z := by
    rw [← hz, ← hS.2.1, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← zpow_mod_orderOf, hz2] at hk
  have hk2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk2 with h0 | h1
  · left
    rw [← hk, h0, zpow_zero]
  · right
    rw [← hk, h1, zpow_one]

theorem endConj_mul (ρ : Representation K S V) (s s' : S) :
    endConj ρ (s * s') = endConj ρ s * endConj ρ s' := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, endConj_apply, endConj_apply, endConj_apply, mul_inv_rev, map_mul,
    map_mul]
  simp only [mul_assoc]

theorem extraspecial_two_minus_module_bound [Finite S] {n : ℕ} (hS : IsExtraspecialPGroup 2 S)
    (hcard : Nat.card S = 2 ^ (1 + 2 * n)) {z : S} (hz : Subgroup.center S = Subgroup.zpowers z)
    (hK : (2 : K) ≠ 0) [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K S V)
    (hρz : ρ z = -1) :
    2 ^ n ≤ Module.finrank K V ∧
    ∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 →
      2 * Module.finrank K (Module.End.eigenspace (ρ s) 1) = Module.finrank K V ∧
      2 ^ (n - 1) ≤ Module.finrank K (Module.End.eigenspace (ρ s) 1) := by
  classical
  obtain ⟨hz2, hcomm⟩ := extraspecial_commutator_eq_one_or hS hz
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzinv : z⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hz2, pow_orderOf_eq_one]
  have hK1 : (1 : K) ≠ -1 := fun h => hK (by
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
  have hendc : ∀ s s' : S, Commute (endConj ρ s) (endConj ρ s') := by
    intro s s'
    have hss : s * s' = ⁅s, s'⁆ * (s' * s) := by rw [commutatorElement_def]; group
    change endConj ρ s * endConj ρ s' = endConj ρ s' * endConj ρ s
    rw [← endConj_mul, ← endConj_mul, hss, endConj_mul]
    have hend1 : endConj ρ 1 = 1 := by
      apply LinearMap.ext
      intro f
      rw [endConj_apply, inv_one, map_one, one_mul, mul_one, Module.End.one_apply]
    rcases hcomm s s' with h | h
    · rw [h, hend1, one_mul]
    · rw [h, hendz, one_mul]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun s => endConj ρ s) (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hendc j i) φ)
  set Q := S ⧸ Subgroup.center S
  let : Fintype Q := Fintype.ofFinite Q
  set rep : Q → S := fun q => Quotient.out q
  have hinjχ : Function.Injective fun q : Q => χ (rep q) := by
    intro q q' hqq
    have hχ : ∀ s, χ (rep q) s = χ (rep q') s := fun s => congrFun hqq s
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change ((rep q : S) : Q) = ((rep q' : S) : Q)
    rw [QuotientGroup.eq, Subgroup.mem_center_iff]
    intro s
    have hs := hχ s
    simp only [χ] at hs
    by_cases h1 : s * rep q = rep q * s
    · have h2 : s * rep q' = rep q' * s := by
        by_contra h2
        rw [ite_eq_left h1, ite_eq_right h2] at hs
        exact hK1 hs
      have hc1 : Commute s (rep q) := h1
      have hc2 : Commute s (rep q') := h2
      exact (hc1.inv_right.mul_right hc2).eq
    · have h2 : ¬ s * rep q' = rep q' * s := by
        intro h2
        rw [ite_eq_right h1, ite_eq_left h2] at hs
        exact hK1 hs.symm
      have e1 : ⁅s, rep q⁆ = z := (hcomm s _).resolve_left fun h =>
        h1 (commutatorElement_eq_one_iff_mul_comm.mp h)
      have e2 : ⁅s, rep q'⁆ = z := (hcomm s _).resolve_left fun h =>
        h2 (commutatorElement_eq_one_iff_mul_comm.mp h)
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
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
    rw [hS.2.2.2, hcard, ← Nat.card_eq_fintype_card] at *
    rw [pow_add, pow_one, mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm
  have hdim : 2 ^ n ≤ Module.finrank K V := by
    have h := hlin.fintype_card_le_finrank
    rw [hcardQ, Module.finrank_linearMap K K V V, two_mul, pow_add] at h
    by_contra hlt
    push Not at hlt
    exact absurd h (not_le.mpr (Nat.mul_lt_mul'' hlt hlt))
  refine ⟨hdim, fun s hs hs2 => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : S, ⁅s, t⁆ = z := by
    rw [Subgroup.mem_center_iff] at hs
    push Not at hs
    obtain ⟨g, hg⟩ := hs
    exact ⟨g, (hcomm s g).resolve_left fun h =>
      hg (commutatorElement_eq_one_iff_mul_comm.mp h).symm⟩
  have hst : ¬ s * t = t * s := fun h => hz1 (ht ▸ commutatorElement_eq_one_iff_mul_comm.mpr h)
  have hanti : ρ s * ρ t = -(ρ t * ρ s) := by
    have h := hconjrep s t
    rw [endConj_apply] at h
    simp only [χ, hst, ↓reduceIte, neg_one_smul] at h
    calc ρ s * ρ t = ρ s * ρ t * ρ s⁻¹ * ρ s := by
          rw [mul_assoc (ρ s * ρ t), ← map_mul ρ s⁻¹ s, inv_mul_cancel, map_one, mul_one]
      _ = -(ρ t * ρ s) := by rw [h, neg_mul]
  have hss : ρ s * ρ s = 1 := by
    rw [← map_mul, ← pow_two, ← hs2, pow_orderOf_eq_one, map_one]
  set Vp := Module.End.eigenspace (ρ s) 1
  set Vm := Module.End.eigenspace (ρ s) (-1)
  have hpm : ∀ v ∈ Vp, ρ t v ∈ Vm := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, hanti, LinearMap.neg_apply, Module.End.mul_apply, hv, one_smul,
      neg_one_smul]
  have hmp : ∀ v ∈ Vm, ρ t v ∈ Vp := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, hanti, LinearMap.neg_apply, Module.End.mul_apply, hv,
      neg_one_smul, map_neg, neg_neg, one_smul]
  have htinj : Function.Injective (ρ t) := by
    intro v w hvw
    have h := congrArg (ρ t⁻¹) hvw
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
  have hle1 : Module.finrank K Vp ≤ Module.finrank K Vm :=
    LinearMap.finrank_le_finrank_of_injective (f := (ρ t).restrict hpm) fun v w h =>
      Subtype.ext (htinj (congrArg Subtype.val h))
  have hle2 : Module.finrank K Vm ≤ Module.finrank K Vp :=
    LinearMap.finrank_le_finrank_of_injective (f := (ρ t).restrict hmp) fun v w h =>
      Subtype.ext (htinj (congrArg Subtype.val h))
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h2inv : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ hK
    have hv : v = (2 : K)⁻¹ • (v + ρ s v) + (2 : K)⁻¹ • (v - ρ s v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, h2inv, one_smul]
    rw [hv]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · rw [Module.End.mem_eigenspace_iff, map_add, ← Module.End.mul_apply, hss,
        Module.End.one_apply, one_smul, add_comm]
    · rw [Module.End.mem_eigenspace_iff, map_sub, ← Module.End.mul_apply, hss,
        Module.End.one_apply, neg_one_smul, neg_sub]
  have hinf : Vp ⊓ Vm = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hv
    rw [Module.End.mem_eigenspace_iff] at h1 h2
    rw [h1, one_smul, neg_one_smul] at h2
    have h3 : (2 : K) • v = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; exact neg_add_cancel v
    exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h3).resolve_left hK)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Vp Vm
  rw [hsup, hinf, finrank_top, finrank_bot, add_zero] at hsum
  have h2 : 2 * Module.finrank K Vp = Module.finrank K V := by omega
  refine ⟨h2, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, Nat.zero_sub, pow_zero]
    have : 0 < Module.finrank K V := Module.finrank_pos
    omega
  · have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

end CFSG.RankThree.GroupTheory
