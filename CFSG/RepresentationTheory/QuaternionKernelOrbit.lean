module

public import CFSG.GroupTheory.HyperplaneDecomposition
public import CFSG.GroupTheory.QuaternionAutPrime

public section

namespace CFSG.RepresentationTheory

open Subgroup
open scoped BigOperators commutatorElement

variable {p : ℕ} [Fact p.Prime]
variable {Γ : Type*} [Group Γ]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
variable (ρ : Representation (ZMod p) Γ V) (N : Subgroup Γ)

theorem pow_mem_normalizer_of_prime {G : Type*} [Group G] {H : Subgroup G} {x : G}
    {r i : ℕ} (hr : r.Prime) (hi0 : 0 < i) (hir : i < r) (hxr : x ^ r = 1)
    (hxi : x ^ i ∈ Subgroup.normalizer (H : Set G)) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  have hnot : ¬ r ∣ i := by
    intro h
    have hle := Nat.le_of_dvd hi0 h
    omega
  have hcop : i.Coprime (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxr)
      (hr.coprime_iff_not_dvd.mpr hnot).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem (Subgroup.normalizer (H : Set G)) hxi m

@[expose]
def IsInvariantUnder (W : Submodule (ZMod p) V) : Prop :=
  ∀ g ∈ N, ∀ w ∈ W, ρ g w ∈ W

@[expose]
def IsSimpleUnder (W : Submodule (ZMod p) V) : Prop :=
  IsInvariantUnder ρ N W ∧
    ∀ W' ≤ W, IsInvariantUnder ρ N W' → W' = ⊥ ∨ W' = W

variable {ρ N}

theorem apply_conj_apply (n t : Γ) (w : V) :
    ρ (n * t * n⁻¹) (ρ n w) = ρ n (ρ t w) := by
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]

theorem IsSimpleUnder.map {W : Submodule (ZMod p) V} (hW : IsSimpleUnder ρ N W) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (N : Set Γ)) :
    IsSimpleUnder ρ N (W.map (ρ g)) := by
  refine ⟨?_, ?_⟩
  · intro n hn w hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    have hmem : g⁻¹ * n * g ∈ N :=
      (Subgroup.mem_set_normalizer_iff''.mp hg n).mp hn
    refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) u, hW.1 _ hmem _ hu, ?_⟩
    rw [← apply_conj_apply (ρ := ρ) g (g⁻¹ * n * g) u,
      show g * (g⁻¹ * n * g) * g⁻¹ = n by group]
  · intro W' hW'le hW'inv
    let U' : Submodule (ZMod p) V := W'.map (ρ g⁻¹)
    have hcomp : (ρ g⁻¹).comp (ρ g) = 1 := by
      ext v
      exact Representation.inv_self_apply (ρ := ρ) g v
    have hU'le : U' ≤ W := by
      have h1 : U' ≤ (W.map (ρ g)).map (ρ g⁻¹) := Submodule.map_mono hW'le
      have h2 : (W.map (ρ g)).map (ρ g⁻¹) = W := by
        rw [← Submodule.map_comp, hcomp,
          show (1 : V →ₗ[ZMod p] V) = LinearMap.id from rfl, Submodule.map_id]
      rwa [h2] at h1
    have hU'inv : IsInvariantUnder ρ N U' := by
      intro n hn w hw
      obtain ⟨w0, hw0, rfl⟩ := Submodule.mem_map.mp hw
      have hmem : g * n * g⁻¹ ∈ N :=
        (Subgroup.mem_set_normalizer_iff.mp hg n).mp hn
      refine Submodule.mem_map.mpr ⟨ρ (g * n * g⁻¹) w0, hW'inv _ hmem _ hw0, ?_⟩
      have h := apply_conj_apply (ρ := ρ) g⁻¹ (g * n * g⁻¹) w0
      simp only [inv_inv] at h
      rw [show g⁻¹ * (g * n * g⁻¹) * g = n by group] at h
      exact h.symm
    have hcomp' : (ρ g).comp (ρ g⁻¹) = 1 := by
      ext v
      exact Representation.self_inv_apply (ρ := ρ) g v
    have hW'map : U'.map (ρ g) = W' := by
      rw [show U' = W'.map (ρ g⁻¹) from rfl, ← Submodule.map_comp, hcomp',
        show (1 : V →ₗ[ZMod p] V) = LinearMap.id from rfl, Submodule.map_id]
    rcases hW.2 U' hU'le hU'inv with hbot | htop
    · left
      rw [← hW'map, hbot, Submodule.map_bot]
    · right
      rw [← hW'map, htop]

theorem quaternion_kernel_commute {T : Subgroup Γ} (hTN : T ≤ N)
    (hN : N ≤ Subgroup.normalizer (T : Set Γ)) {W : Submodule (ZMod p) V}
    (hW : IsInvariantUnder ρ N W) {φ : ↥T →* QuaternionGroup 2}
    (hker : ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ (t : Γ) w = w) {s : ↥T}
    (hs : φ s = QuaternionGroup.a 2) {n : Γ} (hn : n ∈ N) {w : V} (hw : w ∈ W) :
    ρ (s : Γ) (ρ n w) = ρ n (ρ (s : Γ) w) := by
  let g : ↥T := ⟨n * (s : Γ) * n⁻¹,
    (Subgroup.mem_set_normalizer_iff.mp (hN hn) (s : Γ)).mp s.2⟩
  have hs2 : ∀ x ∈ W, ρ ((s ^ 2 : ↥T) : Γ) x = x := by
    intro x hx
    exact (hker (s ^ 2)).mp (by rw [map_pow, hs]; decide) x hx
  have hg2 : ∀ x ∈ W, ρ ((g ^ 2 : ↥T) : Γ) x = x := by
    intro x hx
    have h1 : ((g ^ 2 : ↥T) : Γ) = n * ((s ^ 2 : ↥T) : Γ) * n⁻¹ := by simp [g, pow_two, mul_assoc]
    rw [h1, ← Representation.self_inv_apply (ρ := ρ) n x,
      apply_conj_apply (ρ := ρ) n ((s ^ 2 : ↥T) : Γ) (ρ n⁻¹ x),
      hs2 _ (hW n⁻¹ (inv_mem hn) x hx), Representation.self_inv_apply]
  have hg_ne : φ g ≠ 1 := by
    intro h
    have hfixg : ∀ x ∈ W, ρ (g : Γ) x = x := (hker g).mp h
    have hfixs : ∀ x ∈ W, ρ (s : Γ) x = x := by
      intro x hx
      have h := hfixg (ρ n x) (hW n hn x hx)
      rw [apply_conj_apply (ρ := ρ) n (s : Γ) x] at h
      simpa only [Representation.inv_self_apply] using congrArg (fun y => ρ n⁻¹ y) h
    exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1)
      (by simpa [hs] using (hker s).mpr hfixs)
  have hgφ : φ g = QuaternionGroup.a 2 := by
    have hsq : (φ g) ^ 2 = 1 := by
      simpa [map_pow] using (hker (g ^ 2)).mpr hg2
    rcases CFSG.GroupTheory.quaternion_eq_a_two_or_sq_eq_a_two hg_ne with h | h
    · exact h
    · rw [h] at hsq; exact absurd hsq (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1)
  have hgs_fix : ∀ x ∈ W, ρ ((g * s⁻¹ : ↥T) : Γ) x = x := by
    apply (hker (g * s⁻¹)).mp
    rw [map_mul, map_inv, hgφ, hs, mul_inv_cancel]
  have h1 : ∀ z ∈ W, ρ n (ρ (s : Γ) (ρ n⁻¹ z)) = ρ (s : Γ) z := by
    intro z hz
    have hsz : ρ (s : Γ) z ∈ W := hW (s : Γ) (hTN s.2) z hz
    have h := hgs_fix (ρ (s : Γ) z) hsz
    have h' : ρ (n * (s : Γ) * n⁻¹) z = ρ (s : Γ) z := by
      simpa [g, ← Module.End.mul_apply, ← map_mul, mul_assoc] using h
    have h'' := apply_conj_apply (ρ := ρ) n (s : Γ) (ρ n⁻¹ z)
    rw [Representation.self_inv_apply, h'] at h''
    exact h''.symm
  simpa [Representation.inv_self_apply] using (h1 (ρ n w) (hW n hn w hw)).symm

theorem isInvariantUnder_inf_ker_sub_one {T : Subgroup Γ} (hTN : T ≤ N)
    (hN : N ≤ Subgroup.normalizer (T : Set Γ)) {W : Submodule (ZMod p) V}
    (hW : IsInvariantUnder ρ N W) {φ : ↥T →* QuaternionGroup 2}
    (hker : ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ (t : Γ) w = w) {s : ↥T}
    (hs : φ s = QuaternionGroup.a 2) :
    IsInvariantUnder ρ N (W ⊓ LinearMap.ker (ρ (s : Γ) - 1)) := by
  intro n hn x hx
  have hxW : x ∈ W := hx.1
  have hxfix : ρ (s : Γ) x = x := by
    have h := hx.2
    change ρ (s : Γ) x - x = 0 at h
    exact sub_eq_zero.mp h
  refine ⟨hW n hn x hxW, ?_⟩
  have hcomm := quaternion_kernel_commute hTN hN hW hker hs hn hxW
  change ρ (s : Γ) (ρ n x) - ρ n x = 0
  rw [hcomm, hxfix, sub_self]

theorem eq_neg_of_sq_eq_one_of_inf_ker_eq_bot {f : V →ₗ[ZMod p] V}
    {W : Submodule (ZMod p) V} (hW : ∀ w ∈ W, f w ∈ W)
    (hsq : ∀ w ∈ W, f (f w) = w) (h2 : (2 : ZMod p) ≠ 0)
    (hbot : W ⊓ LinearMap.ker (f - 1) = ⊥) :
    ∀ w ∈ W, f w = -w := by
  intro w hw
  let u : V := (2 : ZMod p)⁻¹ • (w + f w)
  have huW : u ∈ W := W.smul_mem _ (W.add_mem hw (hW w hw))
  have hufix : f u = u := by
    dsimp [u]
    rw [map_smul, map_add, hsq w hw, add_comm]
  have huP : u ∈ W ⊓ LinearMap.ker (f - 1) := by
    refine ⟨huW, ?_⟩
    change f u - u = 0
    rw [hufix, sub_self]
  have hu0 : u = 0 := by
    rw [hbot] at huP
    simpa using huP
  have hsum : w + f w = 0 := by
    have h := congrArg (fun v : V => (2 : ZMod p) • v) hu0
    have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
      Field.mul_inv_cancel (2 : ZMod p) h2
    simpa [u, smul_smul, h2inv] using h
  exact eq_neg_of_add_eq_zero_right hsum

theorem acts_neg_one_of_quaternion_kernel {T : Subgroup Γ} (hTN : T ≤ N)
    (hN : N ≤ Subgroup.normalizer (T : Set Γ)) {W : Submodule (ZMod p) V}
    (hW : IsSimpleUnder ρ N W) {φ : ↥T →* QuaternionGroup 2}
    (hker : ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ (t : Γ) w = w) {s : ↥T}
    (hs : φ s = QuaternionGroup.a 2) (hp2 : p ≠ 2) :
    ∀ w ∈ W, ρ (s : Γ) w = -w := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hA2 : ∀ w ∈ W, ρ (s : Γ) (ρ (s : Γ) w) = w := by
    intro w hw
    have h := (hker (s ^ 2)).mp (by rw [map_pow, hs]; decide) w hw
    simpa [pow_two, map_mul, Module.End.mul_apply] using h
  have hproper : ∃ w ∈ W, ρ (s : Γ) w ≠ w := by
    by_contra h
    push Not at h
    have h1 : φ s = 1 := (hker s).mpr h
    rw [hs] at h1
    exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) h1
  have hPinv := isInvariantUnder_inf_ker_sub_one hTN hN hW.1 hker hs
  have hPne : W ⊓ LinearMap.ker (ρ (s : Γ) - 1) ≠ W := by
    obtain ⟨w, hwW, hwne⟩ := hproper
    intro hPW
    apply hwne
    have hwP : w ∈ W ⊓ LinearMap.ker (ρ (s : Γ) - 1) := by rw [hPW]; exact hwW
    exact sub_eq_zero.mp hwP.2
  have hPbot : W ⊓ LinearMap.ker (ρ (s : Γ) - 1) = ⊥ := by
    rcases hW.2 _ inf_le_left hPinv with h | h
    · exact h
    · exact absurd h hPne
  exact eq_neg_of_sq_eq_one_of_inf_ker_eq_bot
    (f := ρ (s : Γ)) (W := W) (fun w hw => hW.1 (s : Γ) (hTN s.2) w hw) hA2 h2 hPbot

noncomputable def sumMap (ρ : Representation (ZMod p) Γ V) (K : Subgroup Γ) [Fintype K] :
    V →ₗ[ZMod p] V :=
  ∑ k : K, ρ (k : Γ)

theorem sumMap_apply_eq_zero_of_neg {K : Subgroup Γ} [Fintype K] {s : K} {w : V}
    (hs : ρ (s : Γ) w = -w) (hp2 : p ≠ 2) : sumMap ρ K w = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hre : sumMap ρ K (ρ (s : Γ) w) = sumMap ρ K w := by
    simp only [sumMap, LinearMap.sum_apply]
    simp_rw [← Module.End.mul_apply, ← map_mul]
    exact Equiv.sum_comp (Equiv.mulRight s) (fun k : K => ρ (k : Γ) w)
  have hneg : -sumMap ρ K w = sumMap ρ K w := by
    simpa [hs, map_neg] using hre
  have hpp : sumMap ρ K w + sumMap ρ K w = 0 := by
    nth_rewrite 1 [← hneg]
    exact neg_add_cancel _
  have h2P : (2 : ZMod p) • sumMap ρ K w = 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num,
      Nat.cast_smul_eq_nsmul, two_nsmul]
    exact hpp
  exact (smul_eq_zero.mp h2P).resolve_left h2

theorem sumMap_apply_eq_card_smul {K : Subgroup Γ} [Fintype K] {u : V}
    (hfix : ∀ k : K, ρ (k : Γ) u = u) :
    sumMap ρ K u = (Nat.card K : ZMod p) • u := by
  rw [sumMap, LinearMap.sum_apply]
  simp_rw [hfix]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

theorem apply_sum_range_pow_apply {r : ℕ} {x : Γ} (hxr : x ^ r = 1) (u : V) :
    ρ x (Finset.sum (Finset.range r) (fun i => ρ (x ^ i) u)) =
      Finset.sum (Finset.range r) (fun i => ρ (x ^ i) u) := by
  have h := Finset.sum_range_succ' (fun i => ρ (x ^ i) u) r
  rw [Finset.sum_range_succ, pow_zero, hxr] at h
  rw [map_sum]
  simp_rw [← Module.End.mul_apply, ← map_mul, ← pow_succ']
  exact (add_right_cancel h).symm

@[expose]
def kernelIn (ρ : Representation (ZMod p) Γ V) (T : Subgroup Γ)
    (W : Submodule (ZMod p) V) : Subgroup Γ where
  carrier := {t | t ∈ T ∧ ∀ w ∈ W, ρ t w = w}
  one_mem' := ⟨T.one_mem, fun w _ => by simp⟩
  mul_mem' := by
    rintro t s ⟨htT, htW⟩ ⟨hsT, hsW⟩
    refine ⟨T.mul_mem htT hsT, fun w hw => ?_⟩
    rw [map_mul, Module.End.mul_apply, hsW w hw, htW w hw]
  inv_mem' := by
    rintro t ⟨htT, htW⟩
    refine ⟨T.inv_mem htT, fun w hw => ?_⟩
    calc
      ρ t⁻¹ w = ρ t⁻¹ (ρ t w) := by rw [htW w hw]
      _ = w := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]

theorem kernelIn_map_conj {T : Subgroup Γ} {W : Submodule (ZMod p) V} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (T : Set Γ)) :
    kernelIn ρ T (W.map (ρ g)) =
      (kernelIn ρ T W).map (MulAut.conj g) := by
  ext t
  constructor
  · intro ht
    have htT : t ∈ T := ht.1
    have htW : ∀ w ∈ W.map (ρ g), ρ t w = w := ht.2
    have hsT : g⁻¹ * t * g ∈ T := (Subgroup.mem_set_normalizer_iff''.mp hg t).mp htT
    have hsW : ∀ w ∈ W, ρ (g⁻¹ * t * g) w = w := by
      intro w hw
      have htw : ρ t (ρ g w) = ρ g w :=
        htW (ρ g w) (Submodule.mem_map_of_mem (f := ρ g) hw)
      have h := apply_conj_apply (ρ := ρ) g⁻¹ t (ρ g w)
      simp only [inv_inv, Representation.inv_self_apply] at h
      rw [htw, Representation.inv_self_apply] at h
      exact h
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * t * g, ⟨hsT, hsW⟩, ?_⟩
    change (MulAut.conj g) (g⁻¹ * t * g) = t
    rw [MulAut.conj_apply]
    group
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply] using
        (Subgroup.mem_set_normalizer_iff.mp hg s).mp hs.1
    · intro w hw
      obtain ⟨w0, hw0, rfl⟩ := Submodule.mem_map.mp hw
      change ρ (g * s * g⁻¹) (ρ g w0) = ρ g w0
      rw [apply_conj_apply (ρ := ρ) g s w0, hs.2 w0 hw0]

theorem mem_normalizer_kernelIn_of_le [Finite Γ] {T : Subgroup Γ}
    {W : Submodule (ZMod p) V} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (T : Set Γ))
    (h : kernelIn ρ T W ≤ kernelIn ρ T (W.map (ρ g))) :
    g ∈ Subgroup.normalizer (kernelIn ρ T W : Set Γ) := by
  have heq := kernelIn_map_conj (ρ := ρ) (T := T) (W := W) (g := g) hg
  have hcard : Nat.card (kernelIn ρ T (W.map (ρ g))) = Nat.card (kernelIn ρ T W) := by
    rw [heq, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heqsub : kernelIn ρ T W = kernelIn ρ T (W.map (ρ g)) :=
    Subgroup.eq_of_le_of_card_ge h hcard.le
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq.symm.trans heqsub.symm

theorem exists_apply_ne_of_exists_map {T : Subgroup Γ} {U : Submodule (ZMod p) V}
    {g : Γ} (hg : g ∈ Subgroup.normalizer (T : Set Γ))
    (hTU : ∃ t ∈ T, ∃ u ∈ U, ρ t u ≠ u) :
    ∃ t ∈ T, ∃ w ∈ U.map (ρ g), ρ t w ≠ w := by
  obtain ⟨t, ht, u, hu, htu⟩ := hTU
  have hgT : g * t * g⁻¹ ∈ T :=
    (Subgroup.mem_set_normalizer_iff.mp hg t).mp ht
  refine ⟨g * t * g⁻¹, hgT, ρ g u, Submodule.mem_map_of_mem (f := ρ g) hu, ?_⟩
  intro h
  apply htu
  have h' := congrArg (fun v => ρ g⁻¹ v) h
  simpa only [apply_conj_apply, Representation.inv_self_apply] using h'

theorem exists_mem_kernelIn_forall_eq_neg_of_not_mem_normalizer [Finite Γ]
    {T : Subgroup Γ} (hTN : T ≤ N)
    (hN : N ≤ Subgroup.normalizer (T : Set Γ)) (hp2 : p ≠ 2)
    {g : Γ} (hgT : g ∈ Subgroup.normalizer (T : Set Γ))
    {U : Submodule (ZMod p) V} (hW : IsSimpleUnder ρ N (U.map (ρ g)))
    (hTW : ∃ t ∈ T, ∃ w ∈ U.map (ρ g), ρ t w ≠ w)
    (hgK : g ∉ Subgroup.normalizer (kernelIn ρ T U : Set Γ))
    (hQ : ∀ W, IsSimpleUnder ρ N W → (∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) →
      ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
        ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w)
    [Fintype (kernelIn ρ T U)] :
    ∃ s ∈ kernelIn ρ T U, ∀ w ∈ U.map (ρ g), ρ (s : Γ) w = -w := by
  have hnotle : ¬ kernelIn ρ T U ≤ kernelIn ρ T (U.map (ρ g)) := by
    intro hle
    exact hgK (mem_normalizer_kernelIn_of_le (ρ := ρ) hgT hle)
  obtain ⟨s, hsK0, hsKi⟩ := Set.not_subset.mp hnotle
  have hsT : s ∈ T := hsK0.1
  have hsW : ¬ ∀ w ∈ U.map (ρ g), ρ s w = w := by
    intro hfixW
    exact hsKi ⟨hsT, hfixW⟩
  obtain ⟨φ, _, hφker⟩ := hQ _ hW hTW
  have hφne : φ ⟨s, hsT⟩ ≠ 1 := by
    intro h1
    exact hsW ((hφker ⟨s, hsT⟩).mp h1)
  have hsK0sub : (⟨s, hsT⟩ : ↥T) ∈ (kernelIn ρ T U).subgroupOf T := by
    rw [Subgroup.mem_subgroupOf]
    exact hsK0
  have hmemφ : φ ⟨s, hsT⟩ ∈ ((kernelIn ρ T U).subgroupOf T).map φ :=
    Subgroup.mem_map_of_mem φ hsK0sub
  have hmap_ne : ((kernelIn ρ T U).subgroupOf T).map φ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hmemφ
    exact hφne (by simpa using hmemφ)
  have ha2 : QuaternionGroup.a 2 ∈ ((kernelIn ρ T U).subgroupOf T).map φ :=
    CFSG.GroupTheory.quaternion_a_two_mem_of_ne_bot hmap_ne
  obtain ⟨s', hs'mem, hs'φ⟩ := Subgroup.mem_map.mp ha2
  have hs'K0 : (s' : Γ) ∈ kernelIn ρ T U := by
    rwa [Subgroup.mem_subgroupOf] at hs'mem
  exact ⟨s', hs'K0, acts_neg_one_of_quaternion_kernel hTN hN hW hφker hs'φ hp2⟩

theorem sumMap_apply_eq_zero_of_not_mem_normalizer_kernelIn [Finite Γ]
    {T : Subgroup Γ} (hTN : T ≤ N)
    (hN : N ≤ Subgroup.normalizer (T : Set Γ)) (hp2 : p ≠ 2)
    {r : ℕ} (hr : r.Prime) {x : Γ}
    (hxN : x ∈ Subgroup.normalizer (N : Set Γ))
    (hxT : x ∈ Subgroup.normalizer (T : Set Γ)) (hxr : x ^ r = 1)
    {U : Submodule (ZMod p) V} (hU : IsSimpleUnder ρ N U)
    (hTU : ∃ t ∈ T, ∃ u ∈ U, ρ t u ≠ u)
    (hxK : x ∉ Subgroup.normalizer (kernelIn ρ T U : Set Γ))
    {i : ℕ} (hi0 : 0 < i) (hir : i < r)
    (hQ : ∀ W, IsSimpleUnder ρ N W → (∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) →
      ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
        ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w)
    [Fintype (kernelIn ρ T U)] :
    ∀ u ∈ U, sumMap ρ (kernelIn ρ T U) (ρ (x ^ i) u) = 0 := by
  intro u hu
  let W : Submodule (ZMod p) V := U.map (ρ (x ^ i))
  have hxiN : x ^ i ∈ Subgroup.normalizer (N : Set Γ) :=
    Subgroup.pow_mem (Subgroup.normalizer (N : Set Γ)) hxN i
  have hxiT : x ^ i ∈ Subgroup.normalizer (T : Set Γ) :=
    Subgroup.pow_mem (Subgroup.normalizer (T : Set Γ)) hxT i
  have hW : IsSimpleUnder ρ N W := IsSimpleUnder.map hU hxiN
  have hTW : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w :=
    exists_apply_ne_of_exists_map (ρ := ρ) (U := U) (g := x ^ i) hxiT hTU
  have hxiK : x ^ i ∉ Subgroup.normalizer (kernelIn ρ T U : Set Γ) :=
    fun h => hxK (pow_mem_normalizer_of_prime hr hi0 hir hxr h)
  obtain ⟨s, hsK, hneg⟩ := exists_mem_kernelIn_forall_eq_neg_of_not_mem_normalizer
    (ρ := ρ) (T := T) (U := U) (g := x ^ i) hTN hN hp2 hxiT hW hTW hxiK hQ
  exact sumMap_apply_eq_zero_of_neg (K := kernelIn ρ T U) (s := ⟨s, hsK⟩)
    (hneg _ (Submodule.mem_map_of_mem (f := ρ (x ^ i)) hu)) hp2

theorem sumMap_sum_range_apply_eq_card_smul {K : Subgroup Γ} [Fintype K]
    {r : ℕ} (hr : 0 < r) {x : Γ} (u : V)
    (hvan : ∀ i, 0 < i → i < r → sumMap ρ K (ρ (x ^ i) u) = 0)
    (hfix : ∀ k : K, ρ (k : Γ) u = u) :
    sumMap ρ K (Finset.sum (Finset.range r) (fun i => ρ (x ^ i) u)) =
      (Nat.card K : ZMod p) • u := by
  rw [map_sum]
  have hsplit : (Finset.sum (Finset.range r) (fun i => sumMap ρ K (ρ (x ^ i) u))) =
      (Finset.sum (Finset.range (r - 1))
        (fun j => sumMap ρ K (ρ (x ^ (j + 1)) u))) + sumMap ρ K u := by
    rw [show r = (r - 1) + 1 by omega, Finset.sum_range_succ']
    simp
  rw [hsplit, Finset.sum_eq_zero, zero_add,
    sumMap_apply_eq_card_smul (K := K) (u := u) hfix]
  intro j hj
  have hj' : j < r - 1 := Finset.mem_range.mp hj
  exact hvan (j + 1) (by omega) (by omega)

theorem conj_acts_trivially_of_quaternion_quotients [Finite Γ]
    {T : Subgroup Γ} (hTN : T ≤ N)
    (hN : N ≤ Subgroup.normalizer (T : Set Γ)) (hT : IsPGroup 2 T) (hp2 : p ≠ 2)
    {r : ℕ} (hr : r.Prime) {x : Γ}
    (hxN : x ∈ Subgroup.normalizer (N : Set Γ))
    (hxT : x ∈ Subgroup.normalizer (T : Set Γ)) (hxr : x ^ r = 1)
    (hfix : ∀ v, ρ x v = v → v = 0)
    (hQ : ∀ W, IsSimpleUnder ρ N W → (∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) →
      ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
        ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w)
    {U : Submodule (ZMod p) V} (hU : IsSimpleUnder ρ N U)
    {t : Γ} (ht : t ∈ T) (htU : ∀ u ∈ U, ρ t u = u) :
    ∀ u ∈ U, ρ (x * t * x⁻¹) u = u := by
  by_cases hTU : ∃ s ∈ T, ∃ u ∈ U, ρ s u ≠ u
  · have hxK0 : x ∈ Subgroup.normalizer (kernelIn ρ T U : Set Γ) := by
      by_contra hxK
      let K : Subgroup Γ := kernelIn ρ T U
      letI : Fintype K := Fintype.ofFinite K
      obtain ⟨u, huU, hune⟩ : ∃ u ∈ U, u ≠ 0 := by
        obtain ⟨s, hs, u, hu, hsu⟩ := hTU
        exact ⟨u, hu, fun h0 => hsu (by simp [h0])⟩
      let v : V := Finset.sum (Finset.range r) (fun i => ρ (x ^ i) u)
      have hvfix : ρ x v = v := apply_sum_range_pow_apply hxr u
      have hv0 : v = 0 := hfix v hvfix
      have hO1e : ∀ i, 0 < i → i < r → sumMap ρ K (ρ (x ^ i) u) = 0 := by
        intro i hi0 hir
        exact sumMap_apply_eq_zero_of_not_mem_normalizer_kernelIn (ρ := ρ) (N := N)
          hTN hN hp2 hr hxN hxT hxr hU hTU hxK hi0 hir hQ u huU
      have hrpos : 0 < r := hr.pos
      have hPv : sumMap ρ K v = (Nat.card K : ZMod p) • u :=
        sumMap_sum_range_apply_eq_card_smul (K := K) hrpos u hO1e
          (fun k => k.2.2 u huU)
      have hcoeff : (Nat.card K : ZMod p) ≠ 0 :=
        CFSG.SolvableHall.natCast_card_ne_zero_of_isPGroup (p := p) (q := 2)
          (Fact.out) Nat.prime_two (Ne.symm hp2) (IsPGroup.to_le hT (fun s hs => hs.1))
      have hzero : (Nat.card K : ZMod p) • u = 0 := by
        rw [← hPv, hv0, map_zero]
      exact hune ((smul_eq_zero.mp hzero).resolve_left hcoeff)
    have htK0 : t ∈ kernelIn ρ T U := ⟨ht, htU⟩
    have hconj : x * t * x⁻¹ ∈ kernelIn ρ T U :=
      (Subgroup.mem_set_normalizer_iff.mp hxK0 t).mp htK0
    exact fun u hu => hconj.2 u hu
  · push Not at hTU
    have hxT' : x * t * x⁻¹ ∈ T :=
      (Subgroup.mem_set_normalizer_iff.mp hxT t).mp ht
    exact fun u hu => hTU (x * t * x⁻¹) hxT' u hu

theorem mulAut_zpow_apply_eq_of_apply_eq {H K : Type*} [Group H] [Group K]
    (φ : H →* K) (c : MulAut H) (hc : ∀ s : H, φ (c s) = φ s)
    (k : ℤ) (s : H) : φ ((c ^ k) s) = φ s := by
  let S : Subgroup (MulAut H) :=
    { carrier := {d | ∀ s : H, φ (d s) = φ s}
      one_mem' := by intro s; simp
      mul_mem' := by
        rintro d e hd he s
        rw [MulAut.mul_apply]
        exact (hd (e s)).trans (he s)
      inv_mem' := by
        rintro d hd s
        have := hd (d⁻¹ s)
        simpa using this.symm }
  exact Subgroup.zpow_mem (K := S) hc k s

theorem normalizerMonoidHom_zpow_apply_coe {T : Subgroup Γ} {x : Γ}
    (hxT : x ∈ Subgroup.normalizer (T : Set Γ)) (k : ℤ) (s : ↥T) :
    (((Subgroup.normalizerMonoidHom T ⟨x, hxT⟩) ^ k) s : Γ) =
      x ^ k * (s : Γ) * (x ^ k)⁻¹ := by
  have hc : (Subgroup.normalizerMonoidHom T ⟨x, hxT⟩) ^ k =
      Subgroup.normalizerMonoidHom T (⟨x, hxT⟩ ^ k) := by
    rw [← map_zpow]
  rw [hc, Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp

theorem commutator_zpowers_le_kernelIn {T : Subgroup Γ} {U : Submodule (ZMod p) V}
    {x : Γ} {φ : ↥T →* QuaternionGroup 2} {c : MulAut ↥T}
    (hφker : ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ U, ρ (t : Γ) w = w)
    (hcpow : ∀ k : ℤ, ∀ s : ↥T, φ ((c ^ k) s) = φ s)
    (hcoe : ∀ (k : ℤ) (s : ↥T),
      (((c ^ k) s : ↥T) : Γ) = x ^ k * (s : Γ) * (x ^ k)⁻¹) :
    ⁅Subgroup.zpowers x, T⁆ ≤ kernelIn ρ T U := by
  rw [Subgroup.commutator_le]
  intro a ha s hs
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  let sT : ↥T := ⟨s, hs⟩
  let s' : ↥T := (c ^ k) sT
  have hφcomm : φ (s' * sT⁻¹) = 1 := by
    rw [map_mul, map_inv, hcpow k sT, mul_inv_cancel]
  have hcoe' : ((s' * sT⁻¹ : ↥T) : Γ) = ⁅x ^ k, s⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe k sT, commutatorElement_def]
  refine ⟨?_, ?_⟩
  · rw [← hcoe']
    exact (s' * sT⁻¹).2
  · intro u hu
    rw [← hcoe']
    exact (hφker (s' * sT⁻¹)).mp hφcomm u hu

theorem acts_trivially_of_quaternion_quotients [Finite Γ]
    {T : Subgroup Γ} (hTN : T ≤ N)
    (hN : N ≤ Subgroup.normalizer (T : Set Γ)) (hT : IsPGroup 2 T) (hp2 : p ≠ 2)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) {x : Γ}
    (hxN : x ∈ Subgroup.normalizer (N : Set Γ))
    (hxT : x ∈ Subgroup.normalizer (T : Set Γ)) (hxr : x ^ r = 1)
    (hfix : ∀ v, ρ x v = v → v = 0)
    (hQ : ∀ W, IsSimpleUnder ρ N W → (∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) →
      ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
        ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w)
    (hTx : ⁅Subgroup.zpowers x, T⁆ = T)
    {U : Submodule (ZMod p) V} (hU : IsSimpleUnder ρ N U) :
    ∀ t ∈ T, ∀ u ∈ U, ρ t u = u := by
  by_cases hTU : ∃ s ∈ T, ∃ u ∈ U, ρ s u ≠ u
  · obtain ⟨φ, hφsurj, hφker⟩ := hQ U hU hTU
    let xN : Subgroup.normalizer (T : Set Γ) := ⟨x, hxT⟩
    have hxrN : xN ^ r = 1 := Subtype.ext (by simpa [xN] using hxr)
    have hker : ∀ s : ↥T, φ s = 1 →
        φ (Subgroup.normalizerMonoidHom T xN s) = 1 := by
      intro s hs
      have hsU : ∀ u ∈ U, ρ (s : Γ) u = u := (hφker s).mp hs
      have hconj := conj_acts_trivially_of_quaternion_quotients (ρ := ρ) (N := N)
        hTN hN hT hp2 hr hxN hxT hxr hfix hQ hU s.2 hsU
      have hmem : x * (s : Γ) * x⁻¹ ∈ T :=
        (Subgroup.mem_set_normalizer_iff.mp hxT (s : Γ)).mp s.2
      have hφ1 : φ (⟨x * (s : Γ) * x⁻¹, hmem⟩ : ↥T) = 1 := (hφker _).mpr hconj
      have heq : (⟨x * (s : Γ) * x⁻¹, hmem⟩ : ↥T) =
          Subgroup.normalizerMonoidHom T xN s := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rwa [heq] at hφ1
    have hφconj : ∀ s : ↥T, φ (Subgroup.normalizerMonoidHom T xN s) = φ s :=
      fun s => CFSG.GroupTheory.quaternion_map_normalizerMonoidHom_eq φ hφsurj xN hker
        hr hr5 hxrN s
    let c : MulAut ↥T := Subgroup.normalizerMonoidHom T xN
    have hc : ∀ s : ↥T, φ (c s) = φ s := hφconj
    have hcpow : ∀ k : ℤ, ∀ s : ↥T, φ ((c ^ k) s) = φ s :=
      fun k s => mulAut_zpow_apply_eq_of_apply_eq φ c hc k s
    have hcoe_cpow : ∀ (k : ℤ) (s : ↥T),
        (((c ^ k) s : ↥T) : Γ) = x ^ k * (s : Γ) * (x ^ k)⁻¹ := by
      intro k s
      simpa [c, xN] using normalizerMonoidHom_zpow_apply_coe (T := T) hxT k s
    have hle := commutator_zpowers_le_kernelIn (ρ := ρ) (T := T) (U := U) (x := x)
      (φ := φ) (c := c) hφker hcpow hcoe_cpow
    have hTK : T ≤ kernelIn ρ T U := by
      have h := hle
      rw [hTx] at h
      exact h
    intro t ht u hu
    exact (hTK ht).2 u hu
  · push Not at hTU
    intro t ht u hu
    exact hTU t ht u hu

end CFSG.RepresentationTheory

