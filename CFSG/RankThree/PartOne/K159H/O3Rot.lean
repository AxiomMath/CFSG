module

public import CFSG.RankThree.PartOne.K159H.O3Omega
public import CFSG.RankThree.PartOne.K159H.O3Restrict
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

theorem ext_frame_tail {f g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (h1 : ∀ j, f (hypVec K A j) = g (hypVec K A j))
    (h2 : ∀ a : A, f ((0 : Fin r ⊕ Fin r → K), a) = g ((0 : Fin r ⊕ Fin r → K), a)) : f = g := by
  refine LinearEquiv.ext fun v => ?_
  rw [vec_expand v, map_add, map_add, map_sum, map_sum, h2]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, h1]

@[expose] def Rot (qA : QuadraticForm K A) (r : ℕ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  carrier := {g | g ∈ Om qA r ∧ ∀ j, g (hypVec K A j) = hypVec K A j}
  mul_mem' := by
    rintro g k ⟨hg, hgf⟩ ⟨hk, hkf⟩
    refine ⟨mul_mem hg hk, fun j => ?_⟩
    rw [LinearEquiv.mul_apply, hkf, hgf]
  one_mem' := ⟨one_mem _, fun j => rfl⟩
  inv_mem' := by
    rintro g ⟨hg, hgf⟩
    refine ⟨inv_mem hg, fun j => ?_⟩
    conv_lhs => rw [← hgf j]
    exact LinearEquiv.inv_apply_apply' g _

variable {qA : QuadraticForm K A}

theorem rot_coord {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA))
    (hgf : ∀ j, g (hypVec K A j) = hypVec K A j) (x : (Fin r ⊕ Fin r → K) × A) (j : Fin r ⊕ Fin r) :
    (g x).1 j = x.1 j := by
  have h := polar_map_of_mem hgO x (hypVec K A j.swap)
  rw [hgf, polar_hypVec, polar_hypVec, Sum.swap_swap] at h
  exact h

@[expose] def tailSub (K : Type) [Field K] (A : Type) [AddCommGroup A] [Module K A] (r : ℕ) :
    Submodule K ((Fin r ⊕ Fin r → K) × A) where
  carrier := {v | v.1 = 0}
  add_mem' {a b} ha hb := by
    have ha' : a.1 = 0 := ha
    have hb' : b.1 = 0 := hb
    simp [ha', hb']
  zero_mem' := rfl
  smul_mem' c v hv := by
    have hv' : v.1 = 0 := hv
    simp [hv']

theorem mem_tailSub {v : (Fin r ⊕ Fin r → K) × A} : v ∈ tailSub K A r ↔ v.1 = 0 := Iff.rfl

theorem finrank_tailSub [FiniteDimensional K A] :
    finrank K (tailSub K A r) = finrank K A := by
  have : tailSub K A r = LinearMap.range (LinearMap.inr K (Fin r ⊕ Fin r → K) A) := by
    ext v
    simp only [mem_tailSub, LinearMap.mem_range, LinearMap.inr_apply]
    constructor
    · intro h
      exact ⟨v.2, Prod.ext h.symm rfl⟩
    · rintro ⟨a, rfl⟩
      rfl
  rw [this]
  exact (LinearEquiv.ofInjective (LinearMap.inr K (Fin r ⊕ Fin r → K) A) LinearMap.inr_injective).symm.finrank_eq

theorem polar_tail_eq_zero_iff (hreg : (polarBilin qA).Nondegenerate) (z : (Fin r ⊕ Fin r → K) × A) :
    (∀ x ∈ tailSub K A r, polar (quadTail r qA) z x = 0) ↔ z.2 = 0 := by
  constructor
  · intro h
    refine eq_zero_of_polar_eq_zero hreg fun a => ?_
    have := h ((0 : Fin r ⊕ Fin r → K), a) rfl
    rw [polar_quadTail, polar_zero_right, zero_add] at this
    exact this
  · intro h x hx
    rw [polar_quadTail, mem_tailSub.mp hx, h, polar_zero_left, polar_zero_right, add_zero]

theorem regular_tailSub (hreg : (polarBilin qA).Nondegenerate) :
    (polarBilin ((quadTail r qA).restrict (tailSub K A r))).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun x hx => ?_
  have hx1 : (x : (Fin r ⊕ Fin r → K) × A).1 = 0 := x.2
  have hx2 : (x : (Fin r ⊕ Fin r → K) × A).2 = 0 := by
    refine eq_zero_of_polar_eq_zero hreg fun a => ?_
    have := hx ⟨((0 : Fin r ⊕ Fin r → K), a), rfl⟩
    simp only [polar_restrict] at this
    rwa [polar_quadTail, hx1, polar_zero_left, zero_add] at this
  exact Subtype.ext (Prod.ext hx1 hx2)

theorem fix_of_frame_fix {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hgf : ∀ j, g (hypVec K A j) = hypVec K A j) (z : (Fin r ⊕ Fin r → K) × A) (hz : z.2 = 0) :
    g z = z := by
  conv_lhs => rw [vec_expand z]
  conv_rhs => rw [vec_expand z]
  rw [hz]
  have h0 : ((0 : Fin r ⊕ Fin r → K), (0 : A)) = (0 : (Fin r ⊕ Fin r → K) × A) := rfl
  rw [h0, add_zero, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hgf]

theorem torH_eq_of_fst_zero (d : Fin r → Kˣ) {v : (Fin r ⊕ Fin r → K) × A} (hv : v.1 = 0) :
    torH K A r d v = v :=
  Prod.ext (funext fun c => by simp [torH_fst, hv]) rfl

section Facts

variable [Finite K] [CharP K 2] [FiniteDimensional K A] (hreg : (polarBilin qA).Nondegenerate) (hr : 3 ≤ r)
include hreg hr

omit [Finite K] [CharP K 2] [FiniteDimensional K A] hr in
theorem rot_supp {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hg : g ∈ Rot qA r) :
    (∀ x, x ∈ tailSub K A r ↔ g x ∈ tailSub K A r) ∧
      ∀ z, (∀ x ∈ tailSub K A r, polar (quadTail r qA) z x = 0) → g z = z := by
  have hgO := Om_le_orth hg.1
  refine ⟨fun x => ?_, fun z hz => fix_of_frame_fix hg.2 z ((polar_tail_eq_zero_iff hreg z).1 hz)⟩
  rw [mem_tailSub, mem_tailSub]
  constructor
  · intro h
    funext j
    rw [rot_coord hgO hg.2 x j, h]
  · intro h
    funext j
    have := rot_coord hgO hg.2 x j
    rw [← this, h]

theorem Rot_comm (hdim : finrank K A = 2) {g k : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ Rot qA r) (hk : k ∈ Rot qA r) : g * k = k * g := by
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  have hS := regular_tailSub (r := r) hreg
  obtain ⟨hgS, hgfix⟩ := rot_supp hreg hg
  obtain ⟨hkS, hkfix⟩ := rot_supp hreg hk
  have hgΩ : g ∈ omegaGroup (quadTail r qA) hQ := by
    have := hg.1
    rwa [Om_eq_omega hreg hr] at this
  have hkΩ : k ∈ omegaGroup (quadTail r qA) hQ := by
    have := hk.1
    rwa [Om_eq_omega hreg hr] at this
  have hg' := resAut_mem_omega hS hgΩ hgS hgfix
  have hk' := resAut_mem_omega hS hkΩ hkS hkfix
  have hcomm := CFSG.RankThree.PartOne.KCOrthogonal.commute_of_dicksonHom_eq_one hS
    (by rw [finrank_tailSub, hdim]) hg'.1 hk'.1 (dicksonHom_eq_one_of_mem_omega hS hg')
    (dicksonHom_eq_one_of_mem_omega hS hk')
  exact comm_of_resAut_comm hS hgS hkS hgfix hkfix hcomm

omit [Finite K] [CharP K 2] [FiniteDimensional K A] hreg hr in
theorem torH_comm_Rot (d : Fin r → Kˣ) {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ Rot qA r) : torH K A r d * g = g * torH K A r d := by
  have hgO := Om_le_orth hg.1
  refine ext_frame_tail (fun j => ?_) (fun a => ?_)
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg.2, torH_hypVec, map_smul, hg.2]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, torH_snd_zero]
    refine torH_eq_of_fst_zero d (funext fun j => ?_)
    rw [rot_coord hgO hg.2]

end Facts

end CFSG.RankThree.PartOne.K159H
