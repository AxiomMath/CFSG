module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C623Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623a
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S27

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem c623_of_kernels (hr3 : m.r = 3) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (h621 : m.C621) (h621x : m.C621x) : m.C623 := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hsix := m.hZ.sixteen h69
  intro g hg
  by_contra hne
  have hRsyl : IsSylowOf m.r m.R ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, m.d.sylow.isPGroup, ?_⟩
    have := m.toMc614.sylowTop.not_dvd_index
    rw [m.toMc614.coe_sylowTop] at this
    rwa [Subgroup.relIndex_top_right]
  have hZgA : CFSG.conjugate m.Z g ≤ m.A := by
    intro x hx
    have hxR := hg hx
    have hxz : g * x * g⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hx
    have hpow : (g * x * g⁻¹) ^ m.r = 1 := (isElemAbelian_of_card_prime m.hr m.card_Z).2 _ hxz
    have hx1 : x ^ m.r = 1 := by
      have h1 : (MulAut.conj g) (x ^ m.r) = 1 := by
        rw [map_pow, MulAut.conj_apply]
        exact hpow
      exact (MulAut.conj g).injective (h1.trans (map_one _).symm)
    exact hsix.2 x hxR hx1
  have hZ' : ∀ z ∈ m.Z, ∀ x ∈ m.R, x * z = z * x := fun z hz x hx =>
    (hsix.1 z (m.Z_le_A hz) x hx).symm
  have hZg' : ∀ z ∈ m.Z, ∀ x ∈ m.R, x * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x := by
    intro z hz x hx
    have hmem : g⁻¹ * z * g ∈ CFSG.conjugate m.Z g := by
      rw [mem_conjugate_iff_uc6]
      have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rw [e]
      exact hz
    exact (hsix.1 _ (hZgA hmem) x hx).symm
  obtain ⟨n, hnR, hn⟩ := exists_mem_normalizer_conj_eq hRsyl hZ' hZg'
  have hnA : n ∈ normalizer (m.A : Set G) := by
    refine mem_normalizer_of_forward_uc6 fun a ha => ?_
    have haR : a ∈ m.R := m.A_le_R ha
    have hnaR : n * a * n⁻¹ ∈ m.R := (mem_normalizer_iff.1 hnR a).1 haR
    have hpow : (n * a * n⁻¹) ^ m.r = 1 := by
      have h1 : a ^ m.r = 1 := m.isElemAbelian_A.2 a ha
      have h2 : (MulAut.conj n) (a ^ m.r) = 1 := by rw [h1, map_one]
      rwa [map_pow, MulAut.conj_apply] at h2
    exact hsix.2 _ hnaR hpow
  have hnZ : n ∉ normalizer (m.Z : Set G) := by
    intro hnZ
    apply hne
    have hcardc : Nat.card (CFSG.conjugate m.Z g) = Nat.card m.Z :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    refine Subgroup.eq_of_le_of_card_ge ?_ hcardc.ge
    intro x hx
    have hxz : g * x * g⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hx
    have h1 := hn _ hxz
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e] at h1
    rw [← h1]
    exact (mem_normalizer_iff''.1 hnZ _).1 hxz
  have hZL : m.Z ⊓ m.L = ⊥ := inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2
  have hZP : m.Z ⊓ (m.A ⊓ m.L) = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hZL]
    exact inf_le_inf_left _ inf_le_right
  have hRC : m.R ≤ centralizer (m.A : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun a ha => hsix.1 a ha x hx
  have hRW : m.R ≤ normalizer (m.A : Set G) := hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hRWsyl : IsSylowOf m.r m.R (normalizer (m.A : Set G)) := hRsyl.of_le hRW le_top
  have hndvd := (isSylowOf_iff.1 hRWsyl).2.2
  have hRC' : m.R ≤ centralizer (m.A : Set G) ⊓ normalizer (m.A : Set G) := le_inf hRC hRW
  have hcop : ¬ 3 ∣ (centralizer (m.A : Set G) ⊓ normalizer (m.A : Set G)).relIndex
      (normalizer (m.A : Set G)) := by
    intro hd
    apply hndvd
    rw [← Subgroup.relIndex_mul_relIndex m.R _ _ hRC' inf_le_right, hr3]
    exact hd.mul_left _
  have hNP : m.L ⊓ normalizer (m.A : Set G) ≤ normalizer ((m.A ⊓ m.L : Subgroup G) : Set G) := by
    intro n' hn'
    refine mem_normalizer_of_forward_uc6 fun p hp => ?_
    exact ⟨(mem_normalizer_iff.1 hn'.2 p).1 hp.1,
      m.L.mul_mem (m.L.mul_mem hn'.1 hp.2) (m.L.inv_mem hn'.1)⟩
  have hA : IsElemAbelian 3 m.A := by
    have := m.isElemAbelian_A
    rwa [hr3] at this
  have hAcard : Nat.card m.A = 3 ^ 3 := by rw [m.card_A, hr3]
  have hZcard : Nat.card m.Z = 3 := by rw [m.card_Z, hr3]
  have hPcard : Nat.card (m.A ⊓ m.L : Subgroup G) = 3 ^ 2 := by rw [m.card_A_inf_L h620, hr3]
  obtain ⟨x, hxW, hx4, hxZ⟩ := h621x
  exact false_of_irreducible_triple hA hAcard hZP m.Z_le_A inf_le_left hZcard hPcard le_rfl
    inf_le_right hNP (fun n' hn' z hz => (m.Z_comm_L hz hn'.1).symm) h621 hcop
    (fun h => hnZ (h hnA)) x hxW hx4 hxZ

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
