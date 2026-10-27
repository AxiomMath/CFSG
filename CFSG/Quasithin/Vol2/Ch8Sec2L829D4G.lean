module

public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SMB
public import CFSG.Quasithin.Vol2.Ch8Sec2L829D4Nf

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Quasithin CFSG.Quasithin.AutOn CFSG.Open
open scoped IsMulCommutative commutatorElement

section Dict

variable {G : Type} [Group G]

theorem mem_normalizer_stab_sd4 {V U : Subgroup G} [IsMulCommutative ↥V] {Uv : Subgroup ↥V}
    (hUv : ∀ u : ↥V, u ∈ Uv ↔ (u : G) ∈ U) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hU : U ≤ V) :
    x ∈ Subgroup.normalizer (U : Set G) ↔ conjAct V ⟨x, hx⟩ ∈ stabSub (V := ↥V) Uv := by
  have hconj : ∀ u : ↥V, ((conjAct V ⟨x, hx⟩ u : ↥V) : G) = x * (u : G) * x⁻¹ :=
    fun u => AutOn.coe_conjAct_apply V ⟨x, hx⟩ u
  constructor
  · intro hxU
    refine fun u => ?_
    rw [hUv, hUv, hconj]
    exact (Subgroup.mem_normalizer_iff.mp hxU (u : G)).symm
  · intro hstab
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgV : g ∈ V := hU hg
      have h1 := hstab ⟨g, hgV⟩
      rw [hUv, hUv, hconj] at h1
      exact h1.mpr hg
    · intro hg
      have hgV : g ∈ V := (Subgroup.mem_normalizer_iff.mp hx g).mpr (hU hg)
      have h1 := hstab ⟨g, hgV⟩
      rw [hUv, hUv, hconj] at h1
      exact h1.mp hg

theorem autOn_inf_stab_sd4 {V L U : Subgroup G} [IsMulCommutative ↥V] {Uv : Subgroup ↥V}
    (hUv : ∀ u : ↥V, u ∈ Uv ↔ (u : G) ∈ U)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V) :
    autOn (L ⊓ Subgroup.normalizer (U : Set G)) V = autOn L V ⊓ stabSub (V := ↥V) Uv := by
  ext φ
  rw [Subgroup.mem_inf, AutOn.mem_autOn_iff_exists, AutOn.mem_autOn_iff_exists]
  constructor
  · rintro ⟨x, hx, ⟨hxL, hxN⟩, rfl⟩
    exact ⟨⟨x, hx, hxL, rfl⟩, (mem_normalizer_stab_sd4 hUv hx hUV).mp hxN⟩
  · rintro ⟨⟨x, hx, hxL, hφ⟩, hstab⟩
    refine ⟨x, hx, ⟨hxL, (mem_normalizer_stab_sd4 hUv hx hUV).mpr ?_⟩, hφ⟩
    rw [hφ]
    exact hstab

theorem autOn_perfectCore_sd4 [Finite G] {V Y : Subgroup G} [IsMulCommutative ↥V]
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) :
    autOn (CFSG.Quasithin.perfectCore Y) V = CFSG.Quasithin.perfectCore (autOn Y V) := by
  haveI : Finite (MulAut ↥V) := CFSG.Quasithin.H.ZTrans.finite_mulAut_z (V := ↥V)
  unfold autOn
  exact (CFSG.Quasithin.H.Mathieu.perfectCore_map_subgroupOf hY (conjAct V)).symm

theorem autOn_LU_sd4 [Finite G] {V L U : Subgroup G} [IsMulCommutative ↥V] {Uv : Subgroup ↥V}
    (hUv : ∀ u : ↥V, u ∈ Uv ↔ (u : G) ∈ U)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V) :
    autOn (CFSG.Quasithin.H13.ch82LU L U) V = D4P_sd4 (V := ↥V) (autOn L V) Uv := by
  unfold CFSG.Quasithin.H13.ch82LU D4P_sd4
  rw [autOn_perfectCore_sd4 (inf_le_left.trans hLV), autOn_inf_stab_sd4 hUv hLV hUV]

section Module

variable {V : Type} [CommGroup V]

theorem comm_sd4_eq_s828_sd4 (Y : Subgroup (MulAut V)) :
    comm_sd4 Y = CFSG.Quasithin.H13.s828CommSub Y ⊤ := by
  unfold comm_sd4 CFSG.Quasithin.H13.s828CommSub
  congr 1
  ext x
  simp

theorem s828CommSub_mono_sd4 (Y : Subgroup (MulAut V)) {W W' : Subgroup V} (h : W ≤ W') :
    CFSG.Quasithin.H13.s828CommSub Y W ≤ CFSG.Quasithin.H13.s828CommSub Y W' := by
  unfold CFSG.Quasithin.H13.s828CommSub
  refine Subgroup.closure_mono ?_
  rintro x ⟨y, hy, w, hw, rfl⟩
  exact ⟨y, hy, w, h hw, rfl⟩

theorem s828CommSub_invariant_sd4 (Y : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ p ∈ Y, ∀ w ∈ W, p w ∈ W) :
    ∀ p ∈ Y, ∀ c ∈ CFSG.Quasithin.H13.s828CommSub Y W,
      p c ∈ CFSG.Quasithin.H13.s828CommSub Y W := by
  intro p hp
  have hS : ∀ x ∈ {x : V | ∃ y ∈ Y, ∃ w ∈ W, x = y w * w⁻¹},
      p x ∈ CFSG.Quasithin.H13.s828CommSub Y W := by
    rintro x ⟨y, hy, w, hw, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨p * y * p⁻¹, Y.mul_mem (Y.mul_mem hp hy) (Y.inv_mem hp), p w, hW p hp w hw, ?_⟩
    have e : (p * y * p⁻¹) (p w) = p (y w) := by
      rw [MulAut.mul_apply, MulAut.mul_apply]
      congr 1
      rw [MulAut.inv_apply_self]
    rw [e, map_mul, map_inv]
  have hcl : CFSG.Quasithin.H13.s828CommSub Y W ≤
      (CFSG.Quasithin.H13.s828CommSub Y W).comap (p : V →* V) := by
    unfold CFSG.Quasithin.H13.s828CommSub
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    exact hS x hx
  intro c hc
  exact hcl hc

theorem sup_comm_eq_sd4 {Pv : Subgroup (MulAut V)} {Uv Nv : Subgroup V}
    (hUN : Uv ≤ Nv) (hNv : Nv = comm_sd4 Pv)
    (hirr : ∀ C : Subgroup V, Uv ≤ C → C ≤ Nv → (∀ p ∈ Pv, ∀ c ∈ C, p c ∈ C) →
      C = Uv ∨ C = Nv)
    (hnab : ∃ p ∈ Pv, ∃ q ∈ Pv, ∃ n ∈ Nv, ((⁅p, q⁆ : MulAut V)⁻¹ n) * n⁻¹ ∉ Uv)
    (hUinv : ∀ p ∈ Pv, ∀ u ∈ Uv, p u ∈ Uv) :
    CFSG.Quasithin.H13.s828CommSub Pv Nv ⊔ Uv = Nv := by
  have hNinv : ∀ p ∈ Pv, ∀ w ∈ Nv, p w ∈ Nv := by
    intro p hp w hw
    rw [hNv] at hw ⊢
    rw [comm_sd4_eq_s828_sd4] at hw ⊢
    exact s828CommSub_invariant_sd4 Pv ⊤ (fun _ _ _ _ => Subgroup.mem_top _) p hp w hw
  have hsub : CFSG.Quasithin.H13.s828CommSub Pv Nv ≤ Nv := by
    rw [hNv, comm_sd4_eq_s828_sd4]
    exact s828CommSub_mono_sd4 Pv (le_top)
  have hCle : CFSG.Quasithin.H13.s828CommSub Pv Nv ⊔ Uv ≤ Nv := sup_le hsub hUN
  have hinvC : ∀ p ∈ Pv, ∀ c ∈ CFSG.Quasithin.H13.s828CommSub Pv Nv ⊔ Uv,
      p c ∈ CFSG.Quasithin.H13.s828CommSub Pv Nv ⊔ Uv := by
    intro p hp c hc
    rw [Subgroup.mem_sup] at hc ⊢
    obtain ⟨y, hy, z, hz, rfl⟩ := hc
    refine ⟨p y, s828CommSub_invariant_sd4 Pv Nv hNinv p hp y hy, p z, hUinv p hp z hz, ?_⟩
    rw [map_mul]
  rcases hirr _ le_sup_right hCle hinvC with hC | hC
  · exfalso
    obtain ⟨p, hp, q, hq, n, hn, hne⟩ := hnab
    apply hne
    have hy : (⁅p, q⁆ : MulAut V)⁻¹ ∈ Pv := by
      rw [commutatorElement_def]
      exact Pv.inv_mem (Pv.mul_mem (Pv.mul_mem (Pv.mul_mem hp hq) (Pv.inv_mem hp)) (Pv.inv_mem hq))
    have hmem : ((⁅p, q⁆ : MulAut V)⁻¹ n) * n⁻¹ ∈ CFSG.Quasithin.H13.s828CommSub Pv Nv :=
      Subgroup.subset_closure ⟨_, hy, n, hn, rfl⟩
    have : CFSG.Quasithin.H13.s828CommSub Pv Nv ≤ Uv := by
      rw [← hC]
      exact le_sup_left
    exact this hmem
  · exact hC

end Module

end Dict

end CFSG.Quasithin.H13.L829N
