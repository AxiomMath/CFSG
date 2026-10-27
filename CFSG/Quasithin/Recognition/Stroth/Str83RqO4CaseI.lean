module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4CaseIa

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzSylow
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4ThirdSylow
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Series
import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Tools
import CFSG.GroupTheory.CommutatorCentralizerIn
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeSeries
import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.GroupTheory.PGroup.FixedCommutatorNormalizer

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits
open CFSG.GroupTheory.CoprimeActionSupport
  (commutator_mem_of_coprime_of_le_sup commutator_mem_of_coprime_of_commutator_mem)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_map_conj_iff {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem mem_iff_mem_conj_inv {H : Subgroup G} {g y : G}
    (hg : g⁻¹ ∈ normalizer (H : Set G)) : y ∈ H ↔ g⁻¹ * y * g ∈ H := by
  simpa using (Subgroup.mem_normalizer_iff.mp hg y)

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem caseI_thirdSylow_exists
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hLW : t.L0 ≤ normalizer (t.W : Set G)) :
    ∃ u h : G, ∃ T T' : Subgroup G,
      T = S ⊓ L2 ∧ T' = T.map (MulAut.conj t.x₂).toMonoidHom ∧
      IsSylowTwoOf T L2 ∧ IsSylowTwoOf T' L2 ∧
      u ∈ L2 ∧ u ∈ normalizer (t.Qv 0 : Set G) ∧
      u ∈ normalizer (t.Qv 1 : Set G) ∧ u ∈ normalizer (t.W : Set G) ∧
      h ∈ normalizer (t.Qv 2 : Set G) ∧ h ∈ normalizer (t.W : Set G) ∧
      h ∈ T' ∧
      T'.map (MulAut.conj u).toMonoidHom = T.map (MulAut.conj h).toMonoidHom := by
  classical
  set T : Subgroup G := S ⊓ L2 with hTdef
  set T' : Subgroup G := T.map (MulAut.conj t.x₂).toMonoidHom with hT'def
  have hTsyl : IsSylowTwoOf T L2 := by rw [hTdef]; exact hfr.hF.1.h2.sylow
  have hT'syl : IsSylowTwoOf T' L2 := by
    rw [hT'def, hTdef]; exact t.isSylowTwoOf_map_x₂ hfr
  have hTne : T ≠ T' := by
    rw [hTdef, hT'def]; exact t.inf_L2_ne_map_x₂ hfr
  obtain ⟨u, huT, h, hhT', heq⟩ :=
    exists_conj_eq_conj_of_l2 (one_le_two.trans hfr.hf) hfr.hL2 hTsyl hT'syl hTne
  have huT' : u ∈ S ⊓ L2 := by rwa [hTdef] at huT
  have huL2 : u ∈ L2 := huT'.2
  have huL0 : u ∈ t.L0 := t.L2_le_L0 hfr huL2
  have hSbig : S ≤ bigB L1 L2 S := le_sup_right
  have hbigP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hbigP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hSP1 : S ≤ P1 L1 L2 S := hSbig.trans hbigP1
  have hSP2 : S ≤ P2 L1 L2 S := hSbig.trans hbigP2
  have hSNQv0 : S ≤ normalizer (t.Qv 0 : Set G) := by
    rw [t.Qv_zero]
    exact hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hSNQv1 : S ≤ normalizer (t.Qv 1 : Set G) := by
    rw [t.Qv_one]
    exact hSP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have huNQv0 : u ∈ normalizer (t.Qv 0 : Set G) := hSNQv0 huT'.1
  have huNQv1 : u ∈ normalizer (t.Qv 1 : Set G) := hSNQv1 huT'.1
  have huNW : u ∈ normalizer (t.W : Set G) := hLW huL0
  have huTmap : h ∈ T.map (MulAut.conj t.x₂).toMonoidHom := by rwa [hT'def] at hhT'
  obtain ⟨s, hsT, hs_eq⟩ := Subgroup.mem_map.mp huTmap
  have hsT' : s ∈ S ⊓ L2 := by rwa [hTdef] at hsT
  have hhSm : h ∈ t.Sm :=
    hs_eq ▸ Subgroup.mem_map_of_mem (MulAut.conj t.x₂).toMonoidHom hsT'.1
  have hhL0 : h ∈ t.L0 := (le_sup_right : t.Sm ≤ t.L0) hhSm
  have hhGv2 : h ∈ t.Gv 2 := by
    have hSP1' : S ≤ t.Gv 0 := by rw [t.Gv_zero]; exact hSP1
    have h1 : h ∈ (t.Gv 0).map (MulAut.conj t.x₂).toMonoidHom :=
      Subgroup.map_mono hSP1' hhSm
    rwa [t.map_Gv_x₂ 0] at h1
  have hhNQv2 : h ∈ normalizer (t.Qv 2 : Set G) := t.Gv_le_normalizer_Qv 2 hhGv2
  have hhNW : h ∈ normalizer (t.W : Set G) := hLW hhL0
  exact ⟨u, h, T, T', hTdef, hT'def, hTsyl, hT'syl, huL2, huNQv0, huNQv1, huNW,
    hhNQv2, hhNW, hhT', heq⟩

private theorem caseI_thirdSylow_bigB
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {u h : G} {T T' : Subgroup G} (hTdef : T = S ⊓ L2)
    (hT'def : T' = T.map (MulAut.conj t.x₂).toMonoidHom)
    (hT'syl : IsSylowTwoOf T' L2) (huL2 : u ∈ L2) (hhT' : h ∈ T')
    (heq : T'.map (MulAut.conj u).toMonoidHom = T.map (MulAut.conj h).toMonoidHom) :
    (h⁻¹ * u * t.x₂ ∈ bigB L1 L2 S) ∧
      (h⁻¹ * u * t.x₂ ∈ normalizer (t.Qv 0 : Set G)) := by
  classical
  set k : G := h⁻¹ * u * t.x₂ with hkdef
  have hhL2 : h ∈ L2 := hT'syl.1 hhT'
  have huP2 : u ∈ P2 L1 L2 S := (le_sup_left : L2 ≤ P2 L1 L2 S) huL2
  have hhP2 : h ∈ P2 L1 L2 S := (le_sup_left : L2 ≤ P2 L1 L2 S) hhL2
  have hx₂P2 : t.x₂ ∈ P2 L1 L2 S := by
    have h := t.x₂_mem_Gv_one
    rwa [t.Gv_one] at h
  have hkP2 : k ∈ P2 L1 L2 S :=
    (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hhP2) huP2) hx₂P2
  have hcomp : ∀ (A : Subgroup G) (a b : G),
      (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        A.map (MulAut.conj (b * a)).toMonoidHom := by
    intro A a b
    ext y
    rw [mem_map_conj_iff, mem_map_conj_iff, mem_map_conj_iff,
      show a⁻¹ * (b⁻¹ * y * b) * a = (b * a)⁻¹ * y * (b * a) by group]
  have hTmap_u : T.map (MulAut.conj (u * t.x₂)).toMonoidHom =
      T.map (MulAut.conj h).toMonoidHom := by
    rw [← hcomp T t.x₂ u, ← hT'def, heq]
  have hkT : k ∈ normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hk_eq : k = h⁻¹ * (u * t.x₂) := by rw [hkdef]; group
    calc
      T.map (MulAut.conj k).toMonoidHom
          = T.map (MulAut.conj (h⁻¹ * (u * t.x₂))).toMonoidHom := by rw [hk_eq]
      _ = (T.map (MulAut.conj (u * t.x₂)).toMonoidHom).map
            (MulAut.conj h⁻¹).toMonoidHom := (hcomp T (u * t.x₂) h⁻¹).symm
      _ = (T.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom := by
            rw [hTmap_u]
      _ = T.map (MulAut.conj (h⁻¹ * h)).toMonoidHom := hcomp T h h⁻¹
      _ = T := by
            rw [show h⁻¹ * h = 1 by group,
              show MulAut.conj (1 : G) = 1 from map_one MulAut.conj]
            exact Subgroup.map_id T
  have hkbigB : k ∈ bigB L1 L2 S :=
    normalizer_inf_le_bigB hfr ⟨hkP2, hTdef ▸ hkT⟩
  have hkQv0 : k ∈ normalizer (t.Qv 0 : Set G) := by
    rw [t.Qv_zero]
    exact ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))) hkbigB
  exact ⟨hkbigB, hkQv0⟩

private theorem caseI_thirdSylow_Qd_eq {L1 L2 S : Subgroup G} (t : Track L1 L2 S)
    {u h : G} (hkQv0 : h⁻¹ * u * t.x₂ ∈ normalizer (t.Qv 0 : Set G)) :
    (t.Qv 2).map (MulAut.conj u).toMonoidHom =
      (t.Qv 0).map (MulAut.conj h).toMonoidHom := by
  have hmapQv : (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 2 := by
    simpa using t.map_Qv_x₂ 0
  have hk' : (h⁻¹ * u * t.x₂)⁻¹ ∈ normalizer (t.Qv 0 : Set G) :=
    (normalizer (t.Qv 0 : Set G)).inv_mem hkQv0
  ext y
  constructor
  · intro hyd
    have h1 : u⁻¹ * y * u ∈ t.Qv 2 := mem_map_conj_iff.mp hyd
    rw [← hmapQv] at h1
    have h2 : t.x₂⁻¹ * (u⁻¹ * y * u) * t.x₂ ∈ t.Qv 0 := mem_map_conj_iff.mp h1
    have hid : t.x₂⁻¹ * (u⁻¹ * y * u) * t.x₂ =
        (h⁻¹ * u * t.x₂)⁻¹ * (h⁻¹ * y * h) * (h⁻¹ * u * t.x₂) := by group
    rw [hid] at h2
    have h3 : h⁻¹ * y * h ∈ t.Qv 0 :=
      (mem_iff_mem_conj_inv hk' (y := h⁻¹ * y * h)).mpr h2
    exact mem_map_conj_iff.mpr h3
  · intro hy
    have h1 : h⁻¹ * y * h ∈ t.Qv 0 := mem_map_conj_iff.mp hy
    have h2 : (h⁻¹ * u * t.x₂)⁻¹ * (h⁻¹ * y * h) * (h⁻¹ * u * t.x₂) ∈ t.Qv 0 :=
      (mem_iff_mem_conj_inv hk' (y := h⁻¹ * y * h)).mp h1
    have hid : t.x₂⁻¹ * (u⁻¹ * y * u) * t.x₂ =
        (h⁻¹ * u * t.x₂)⁻¹ * (h⁻¹ * y * h) * (h⁻¹ * u * t.x₂) := by group
    rw [← hid] at h2
    have h3 : u⁻¹ * y * u ∈ (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom :=
      mem_map_conj_iff.mpr h2
    rw [hmapQv] at h3
    exact mem_map_conj_iff.mpr h3

private theorem caseI_thirdSylow_inf {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {u h : G}
    (huNQv0 : u ∈ normalizer (t.Qv 0 : Set G))
    (huNW : u ∈ normalizer (t.W : Set G))
    (hhNQv2 : h ∈ normalizer (t.Qv 2 : Set G))
    (hhNW : h ∈ normalizer (t.W : Set G)) :
    (t.Qv 0 ⊓ (t.Qv 2).map (MulAut.conj u).toMonoidHom = t.W) ∧
      (t.Qv 2 ⊓ (t.Qv 0).map (MulAut.conj h).toMonoidHom = t.W) := by
  constructor
  · refine le_antisymm ?_ ?_
    · rintro y ⟨hy0, hyd⟩
      have hyd' : y ∈ (t.Qv 2).map (MulAut.conj u).toMonoidHom := hyd
      have hyd'' : u⁻¹ * y * u ∈ t.Qv 2 := mem_map_conj_iff.mp hyd'
      have hz0 : u⁻¹ * y * u ∈ t.Qv 0 :=
        (mem_iff_mem_conj_inv ((normalizer (t.Qv 0 : Set G)).inv_mem huNQv0)).mp hy0
      have hzW : u⁻¹ * y * u ∈ t.W := ⟨hz0, hyd''⟩
      have hy : y = u * (u⁻¹ * y * u) * u⁻¹ := by group
      rw [hy]
      exact (Subgroup.mem_normalizer_iff.mp huNW _).mp hzW
    · intro y hy
      refine ⟨hy.1, ?_⟩
      have hzu : u⁻¹ * y * u ∈ t.W :=
        (mem_iff_mem_conj_inv ((normalizer (t.W : Set G)).inv_mem huNW)).mp hy
      exact mem_map_conj_iff.mpr hzu.2
  · refine le_antisymm ?_ ?_
    · rintro y ⟨hy2, hyd⟩
      have hyd' : h⁻¹ * y * h ∈ t.Qv 0 := mem_map_conj_iff.mp hyd
      have hz2 : h⁻¹ * y * h ∈ t.Qv 2 :=
        (mem_iff_mem_conj_inv ((normalizer (t.Qv 2 : Set G)).inv_mem hhNQv2)).mp hy2
      have hzW : h⁻¹ * y * h ∈ t.W := ⟨hyd', hz2⟩
      have hy : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
      rw [hy]
      exact (Subgroup.mem_normalizer_iff.mp hhNW _).mp hzW
    · intro y hy
      refine ⟨hy.2, ?_⟩
      have hzh : h⁻¹ * y * h ∈ t.W :=
        (mem_iff_mem_conj_inv ((normalizer (t.W : Set G)).inv_mem hhNW)).mp hy
      exact mem_map_conj_iff.mpr hzh.1

private theorem caseI_thirdSylow_Aδ {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {u : G}
    (huNQv1 : u ∈ normalizer (t.Qv 1 : Set G))
    (hQv1NQv2 : t.Qv 1 ≤ normalizer (t.Qv 2 : Set G)) :
    (t.Qv 1 ⊓ (t.Qv 2).map (MulAut.conj u).toMonoidHom =
      (t.Am).map (MulAut.conj u).toMonoidHom) ∧
    (t.Qv 1 ≤ normalizer ((t.Qv 2).map (MulAut.conj u).toMonoidHom : Set G)) := by
  constructor
  · refine le_antisymm ?_ ?_
    · rintro y ⟨hy1, hy2⟩
      have hy2' : y ∈ (t.Qv 2).map (MulAut.conj u).toMonoidHom := hy2
      have hy2'' : u⁻¹ * y * u ∈ t.Qv 2 := mem_map_conj_iff.mp hy2'
      refine mem_map_conj_iff.mpr ⟨?_, hy2''⟩
      exact (mem_iff_mem_conj_inv ((normalizer (t.Qv 1 : Set G)).inv_mem huNQv1)).mp hy1
    · intro y hy
      have hy' : u⁻¹ * y * u ∈ t.Am := mem_map_conj_iff.mp hy
      refine ⟨?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.mp huNQv1 (u⁻¹ * y * u)).mp hy'.1
        rwa [show u * (u⁻¹ * y * u) * u⁻¹ = y by group] at h
      · exact mem_map_conj_iff.mpr hy'.2
  · intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext y
    constructor
    · intro hy
      have h1 : q⁻¹ * y * q ∈ (t.Qv 2).map (MulAut.conj u).toMonoidHom :=
        mem_map_conj_iff.mp hy
      have h2 : u⁻¹ * (q⁻¹ * y * q) * u ∈ t.Qv 2 := mem_map_conj_iff.mp h1
      have hqu : u⁻¹ * q * u ∈ t.Qv 1 :=
        (mem_iff_mem_conj_inv ((normalizer (t.Qv 1 : Set G)).inv_mem huNQv1)).mp hq
      have hN2 : (u⁻¹ * q * u)⁻¹ ∈ normalizer (t.Qv 2 : Set G) :=
        (normalizer (t.Qv 2 : Set G)).inv_mem (hQv1NQv2 hqu)
      have hid : u⁻¹ * (q⁻¹ * y * q) * u =
          (u⁻¹ * q * u)⁻¹ * (u⁻¹ * y * u) * (u⁻¹ * q * u) := by group
      rw [hid] at h2
      have h3 : u⁻¹ * y * u ∈ t.Qv 2 :=
        (mem_iff_mem_conj_inv hN2 (y := u⁻¹ * y * u)).mpr h2
      exact mem_map_conj_iff.mpr h3
    · intro hy
      have h3 : u⁻¹ * y * u ∈ t.Qv 2 := mem_map_conj_iff.mp hy
      have hqu : u⁻¹ * q * u ∈ t.Qv 1 :=
        (mem_iff_mem_conj_inv ((normalizer (t.Qv 1 : Set G)).inv_mem huNQv1)).mp hq
      have hN2 : (u⁻¹ * q * u)⁻¹ ∈ normalizer (t.Qv 2 : Set G) :=
        (normalizer (t.Qv 2 : Set G)).inv_mem (hQv1NQv2 hqu)
      have hmid : u⁻¹ * (q⁻¹ * y * q) * u ∈ t.Qv 2 := by
        rw [show u⁻¹ * (q⁻¹ * y * q) * u =
          (u⁻¹ * q * u)⁻¹ * (u⁻¹ * y * u) * (u⁻¹ * q * u) by group]
        exact (mem_iff_mem_conj_inv hN2 (y := u⁻¹ * y * u)).mp h3
      exact mem_map_conj_iff.mpr (mem_map_conj_iff.mpr hmid)

private theorem caseI_thirdSylow_Qv1_sup
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hS : S ≤ t.Am ⊔ t.Qv 0) : t.Qv 1 ≤ t.Ap ⊔ t.Am := by
  have hQv1S : t.Qv 1 ≤ S := by rw [t.Qv_one]; exact Q2_le_S hfr.hF
  have hQv1NQv0 : t.Qv 1 ≤ normalizer (t.Qv 0 : Set G) :=
    (t.Qv_one_le_normalizer_Qv hfr).1
  have hAmNQv0 : t.Am ≤ normalizer (t.Qv 0 : Set G) :=
    (inf_le_left : t.Am ≤ t.Qv 1).trans hQv1NQv0
  intro y hy
  have h : y ∈ (t.Am ⊔ t.Qv 0) ⊓ t.Qv 1 := Subgroup.mem_inf.mpr ⟨hS (hQv1S hy), hy⟩
  rw [sup_inf_eq_sup_inf_of_le_normalizer (inf_le_left : t.Am ≤ t.Qv 1) hAmNQv0,
    inf_comm (t.Qv 0) (t.Qv 1), sup_comm t.Am t.Ap] at h
  exact h

private theorem caseI_thirdSylow_commutators_Ap {L1 L2 S : Subgroup G}
    (t : Track L1 L2 S) {Qd : Subgroup G} (hQd_inf_Qv0 : t.Qv 0 ⊓ Qd = t.W)
    (hQd_normal : t.Qv 1 ≤ normalizer (Qd : Set G))
    (hQv1NQv0 : t.Qv 1 ≤ normalizer (t.Qv 0 : Set G)) :
    ∀ a ∈ t.Qv 1 ⊓ Qd, ∀ x ∈ t.Ap, ⁅a, x⁆ ∈ t.W := by
  intro a ha x hx
  have haQv1 : a ∈ t.Qv 1 := ha.1
  have haQd : a ∈ Qd := ha.2
  have hxQv1 : x ∈ t.Qv 1 := hx.1
  have hxQv0 : x ∈ t.Qv 0 := hx.2
  have h1 : a * x * a⁻¹ ∈ t.Qv 0 :=
    (Subgroup.le_normalizer_iff.mp hQv1NQv0 a haQv1) x hxQv0
  have hmem0 : ⁅a, x⁆ ∈ t.Qv 0 := by
    have hid : ⁅a, x⁆ = (a * x * a⁻¹) * x⁻¹ := by
      simp [commutatorElement_def]
    rw [hid]
    exact (t.Qv 0).mul_mem h1 ((t.Qv 0).inv_mem hxQv0)
  have hxnorm : x * a * x⁻¹ ∈ t.Qv 1 ⊓ Qd :=
    ⟨(t.Qv 1).mul_mem ((t.Qv 1).mul_mem hxQv1 haQv1) ((t.Qv 1).inv_mem hxQv1),
      (Subgroup.mem_normalizer_iff.mp (hQd_normal hxQv1) a).mp haQd⟩
  have hmemA : ⁅x, a⁆ ∈ t.Qv 1 ⊓ Qd :=
    (t.Qv 1 ⊓ Qd).mul_mem hxnorm ((t.Qv 1 ⊓ Qd).inv_mem ha)
  have hmemQd : ⁅a, x⁆ ∈ Qd := by
    have h := (t.Qv 1 ⊓ Qd).inv_mem hmemA
    rw [commutatorElement_inv] at h
    exact h.2
  rw [← hQd_inf_Qv0]
  exact ⟨hmem0, hmemQd⟩

private theorem caseI_thirdSylow_commutators_Am {L1 L2 S : Subgroup G}
    (t : Track L1 L2 S) {h : G} {Qd : Subgroup G}
    (hQd_inf_Qv2 : t.Qv 2 ⊓ (t.Qv 0).map (MulAut.conj h).toMonoidHom = t.W)
    (hQd_eq : Qd = (t.Qv 0).map (MulAut.conj h).toMonoidHom)
    (hQd_normal : t.Qv 1 ≤ normalizer (Qd : Set G))
    (hQv1NQv2 : t.Qv 1 ≤ normalizer (t.Qv 2 : Set G)) :
    ∀ a ∈ t.Qv 1 ⊓ Qd, ∀ x ∈ t.Am, ⁅a, x⁆ ∈ t.W := by
  intro a ha x hx
  have haQv1 : a ∈ t.Qv 1 := ha.1
  have haQd : a ∈ Qd := ha.2
  have hxQv1 : x ∈ t.Qv 1 := hx.1
  have hxQv2 : x ∈ t.Qv 2 := hx.2
  have h1 : a * x * a⁻¹ ∈ t.Qv 2 :=
    (Subgroup.le_normalizer_iff.mp hQv1NQv2 a haQv1) x hxQv2
  have hmem2 : ⁅a, x⁆ ∈ t.Qv 2 := by
    have hid : ⁅a, x⁆ = (a * x * a⁻¹) * x⁻¹ := by
      simp [commutatorElement_def]
    rw [hid]
    exact (t.Qv 2).mul_mem h1 ((t.Qv 2).inv_mem hxQv2)
  have hxnorm : x * a * x⁻¹ ∈ t.Qv 1 ⊓ Qd :=
    ⟨(t.Qv 1).mul_mem ((t.Qv 1).mul_mem hxQv1 haQv1) ((t.Qv 1).inv_mem hxQv1),
      (Subgroup.mem_normalizer_iff.mp (hQd_normal hxQv1) a).mp haQd⟩
  have hmemA : ⁅x, a⁆ ∈ t.Qv 1 ⊓ Qd :=
    (t.Qv 1 ⊓ Qd).mul_mem hxnorm ((t.Qv 1 ⊓ Qd).inv_mem ha)
  have hmemQd : ⁅a, x⁆ ∈ (t.Qv 0).map (MulAut.conj h).toMonoidHom := by
    have h := ((t.Qv 1 ⊓ Qd).inv_mem hmemA).2
    rw [commutatorElement_inv] at h
    rwa [hQd_eq] at h
  rw [← hQd_inf_Qv2]
  exact ⟨hmem2, hmemQd⟩

private theorem caseI_thirdSylow_centralizes {L1 L2 S : Subgroup G} (t : Track L1 L2 S)
    {Qd : Subgroup G} (hQv1_sup : t.Qv 1 ≤ t.Ap ⊔ t.Am)
    (hQv1NW : t.Qv 1 ≤ normalizer (t.W : Set G))
    (hApNAm : t.Ap ≤ normalizer (t.Am : Set G))
    (hAδApW : ∀ a ∈ t.Qv 1 ⊓ Qd, ∀ x ∈ t.Ap, ⁅a, x⁆ ∈ t.W)
    (hAδAmW : ∀ a ∈ t.Qv 1 ⊓ Qd, ∀ x ∈ t.Am, ⁅a, x⁆ ∈ t.W) :
    ∀ a ∈ t.Qv 1 ⊓ Qd, ∀ x ∈ t.Qv 1, ⁅a, x⁆ ∈ t.W := by
  intro a ha x hx
  obtain ⟨b, hbAp, c, hcAm, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hApNAm).mp (hQv1_sup hx)
  have hbQv1 : b ∈ t.Qv 1 := hbAp.1
  have hbNW : b ∈ normalizer (t.W : Set G) := hQv1NW hbQv1
  have h1 : ⁅a, b⁆ ∈ t.W := hAδApW a ha b hbAp
  have h2 : ⁅a, c⁆ ∈ t.W := hAδAmW a ha c hcAm
  have hid : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    simp only [mul_assoc]
  rw [hid]
  exact (t.W).mul_mem h1 ((Subgroup.mem_normalizer_iff.mp hbNW _).mp h2)

private theorem caseI_thirdSylow_normal {L1 L2 S : Subgroup G} (t : Track L1 L2 S) :
    ⁅t.Qv 0, S⁆ ≤ t.Qv 0 ∧ ⁅S, t.Qv 0⁆ ≤ t.Qv 0 := by
  have hSNQv0 : S ≤ normalizer (t.Qv 0 : Set G) := by
    rw [t.Qv_zero]
    exact ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  constructor
  · rw [Subgroup.commutator_le]
    intro n hn s hs
    have h1 : s * n⁻¹ * s⁻¹ ∈ t.Qv 0 :=
      (Subgroup.le_normalizer_iff.mp hSNQv0 s hs) n⁻¹ ((t.Qv 0).inv_mem hn)
    have hid : ⁅n, s⁆ = n * (s * n⁻¹ * s⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hid]
    exact (t.Qv 0).mul_mem hn h1
  · rw [Subgroup.commutator_le]
    intro s hs n hn
    have h1 : s * n * s⁻¹ ∈ t.Qv 0 :=
      (Subgroup.le_normalizer_iff.mp hSNQv0 s hs) n hn
    have hid : ⁅s, n⁆ = (s * n * s⁻¹) * n⁻¹ := rfl
    rw [hid]
    exact (t.Qv 0).mul_mem h1 ((t.Qv 0).inv_mem hn)

private theorem caseI_thirdSylow_bPrime
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hS : S ≤ t.Am ⊔ t.Qv 0)
    (hNS : ⁅t.Qv 0, S⁆ ≤ t.Qv 0) (hSN : ⁅S, t.Qv 0⁆ ≤ t.Qv 0) :
    ∃ b₁ b₂ : G, b₁ ∈ t.Am ∧ b₂ ∈ t.Am ∧ ⁅b₁, b₂⁆ ∉ t.Qv 0 := by
  have hQv1S : t.Qv 1 ≤ S := by rw [t.Qv_one]; exact Q2_le_S hfr.hF
  have hQv0S : t.Qv 0 ≤ S := by rw [t.Qv_zero]; exact Q1_le_S hfr.hF
  have hSNQv0 : S ≤ normalizer (t.Qv 0 : Set G) := by
    rw [t.Qv_zero]
    exact ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hAmNQv0 : t.Am ≤ normalizer (t.Qv 0 : Set G) :=
    (inf_le_left : t.Am ≤ t.Qv 1).trans ((t.Qv_one_le_normalizer_Qv hfr).1)
  obtain ⟨s₁, hs₁S, s₂, hs₂S, hnot0⟩ := exists_commutator_not_mem_Q1 hfr
  have hnot : ⁅s₁, s₂⁆ ∉ t.Qv 0 := by
    rw [t.Qv_zero]
    exact hnot0
  obtain ⟨b₁, hb₁Am, q₁, hq₁Qv0, hs₁_eq⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hAmNQv0).mp (hS hs₁S)
  obtain ⟨b₂, hb₂Am, q₂, hq₂Qv0, hs₂_eq⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hAmNQv0).mp (hS hs₂S)
  have hb₁Qv1 : b₁ ∈ t.Qv 1 := hb₁Am.1
  have hb₂Qv1 : b₂ ∈ t.Qv 1 := hb₂Am.1
  have hb₁S : b₁ ∈ S := hQv1S hb₁Qv1
  have hb₂S : b₂ ∈ S := hQv1S hb₂Qv1
  have hq₁S : q₁ ∈ S := hQv0S hq₁Qv0
  have hq₂S : q₂ ∈ S := hQv0S hq₂Qv0
  have hb₁q₁S : b₁ * q₁ ∈ S := S.mul_mem hb₁S hq₁S
  have hq₁b₂ : ⁅q₁, b₂⁆ ∈ t.Qv 0 :=
    hNS (Subgroup.commutator_mem_commutator hq₁Qv0 hb₂S)
  have hb₁q₁q₂ : ⁅b₁ * q₁, q₂⁆ ∈ t.Qv 0 :=
    hSN (Subgroup.commutator_mem_commutator hb₁q₁S hq₂Qv0)
  have hA : b₁ * ⁅q₁, b₂⁆ * b₁⁻¹ ∈ t.Qv 0 :=
    (Subgroup.mem_normalizer_iff.mp (hSNQv0 hb₁S) _).mp hq₁b₂
  have hB : b₂ * ⁅b₁ * q₁, q₂⁆ * b₂⁻¹ ∈ t.Qv 0 :=
    (Subgroup.mem_normalizer_iff.mp (hSNQv0 hb₂S) _).mp hb₁q₁q₂
  have hnotmem : ⁅b₁, b₂⁆ ∉ t.Qv 0 := by
    intro hmem
    have hid : ⁅b₁ * q₁, b₂ * q₂⁆ =
        (b₁ * ⁅q₁, b₂⁆ * b₁⁻¹) * ⁅b₁, b₂⁆ * (b₂ * ⁅b₁ * q₁, q₂⁆ * b₂⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_mul_left_eq_conj_mul]
      group
    have hprod : ⁅b₁ * q₁, b₂ * q₂⁆ ∈ t.Qv 0 := by
      rw [hid]
      exact (t.Qv 0).mul_mem ((t.Qv 0).mul_mem hA hmem) hB
    rw [← hs₁_eq, ← hs₂_eq] at hprod
    exact hnot hprod
  exact ⟨b₁, b₂, hb₁Am, hb₂Am, hnotmem⟩

private theorem caseI_thirdSylow_final {L1 L2 S : Subgroup G} (t : Track L1 L2 S)
    {u : G} {Qd : Subgroup G} (hQddef : Qd = (t.Qv 2).map (MulAut.conj u).toMonoidHom)
    (huNQv1 : u ∈ normalizer (t.Qv 1 : Set G))
    (huNW : u ∈ normalizer (t.W : Set G))
    (hcent : ∀ a ∈ t.Qv 1 ⊓ Qd, ∀ x ∈ t.Qv 1, ⁅a, x⁆ ∈ t.W)
    {b₁ b₂ : G} (hb₁Am : b₁ ∈ t.Am) (hb₂Am : b₂ ∈ t.Am)
    (hnotmem : ⁅b₁, b₂⁆ ∉ t.Qv 0) : False := by
  have hb₁u : u * b₁ * u⁻¹ ∈ t.Qv 1 ⊓ Qd := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp huNQv1 b₁).mp hb₁Am.1, ?_⟩
    rw [hQddef]
    change u * b₁ * u⁻¹ ∈ (t.Qv 2).map (MulAut.conj u).toMonoidHom
    rw [mem_map_conj_iff]
    rw [show u⁻¹ * (u * b₁ * u⁻¹) * u = b₁ by group]
    exact hb₁Am.2
  have hb₂u : u * b₂ * u⁻¹ ∈ t.Qv 1 ⊓ Qd := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp huNQv1 b₂).mp hb₂Am.1, ?_⟩
    rw [hQddef]
    change u * b₂ * u⁻¹ ∈ (t.Qv 2).map (MulAut.conj u).toMonoidHom
    rw [mem_map_conj_iff]
    rw [show u⁻¹ * (u * b₂ * u⁻¹) * u = b₂ by group]
    exact hb₂Am.2
  have hmemW : ⁅b₁, b₂⁆ ∈ t.W := by
    have h := hcent (u * b₁ * u⁻¹) hb₁u (u * b₂ * u⁻¹) hb₂u.1
    rw [← conjugate_commutatorElement] at h
    exact (Subgroup.mem_normalizer_iff.mp huNW _).mpr h
  exact hnotmem ((show t.W ≤ t.Qv 0 from inf_le_left) hmemW)

theorem caseI_not_le_Am_sup {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hLW : t.L0 ≤ normalizer (t.W : Set G))
    (hS : S ≤ t.Am ⊔ t.Qv 0) : False := by
  classical
  obtain ⟨u, h, T, T', hTdef, hT'def, hTsyl, hT'syl, huL2, huNQv0, huNQv1, huNW,
    hhNQv2, hhNW, hhT', heq⟩ := caseI_thirdSylow_exists t hfr hLW
  have hk := caseI_thirdSylow_bigB t hfr hTdef hT'def hT'syl huL2 hhT' heq
  have hkQv0 : h⁻¹ * u * t.x₂ ∈ normalizer (t.Qv 0 : Set G) := hk.2
  have hQd_eq : (t.Qv 2).map (MulAut.conj u).toMonoidHom =
      (t.Qv 0).map (MulAut.conj h).toMonoidHom := caseI_thirdSylow_Qd_eq t hkQv0
  have hQd_inf := caseI_thirdSylow_inf t huNQv0 huNW hhNQv2 hhNW
  have hQv1NQv2 : t.Qv 1 ≤ normalizer (t.Qv 2 : Set G) :=
    (t.Qv_one_le_normalizer_Qv hfr).2
  have hAδ := caseI_thirdSylow_Aδ t huNQv1 hQv1NQv2
  have hQv1_sup := caseI_thirdSylow_Qv1_sup t hfr hS
  have hQv1NQv0 : t.Qv 1 ≤ normalizer (t.Qv 0 : Set G) :=
    (t.Qv_one_le_normalizer_Qv hfr).1
  have hQv1NW : t.Qv 1 ≤ normalizer (t.W : Set G) :=
    ((t.Qv_le_Sm hfr).1.trans le_sup_right).trans hLW
  have hApNAm : t.Ap ≤ normalizer (t.Am : Set G) :=
    (inf_le_left : t.Ap ≤ t.Qv 1).trans
      ((le_inf le_normalizer hQv1NQv2).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hApW := caseI_thirdSylow_commutators_Ap t hQd_inf.1 hAδ.2 hQv1NQv0
  have hAmW := caseI_thirdSylow_commutators_Am t hQd_inf.2 hQd_eq hAδ.2 hQv1NQv2
  have hcent := caseI_thirdSylow_centralizes t hQv1_sup hQv1NW hApNAm hApW hAmW
  have hnormal := caseI_thirdSylow_normal t
  obtain ⟨b₁, b₂, hb₁, hb₂, hnot⟩ := caseI_thirdSylow_bPrime t hfr hS hnormal.1 hnormal.2
  exact caseI_thirdSylow_final t (Qd := (t.Qv 2).map (MulAut.conj u).toMonoidHom) rfl
    huNQv1 huNW hcent hb₁ hb₂ hnot

private theorem caseI_S_le_normalizer_Qv_zero {L1 L2 S : Subgroup G}
    (t : Track L1 L2 S) : S ≤ normalizer (t.Qv 0 : Set G) := by
  rw [t.Qv_zero]
  exact ((le_sup_right : S ≤ bigB L1 L2 S).trans
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))

private theorem caseI_S_le_normalizer_Qv_one {L1 L2 S : Subgroup G}
    (t : Track L1 L2 S) : S ≤ normalizer (t.Qv 1 : Set G) := by
  rw [t.Qv_one]
  exact ((le_sup_right : S ≤ bigB L1 L2 S).trans
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))

private theorem caseI_Sm_le_normalizer_Qv_one {L1 L2 S : Subgroup G}
    (t : Track L1 L2 S) : t.Sm ≤ normalizer (t.Qv 1 : Set G) := by
  have hSmP2 : t.Sm ≤ P2 L1 L2 S := by
    have h := t.L0_le_Gv_one
    rw [t.Gv_one] at h
    exact (le_sup_right : t.Sm ≤ t.L0).trans h
  rw [t.Qv_one]
  exact hSmP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))

private theorem caseI_Zv_neg_one_le_normalizer_Qv_one
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZQ : t.Zv (-1) ≤ t.Qv 0) : t.Zv (-1) ≤ normalizer (t.Qv 1 : Set G) := by
  have hQv0S : t.Qv 0 ≤ S := by rw [t.Qv_zero]; exact Q1_le_S hfr.hF
  exact hZQ.trans (hQv0S.trans (caseI_S_le_normalizer_Qv_one t))

private theorem caseI_S_le_Qv_one_sup_Qv_zero {L1 L2 S : Subgroup G} {t : Track L1 L2 S}
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1) (hZQ : t.Zv (-1) ≤ t.Qv 0) :
    S ≤ t.Qv 1 ⊔ t.Qv 0 :=
  hS.trans (sup_le (hZQ.trans le_sup_right) le_sup_left)

private theorem caseI_commutator_Qv_zero_Qv_one_le_Ap
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    ⁅t.Qv 0, t.Qv 1⁆ ≤ t.Ap := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hQv0S : t.Qv 0 ≤ S := by rw [t.Qv_zero]; exact Q1_le_S hfr.hF
  have hxa : x * a * x⁻¹ ∈ t.Qv 1 :=
    (Subgroup.mem_normalizer_iff.mp (caseI_S_le_normalizer_Qv_one t (hQv0S hx)) a).mp ha
  have hmem1 : x * a * x⁻¹ * a⁻¹ ∈ t.Qv 1 :=
    (t.Qv 1).mul_mem hxa ((t.Qv 1).inv_mem ha)
  have hax : a * x * a⁻¹ ∈ t.Qv 0 :=
    (Subgroup.mem_normalizer_iff.mp
      ((t.Qv_one_le_normalizer_Qv hfr).1 ha) x).mp hx
  have hmem0 : x * a * x⁻¹ * a⁻¹ ∈ t.Qv 0 := by
    have hid : x * a * x⁻¹ * a⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
    rw [hid]
    exact (t.Qv 0).inv_mem ((t.Qv 0).mul_mem hax ((t.Qv 0).inv_mem hx))
  exact ⟨hmem1, hmem0⟩

private theorem caseI_commutator_Qv_two_Qv_one_le_Am
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    ⁅t.Qv 2, t.Qv 1⁆ ≤ t.Am := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hxSm : x ∈ t.Sm := (t.Qv_le_Sm hfr).2 hx
  have hxa : x * a * x⁻¹ ∈ t.Qv 1 :=
    (Subgroup.mem_normalizer_iff.mp (caseI_Sm_le_normalizer_Qv_one t hxSm) a).mp ha
  have hmem1 : x * a * x⁻¹ * a⁻¹ ∈ t.Qv 1 :=
    (t.Qv 1).mul_mem hxa ((t.Qv 1).inv_mem ha)
  have hax : a * x * a⁻¹ ∈ t.Qv 2 :=
    (Subgroup.mem_normalizer_iff.mp ((t.Qv_one_le_normalizer_Qv hfr).2 ha) x).mp hx
  have hmem2 : x * a * x⁻¹ * a⁻¹ ∈ t.Qv 2 := by
    have hid : x * a * x⁻¹ * a⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
    rw [hid]
    exact (t.Qv 2).inv_mem ((t.Qv 2).mul_mem hax ((t.Qv 2).inv_mem hx))
  exact ⟨hmem1, hmem2⟩

private theorem caseI_commutator_Qv_one_Am_le_Ap
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hsqAm : ∀ a ∈ t.Am, a * a ∈ t.Qv 0) : ⁅t.Qv 1, t.Am⁆ ≤ t.Ap := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have hQv1S : t.Qv 1 ≤ S := by rw [t.Qv_one]; exact Q2_le_S hfr.hF
  have hxS : x ∈ S := hQv1S hx
  have haS : a ∈ S := hQv1S ha.1
  have hR : pCoreOf 2 (t.Gw 0 (0 + 1)) = S := by
    rw [zero_add]
    exact t.pCoreOf_Gw_zero_one hfr
  have haΩ : a ∈ t.rootOmega 0 := by
    rw [t.mem_rootOmega_iff hfr 0, hR, pow_two]
    exact ⟨haS, hsqAm a ha⟩
  have h' : ⁅a, x⁆ ∈ t.Qv 0 := t.commutator_rootOmega_le hfr 0
    (Subgroup.commutator_mem_commutator haΩ (by rw [hR]; exact hxS))
  have h1 : ⁅x, a⁆ ∈ t.Qv 1 :=
    (t.Qv 1).mul_mem ((t.Qv 1).mul_mem ((t.Qv 1).mul_mem hx ha.1) ((t.Qv 1).inv_mem hx))
      ((t.Qv 1).inv_mem ha.1)
  refine ⟨h1, ?_⟩
  rw [show ⁅x, a⁆ = ⁅a, x⁆⁻¹ from (commutatorElement_inv (g₁ := a) (g₂ := x)).symm]
  exact (t.Qv 0).inv_mem h'

private theorem caseI_commutator_Qv_one_Ap_le_Am
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hsqAm : ∀ a ∈ t.Am, a * a ∈ t.Qv 0) : ⁅t.Qv 1, t.Ap⁆ ≤ t.Am := by
  have hA' := caseI_commutator_Qv_one_Am_le_Ap t hfr hsqAm
  have hmapQv1 : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
    simpa using t.map_Qv_x₂ 1
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hA'
  rw [Subgroup.map_commutator, hmapQv1, t.map_Am_x₂, t.map_Ap_x₂] at h
  exact h

private theorem caseI_commutator_Qv_one_Qv_one_le
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hrootAm : ∀ s ∈ S, s * s ∈ t.Qv 0 → s ∈ t.Am ⊔ t.Qv 0) :
    ⁅t.Qv 1, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hQv1S : t.Qv 1 ≤ S := by rw [t.Qv_one]; exact Q2_le_S hfr.hF
  have hxS : x ∈ S := hQv1S hx
  have hyS : y ∈ S := hQv1S hy
  have hxyS : ⁅x, y⁆ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hxS hyS) (S.inv_mem hxS)) (S.inv_mem hyS)
  have hsq : ⁅x, y⁆ * ⁅x, y⁆ ∈ Q1 L1 L2 S :=
    commutator_mul_self_mem_Q1 hfr hxS hyS
  have hsq' : ⁅x, y⁆ * ⁅x, y⁆ ∈ t.Qv 0 := by rwa [← t.Qv_zero] at hsq
  have hroot := hrootAm ⁅x, y⁆ hxyS hsq'
  have hxyQv1 : ⁅x, y⁆ ∈ t.Qv 1 :=
    (t.Qv 1).mul_mem ((t.Qv 1).mul_mem ((t.Qv 1).mul_mem hx hy) ((t.Qv 1).inv_mem hx))
      ((t.Qv 1).inv_mem hy)
  have hAmNQv0 : t.Am ≤ normalizer (t.Qv 0 : Set G) :=
    (inf_le_left : t.Am ≤ t.Qv 1).trans (t.Qv_one_le_normalizer_Qv hfr).1
  have hded : ⁅x, y⁆ ∈ (t.Am ⊔ t.Qv 0) ⊓ t.Qv 1 := Subgroup.mem_inf.mpr ⟨hroot, hxyQv1⟩
  rw [sup_inf_eq_sup_inf_of_le_normalizer (inf_le_left : t.Am ≤ t.Qv 1) hAmNQv0,
    inf_comm (t.Qv 0) (t.Qv 1), sup_comm t.Am t.Ap] at hded
  exact hded

private theorem caseI_Am_le_commutator_sup_Ap
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZQ : t.Zv (-1) ≤ t.Qv 0)
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1)
    (hsqAm : ∀ a ∈ t.Am, a * a ∈ t.Qv 0) :
    t.Am ≤ ⁅t.Qv 1, t.Qv 1⁆ ⊔ t.Ap := by
  have hQv1S : t.Qv 1 ≤ S := by rw [t.Qv_one]; exact Q2_le_S hfr.hF
  have hSQ : S ≤ t.Qv 1 ⊔ t.Qv 0 := caseI_S_le_Qv_one_sup_Qv_zero hS hZQ
  have hcomm : ⁅S, S⁆ ≤ ⁅t.Qv 1, t.Qv 1⁆ ⊔ t.Qv 0 :=
    (Subgroup.commutator_mono hSQ hSQ).trans
      (commutator_sup_le_sup_of_le_normalizer (t.Qv_one_le_normalizer_Qv hfr).1)
  have hXN : ⁅t.Qv 1, t.Qv 1⁆ ≤ normalizer (t.Qv 0 : Set G) :=
    (Subgroup.commutator_le_self _).trans (t.Qv_one_le_normalizer_Qv hfr).1
  intro a ha
  have haS : a ∈ S := hQv1S ha.1
  have hsq : a * a ∈ Q1 L1 L2 S := by
    rw [← t.Qv_zero]
    exact hsqAm a ha
  have h1 : a ∈ ⁅S, S⁆ ⊔ Q1 L1 L2 S := mem_commutator_sup_Q1 hfr haS hsq
  rw [← t.Qv_zero] at h1
  have h2' : a ∈ (⁅t.Qv 1, t.Qv 1⁆ ⊔ t.Qv 0) ⊔ t.Qv 0 :=
    (sup_le_sup hcomm le_rfl) h1
  rw [sup_assoc, sup_idem] at h2'
  have h3 : a ∈ (⁅t.Qv 1, t.Qv 1⁆ ⊔ t.Qv 0) ⊓ t.Qv 1 := Subgroup.mem_inf.mpr ⟨h2', ha.1⟩
  rwa [sup_inf_eq_sup_inf_of_le_normalizer (Subgroup.commutator_le_self _) hXN,
    inf_comm (t.Qv 0) (t.Qv 1)] at h3

private theorem caseI_Ap_le_commutator_sup_Am
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZQ : t.Zv (-1) ≤ t.Qv 0)
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1)
    (hsqAm : ∀ a ∈ t.Am, a * a ∈ t.Qv 0) :
    t.Ap ≤ ⁅t.Qv 1, t.Qv 1⁆ ⊔ t.Am := by
  have hDA := caseI_Am_le_commutator_sup_Ap t hfr hZQ hS hsqAm
  have hmapQv1 : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
    simpa using t.map_Qv_x₂ 1
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hDA
  rw [Subgroup.map_sup, Subgroup.map_commutator, hmapQv1, t.map_Ap_x₂, t.map_Am_x₂] at h
  exact h

private theorem caseI_S_le_commutator_W_Ap
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hZQ : t.Zv (-1) ≤ t.Qv 0) (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1)
    (hW : t.Zv 1 ≤ t.W) (hL0NW : t.L0 ≤ normalizer (t.W : Set G))
    (hA : ⁅t.Qv 1, t.Ap⁆ ≤ t.Am) :
    ⁅S, t.Ap⁆ ≤ t.W := by
  rw [Subgroup.commutator_le]
  intro s hs a ha
  have hs' : s ∈ t.Qv 1 ⊔ t.Zv (-1) := by
    have h := hS hs
    rwa [sup_comm] at h
  obtain ⟨q, hq, z, hz, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes
      (H := t.Qv 1) (K := t.Zv (-1)) (caseI_Zv_neg_one_le_normalizer_Qv_one t hfr hZQ)).mp hs'
  have hqQv1 : q ∈ t.Qv 1 := hq
  have hqAp' : q * a * q⁻¹ * a⁻¹ ∈ t.Ap := by
    have h1 : q * a * q⁻¹ ∈ t.Qv 0 :=
      (Subgroup.mem_normalizer_iff.mp
        ((t.Qv_one_le_normalizer_Qv hfr).1 hqQv1) a).mp ha.2
    have hmem0 : q * a * q⁻¹ * a⁻¹ ∈ t.Qv 0 :=
      (t.Qv 0).mul_mem h1 ((t.Qv 0).inv_mem ha.2)
    have h2 : q * a * q⁻¹ ∈ t.Qv 1 :=
      (t.Qv 1).mul_mem ((t.Qv 1).mul_mem hqQv1 ha.1) ((t.Qv 1).inv_mem hqQv1)
    have hmem1 : q * a * q⁻¹ * a⁻¹ ∈ t.Qv 1 :=
      (t.Qv 1).mul_mem h2 ((t.Qv 1).inv_mem ha.1)
    exact ⟨hmem1, hmem0⟩
  have hqW : q * a * q⁻¹ * a⁻¹ ∈ t.W := by
    rw [← t.Ap_inf_Am hfr]
    exact ⟨hqAp',
      hA (Subgroup.commutator_mem_commutator hqQv1 ha)⟩
  have hzW : z * a * z⁻¹ * a⁻¹ ∈ t.W := by
    have h := (t.caseI_commutator_Zv hQ₁Z₀).1 a ha.2 z hz
    have h' : a * z * a⁻¹ * z⁻¹ ∈ t.W := (hZ₁Z₀.trans hW) h
    rw [show z * a * z⁻¹ * a⁻¹ = (a * z * a⁻¹ * z⁻¹)⁻¹ by group]
    exact (t.W).inv_mem h'
  have hQv1L0 : t.Qv 1 ≤ t.L0 := (t.Qv_le_Sm hfr).1.trans le_sup_right
  have hqNW : q ∈ normalizer (t.W : Set G) := hL0NW (hQv1L0 hqQv1)
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact (t.W).mul_mem ((Subgroup.mem_normalizer_iff.mp hqNW _).mp hzW) hqW

private theorem caseI_S_le_commutator_Ap_sup_Am
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZQ : t.Zv (-1) ≤ t.Qv 0) (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1)
    (hD : ⁅t.Qv 1, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am) :
    ⁅S, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am := by
  rw [Subgroup.commutator_le]
  intro s hs x hx
  have hs' : s ∈ t.Qv 1 ⊔ t.Zv (-1) := by
    have h := hS hs
    rwa [sup_comm] at h
  obtain ⟨q, hq, z, hz, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes
      (H := t.Qv 1) (K := t.Zv (-1)) (caseI_Zv_neg_one_le_normalizer_Qv_one t hfr hZQ)).mp hs'
  have hqQv1 : q ∈ t.Qv 1 := hq
  have hqcomm : ⁅q, x⁆ ∈ t.Ap ⊔ t.Am :=
    hD (Subgroup.commutator_mem_commutator hqQv1 hx)
  have hzcomm : ⁅z, x⁆ ∈ t.Ap := by
    have hzQv0 : z ∈ t.Qv 0 := hZQ hz
    have h1 : x * z * x⁻¹ ∈ t.Qv 0 :=
      (Subgroup.mem_normalizer_iff.mp
        ((t.Qv_one_le_normalizer_Qv hfr).1 hx) z).mp hzQv0
    have hmem0 : z * x * z⁻¹ * x⁻¹ ∈ t.Qv 0 := by
      have hid : z * x * z⁻¹ * x⁻¹ = (x * z * x⁻¹ * z⁻¹)⁻¹ := by group
      rw [hid]
      exact (t.Qv 0).inv_mem ((t.Qv 0).mul_mem h1 ((t.Qv 0).inv_mem hzQv0))
    have hzS : z ∈ S :=
      (show t.Qv 0 ≤ S from by rw [t.Qv_zero]; exact Q1_le_S hfr.hF) (hZQ hz)
    have h2 : z * x * z⁻¹ ∈ t.Qv 1 :=
      (Subgroup.mem_normalizer_iff.mp (caseI_S_le_normalizer_Qv_one t hzS) x).mp hx
    have hmem1 : z * x * z⁻¹ * x⁻¹ ∈ t.Qv 1 :=
      (t.Qv 1).mul_mem h2 ((t.Qv 1).inv_mem hx)
    exact ⟨hmem1, hmem0⟩
  have hQv1NAp : t.Qv 1 ≤ normalizer (t.Ap : Set G) :=
    (le_inf le_normalizer (t.Qv_one_le_normalizer_Qv hfr).1).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQv1NAm : t.Qv 1 ≤ normalizer (t.Am : Set G) :=
    (le_inf le_normalizer (t.Qv_one_le_normalizer_Qv hfr).2).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hqN : q ∈ normalizer ((t.Ap ⊔ t.Am : Subgroup G) : Set G) :=
    (CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hQv1NAp hQv1NAm) hqQv1
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact (t.Ap ⊔ t.Am).mul_mem
    ((Subgroup.mem_normalizer_iff.mp hqN _).mp (Subgroup.mem_sup_left hzcomm)) hqcomm

private theorem caseI_commutator_mem_W_of_Am_le
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZQ : t.Zv (-1) ≤ t.Qv 0)
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1)
    (hL0NW : t.L0 ≤ normalizer (t.W : Set G))
    (hAmQv0 : t.Am ≤ t.Qv 0)
    {l : G} (hl : l ∈ t.L0) (hodd : Odd (orderOf l)) :
    ∀ x ∈ t.Qv 1, l * x * l⁻¹ * x⁻¹ ∈ t.W := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSQ : S ≤ t.Qv 1 ⊔ t.Qv 0 := caseI_S_le_Qv_one_sup_Qv_zero hS hZQ
  have hQv0L0 : t.Qv 0 ≤ t.L0 := by
    rw [t.Qv_zero]; exact (Q1_le_S hfr.hF).trans le_sup_left
  have hQv1L0 : t.Qv 1 ≤ t.L0 := (t.Qv_le_Sm hfr).1.trans le_sup_right
  have hQv2L0 : t.Qv 2 ≤ t.L0 := (t.Qv_le_Sm hfr).2.trans le_sup_right
  have hAmW : t.Am ≤ t.W := le_inf hAmQv0 inf_le_right
  have hx₂NW : t.x₂ ∈ normalizer (t.W : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr t.map_W_x₂
  have hApW : t.Ap ≤ t.W := by
    intro y hy
    have h1 : t.x₂ * y * t.x₂⁻¹ ∈ t.Am := by
      rw [← t.map_Ap_x₂]
      exact Subgroup.mem_map_of_mem _ hy
    have h2 : t.x₂ * y * t.x₂⁻¹ ∈ t.W := hAmW h1
    rw [show y = t.x₂⁻¹ * (t.x₂ * y * t.x₂⁻¹) * t.x₂ by group]
    exact (mem_iff_mem_conj_inv ((normalizer (t.W : Set G)).inv_mem hx₂NW)
      (y := t.x₂ * y * t.x₂⁻¹)).mp h2
  have h₁ : ∀ x ∈ t.Qv 0, ∀ a ∈ t.Qv 1, x * a * x⁻¹ * a⁻¹ ∈ t.W :=
    fun x hx a ha =>
      hApW (Subgroup.commutator_le.mp (caseI_commutator_Qv_zero_Qv_one_le_Ap t hfr) x hx a ha)
  have h₂ : ∀ x ∈ t.Qv 2, ∀ a ∈ t.Qv 1, x * a * x⁻¹ * a⁻¹ ∈ t.W :=
    fun x hx a ha =>
      hAmW (Subgroup.commutator_le.mp (caseI_commutator_Qv_two_Qv_one_le_Am t hfr) x hx a ha)
  have hmapQv0 : (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 2 := by
    simpa using t.map_Qv_x₂ 0
  have hmapQv1 : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
    simpa using t.map_Qv_x₂ 1
  have hSmSQ : t.Sm ≤ t.Qv 1 ⊔ t.Qv 2 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hSQ
    rw [Subgroup.map_sup, hmapQv1, hmapQv0] at h
    exact h
  have hgen : t.L0 ≤ t.Qv 0 ⊔ t.Qv 2 ⊔ t.Qv 1 := by
    have h1 : S ≤ (t.Qv 0 ⊔ t.Qv 2) ⊔ t.Qv 1 :=
      hSQ.trans (sup_le (le_sup_right : t.Qv 1 ≤ (t.Qv 0 ⊔ t.Qv 2) ⊔ t.Qv 1)
        ((le_sup_left : t.Qv 0 ≤ t.Qv 0 ⊔ t.Qv 2).trans le_sup_left))
    have h2 : t.Sm ≤ (t.Qv 0 ⊔ t.Qv 2) ⊔ t.Qv 1 :=
      hSmSQ.trans (sup_le (le_sup_right : t.Qv 1 ≤ (t.Qv 0 ⊔ t.Qv 2) ⊔ t.Qv 1)
        ((le_sup_right : t.Qv 2 ≤ t.Qv 0 ⊔ t.Qv 2).trans le_sup_left))
    exact sup_le h1 h2
  exact commutator_mem_of_coprime_of_le_sup (p := 2) (L := t.L0) (A := t.Qv 1) (B := t.W)
    (P := t.Qv 1) (X₁ := t.Qv 0) (X₂ := t.Qv 2) (t.isPGroup_Qv 1) hQv1L0 hQv0L0 hQv2L0
    t.L0_le_normalizer_Qv_one hL0NW h₁ h₂ hgen hl (Nat.coprime_two_right.mpr hodd)

private theorem caseI_Sm_le_normalizer_Am {L1 L2 S : Subgroup G} (t : Track L1 L2 S)
    (hSA : S ≤ normalizer (t.Ap : Set G)) :
    t.Sm ≤ normalizer (t.Am : Set G) := by
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hSA
  refine h.trans ?_
  have h2 := Subgroup.le_normalizer_map (f := (MulAut.conj t.x₂).toMonoidHom) (H := t.Ap)
  rwa [t.map_Ap_x₂] at h2

private theorem caseI_Sm_commutator_Qv_one_le {L1 L2 S : Subgroup G} (t : Track L1 L2 S)
    (hSQ : ⁅S, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am) : ⁅t.Sm, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am := by
  have hmapQv1 : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
    simpa using t.map_Qv_x₂ 1
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hSQ
  rw [Subgroup.map_sup, Subgroup.map_commutator, hmapQv1, t.map_Ap_x₂, t.map_Am_x₂,
    sup_comm] at h
  exact h

private theorem caseI_Sm_commutator_Am_le {L1 L2 S : Subgroup G} (t : Track L1 L2 S)
    (hSW : ⁅S, t.Ap⁆ ≤ t.W) : ⁅t.Sm, t.Am⁆ ≤ t.W := by
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hSW
  rw [Subgroup.map_commutator, t.map_Ap_x₂, t.map_W_x₂] at h
  exact h

private theorem caseI_commutator_mem_W_of_middle
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hZQ : t.Zv (-1) ≤ t.Qv 0)
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1)
    (hW : t.Zv 1 ≤ t.W ∧ t.W ≤ t.Qv 1 ∧ t.L0 ≤ normalizer (t.W : Set G))
    (hsqAm : ∀ a ∈ t.Am, a * a ∈ t.Qv 0)
    (hrootAm : ∀ s ∈ S, s * s ∈ t.Qv 0 → s ∈ t.Am ⊔ t.Qv 0)
    {l : G} (hl : l ∈ t.L0) (hodd : Odd (orderOf l)) :
    ∀ x ∈ t.Qv 1, l * x * l⁻¹ * x⁻¹ ∈ t.W := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQv1L0 : t.Qv 1 ≤ t.L0 := (t.Qv_le_Sm hfr).1.trans le_sup_right
  have hQv1NAp : t.Qv 1 ≤ normalizer (t.Ap : Set G) :=
    (le_inf le_normalizer (t.Qv_one_le_normalizer_Qv hfr).1).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQv1NAm : t.Qv 1 ≤ normalizer (t.Am : Set G) :=
    (le_inf le_normalizer (t.Qv_one_le_normalizer_Qv hfr).2).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hSA : S ≤ normalizer (t.Ap : Set G) :=
    (le_inf (caseI_S_le_normalizer_Qv_one t) (caseI_S_le_normalizer_Qv_zero t)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hS'A' : t.Sm ≤ normalizer (t.Am : Set G) := caseI_Sm_le_normalizer_Am t hSA
  have hWA : t.W ≤ t.Ap := le_inf hW.2.1 inf_le_left
  have hA : ⁅t.Qv 1, t.Ap⁆ ≤ t.Am := caseI_commutator_Qv_one_Ap_le_Am t hfr hsqAm
  have hA' : ⁅t.Qv 1, t.Am⁆ ≤ t.Ap := caseI_commutator_Qv_one_Am_le_Ap t hfr hsqAm
  have hD : ⁅t.Qv 1, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am :=
    caseI_commutator_Qv_one_Qv_one_le t hfr hrootAm
  have hDA : t.Am ≤ ⁅t.Qv 1, t.Qv 1⁆ ⊔ t.Ap :=
    caseI_Am_le_commutator_sup_Ap t hfr hZQ hS hsqAm
  have hDA' : t.Ap ≤ ⁅t.Qv 1, t.Qv 1⁆ ⊔ t.Am :=
    caseI_Ap_le_commutator_sup_Am t hfr hZQ hS hsqAm
  have hSW : ⁅S, t.Ap⁆ ≤ t.W :=
    caseI_S_le_commutator_W_Ap t hfr hZ₁Z₀ hQ₁Z₀ hZQ hS hW.1 hW.2.2 hA
  have hSQ : ⁅S, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am :=
    caseI_S_le_commutator_Ap_sup_Am t hfr hZQ hS hD
  have hS'Q : ⁅t.Sm, t.Qv 1⁆ ≤ t.Ap ⊔ t.Am := caseI_Sm_commutator_Qv_one_le t hSQ
  have hS'W : ⁅t.Sm, t.Am⁆ ≤ t.W := caseI_Sm_commutator_Am_le t hSW
  exact commutator_mem_of_coprime_of_central_images (p := 2) (L := t.L0) (Q₀ := t.Qv 1)
    (W := t.W) (A := t.Ap) (A' := t.Am) (S := S) (S' := t.Sm)
    (t.isPGroup_Qv 1) hQv1L0 hWA (inf_le_left : t.Ap ≤ t.Qv 1)
    (inf_le_left : t.Am ≤ t.Qv 1) hQv1NAp hQv1NAm hW.2.2 t.L0_le_normalizer_Qv_one
    (t.Ap_inf_Am hfr) (fun x hx a ha => Subgroup.commutator_le.mp hA x hx a ha)
    (fun x hx a ha => Subgroup.commutator_le.mp hA' x hx a ha) hD hDA hDA'
    le_sup_left le_sup_right le_rfl hSA hS'A'
    (fun s hs x hx => Subgroup.commutator_le.mp hSQ s hs x hx)
    (fun s hs x hx => Subgroup.commutator_le.mp hS'Q s hs x hx)
    (fun s hs a ha => Subgroup.commutator_le.mp hSW s hs a ha)
    (fun s hs a ha => Subgroup.commutator_le.mp hS'W s hs a ha)
    hl (Nat.coprime_two_right.mpr hodd)

theorem caseI_commutator_mem_W {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hZQ : t.Zv (-1) ≤ t.Qv 0) (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1)
    (hW : t.Zv 1 ≤ t.W ∧ t.W ≤ t.Qv 1 ∧ t.L0 ≤ normalizer (t.W : Set G))
    {l : G} (hl : l ∈ t.L0) (hodd : Odd (orderOf l)) :
    ∀ x ∈ t.Qv 1, l * x * l⁻¹ * x⁻¹ ∈ t.W := by
  have hSQ : S ≤ t.Qv 1 ⊔ t.Qv 0 := caseI_S_le_Qv_one_sup_Qv_zero hS.1 hZQ
  rcases t.caseI_trichotomy hfr hSQ with hAmQv0 | ⟨hsqAm, hrootAm⟩ | hS_AmQv0
  · exact caseI_commutator_mem_W_of_Am_le t hfr hZQ hS.1 hW.2.2 hAmQv0 hl hodd
  · exact caseI_commutator_mem_W_of_middle t hfr hZ₁Z₀ hQ₁Z₀ hZQ hS.1 hW hsqAm hrootAm hl hodd
  · exact (t.caseI_not_le_Am_sup hfr hW.2.2 hS_AmQv0).elim

private theorem caseI_commutator_W_Zv_one
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hZQ : t.Zv (-1) ≤ t.Qv 0)
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1)
    (hL0NW : t.L0 ≤ normalizer (t.W : Set G))
    {l : G} (hl : l ∈ t.L0) (hodd : Odd (orderOf l)) :
    ∀ x ∈ t.W, l * x * l⁻¹ * x⁻¹ ∈ t.Zv 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQv1L0 : t.Qv 1 ≤ t.L0 := (t.Qv_le_Sm hfr).1.trans le_sup_right
  have hZv1L0 : t.Zv (-1) ≤ t.L0 :=
    hZQ.trans ((show t.Qv 0 ≤ S from by rw [t.Qv_zero]; exact Q1_le_S hfr.hF).trans
      le_sup_left)
  have hZv3L0 : t.Zv 3 ≤ t.L0 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hZQ
    rw [t.map_Zv_x₂ (-1), t.map_Qv_x₂ 0] at h
    exact h.trans ((t.Qv_le_Sm hfr).2.trans le_sup_right)
  have hZv2Zv1 : t.Zv 2 ≤ t.Zv 1 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hZ₁Z₀
    rw [t.map_Zv_x₂ 0, t.map_Zv_x₂ 1] at h
    simpa using h
  have h₁ : ∀ z ∈ t.Zv (-1), ∀ a ∈ t.W, z * a * z⁻¹ * a⁻¹ ∈ t.Zv 1 := by
    intro z hz a ha
    have h := (t.caseI_commutator_Zv hQ₁Z₀).1 a ha.1 z hz
    have h' : a * z * a⁻¹ * z⁻¹ ∈ t.Zv 1 := hZ₁Z₀ h
    rw [show z * a * z⁻¹ * a⁻¹ = (a * z * a⁻¹ * z⁻¹)⁻¹ by group]
    exact (t.Zv 1).inv_mem h'
  have h₂ : ∀ z ∈ t.Zv 3, ∀ a ∈ t.W, z * a * z⁻¹ * a⁻¹ ∈ t.Zv 1 := by
    intro z hz a ha
    have h := (t.caseI_commutator_Zv hQ₁Z₀).2 a ha.2 z hz
    have h' : a * z * a⁻¹ * z⁻¹ ∈ t.Zv 1 := hZv2Zv1 h
    rw [show z * a * z⁻¹ * a⁻¹ = (a * z * a⁻¹ * z⁻¹)⁻¹ by group]
    exact (t.Zv 1).inv_mem h'
  have hgen : t.L0 ≤ t.Zv (-1) ⊔ t.Zv 3 ⊔ t.Qv 1 := by
    have h1 : S ≤ (t.Zv (-1) ⊔ t.Zv 3) ⊔ t.Qv 1 :=
      hS.1.trans (sup_le
        ((le_sup_left : t.Zv (-1) ≤ t.Zv (-1) ⊔ t.Zv 3).trans le_sup_left)
        (le_sup_right : t.Qv 1 ≤ (t.Zv (-1) ⊔ t.Zv 3) ⊔ t.Qv 1))
    have h2 : t.Sm ≤ (t.Zv (-1) ⊔ t.Zv 3) ⊔ t.Qv 1 :=
      hS.2.trans (sup_le
        ((le_sup_right : t.Zv 3 ≤ t.Zv (-1) ⊔ t.Zv 3).trans le_sup_left)
        (le_sup_right : t.Qv 1 ≤ (t.Zv (-1) ⊔ t.Zv 3) ⊔ t.Qv 1))
    exact sup_le h1 h2
  exact commutator_mem_of_coprime_of_le_sup (p := 2) (L := t.L0) (A := t.W) (B := t.Zv 1)
    (P := t.Qv 1) (X₁ := t.Zv (-1)) (X₂ := t.Zv 3) (t.isPGroup_Qv 1) hQv1L0 hZv1L0 hZv3L0
    hL0NW t.L0_le_normalizer_Zv_one h₁ h₂ hgen hl (Nat.coprime_two_right.mpr hodd)

theorem caseI_commutator_mem_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hZQ : t.Zv (-1) ≤ t.Qv 0) (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1)
    (hW : t.Zv 1 ≤ t.W ∧ t.W ≤ t.Qv 1 ∧ t.L0 ≤ normalizer (t.W : Set G))
    {l : G} (hl : l ∈ t.L0) (hodd : Odd (orderOf l)) :
    ∀ x ∈ t.Qv 1, l * x * l⁻¹ * x⁻¹ ∈ t.Zv 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQv1L0 : t.Qv 1 ≤ t.L0 := (t.Qv_le_Sm hfr).1.trans le_sup_right
  have hWZ : t.W ≤ normalizer (t.Zv 1 : Set G) :=
    (hW.2.1.trans hQv1L0).trans t.L0_le_normalizer_Zv_one
  have hWQv1 : IsPGroup 2 t.W := (t.isPGroup_Qv 1).to_le hW.2.1
  exact commutator_mem_of_coprime_of_commutator_mem (p := 2) (P := t.Qv 1) (W := t.W)
    (Z := t.Zv 1) hWQv1 hWZ (Nat.coprime_two_right.mpr hodd)
    (t.L0_le_normalizer_Zv_one hl)
    (caseI_commutator_mem_W t hfr hZ₁Z₀ hQ₁Z₀ hZQ hS hW hl hodd)
    (caseI_commutator_W_Zv_one t hfr hZ₁Z₀ hQ₁Z₀ hZQ hS hW.2.2 hl hodd)

private theorem caseI_floor_facts
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {E : Subgroup G}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hQE : pCoreOf 2 t.GT ≤ E)
    (hZ₀E : t.Zv 1 ≤ E) (hZ₀Q : t.Zv 1 ⊓ pCoreOf 2 t.GT = ⊥)
    (hEQ₁ : E ≤ t.Qv 0)
    (hEQ₂ : E ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ pCoreOf 2 t.GT) (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    {Lstar : Subgroup G} (hLstar : Lstar ≤ L2 ⊔ t.Qv 1) :
    (t.Zv (-1) ≤ t.Qv 0) ∧
      (S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1) ∧
      (t.Zv 1 ≤ t.W ∧ t.W ≤ t.Qv 1 ∧ t.L0 ≤ normalizer (t.W : Set G)) ∧
      (Lstar ≤ t.L0) := by
  have hZvQv : t.Zv 1 ≤ t.Qv 0 ∧ t.Zv (-1) ≤ t.Qv 0 :=
    t.caseI_Zv_le_Qv_zero hZ₀E hEQ₁
  have hZQ : t.Zv (-1) ≤ t.Qv 0 := hZvQv.2
  have hZQ₀ : t.Zv 1 ≤ t.Qv 0 := hZvQv.1
  have hZ : ¬ t.Zv (-1) ≤ t.Qv 1 :=
    t.caseI_not_Zv_le_Qv_one hfr hEab hQE hZ₀E hZ₀Q hEQ₂ hZ₁Z₀
  have hS : S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1 :=
    t.caseI_S_le hfr hZQ hZ
  have hW : t.Zv 1 ≤ t.W ∧ t.W ≤ t.Qv 1 ∧ t.L0 ≤ normalizer (t.W : Set G) :=
    t.caseI_W hfr hZ₁Z₀ hZQ₀ hQ₁Z₀ hS
  have hQv1L0 : t.Qv 1 ≤ t.L0 := (t.Qv_le_Sm hfr).1.trans le_sup_right
  have hLstarL0 : Lstar ≤ t.L0 := hLstar.trans (sup_le (t.L2_le_L0 hfr) hQv1L0)
  exact ⟨hZQ, hS, hW, hLstarL0⟩

private theorem caseI_oTwoRes_commutator
    {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hZQ : t.Zv (-1) ≤ t.Qv 0)
    (hS : S ≤ t.Zv (-1) ⊔ t.Qv 1 ∧ t.Sm ≤ t.Zv 3 ⊔ t.Qv 1)
    (hW : t.Zv 1 ≤ t.W ∧ t.W ≤ t.Qv 1 ∧ t.L0 ≤ normalizer (t.W : Set G))
    {Lstar : Subgroup G} (hLstarL0 : Lstar ≤ t.L0) :
    ∀ d ∈ t.Qv 1, ∀ l ∈ oTwoRes Lstar, l * d * l⁻¹ * d⁻¹ ∈ t.Zv 1 := by
  have hL0NZ : t.L0 ≤ normalizer (t.Zv 1 : Set G) := t.L0_le_normalizer_Zv_one
  have hYle : oTwoRes Lstar ≤
      CFSG.GroupTheory.commutatorCentralizerIn t.L0 (t.Zv 1) (t.Qv 1) hL0NZ := by
    change Subgroup.closure {x : G | x ∈ Lstar ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1} ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxLstar, m, hm, hxpow⟩
    have hxL0 : x ∈ t.L0 := hLstarL0 hxLstar
    have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxpow)
    refine (CFSG.GroupTheory.mem_commutatorCentralizerIn hL0NZ).mpr ⟨hxL0, ?_⟩
    intro d hd
    exact t.caseI_commutator_mem_Zv_one hfr hZ₁Z₀ hQ₁Z₀ hZQ hS hW hxL0 hxodd d hd
  intro d hd l hlY
  exact ((CFSG.GroupTheory.mem_commutatorCentralizerIn hL0NZ).mp (hYle hlY)).2 d hd

private theorem caseI_oTwoRes_centralizer {Q Lstar : Subgroup G}
    (hα : ∀ l ∈ Lstar, Odd (orderOf l) → ∀ x ∈ Q, l * x * l⁻¹ = x) :
    (oTwoRes Lstar ≤ Subgroup.centralizer (Q : Set G)) ∧
      ∀ l ∈ oTwoRes Lstar, ∀ x ∈ Q, l * x * l⁻¹ = x := by
  have hYcent : oTwoRes Lstar ≤ Subgroup.centralizer (Q : Set G) := by
    change Subgroup.closure {x : G | x ∈ Lstar ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1} ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxLstar, m, hm, hxpow⟩
    have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxpow)
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    have h := hα x hxLstar hxodd y hy
    have h2 : x * y = y * x := by
      have := congrArg (· * x) h
      simpa [mul_assoc] using this
    exact h2.symm
  refine ⟨hYcent, ?_⟩
  intro l hlY x hx
  have hcomm : x * l = l * x := (Subgroup.mem_centralizer_iff.mp (hYcent hlY)) x hx
  rw [← hcomm]
  group

private theorem caseI_oTwoRes_fixed_points {E Q Lstar : Subgroup G}
    (hCE : ∀ e ∈ E, (∀ l ∈ Lstar, Odd (orderOf l) → l * e * l⁻¹ = e) → e ∈ Q) :
    ∀ e ∈ E, (∀ l ∈ oTwoRes Lstar, l * e * l⁻¹ = e) → e ∈ Q := by
  intro e he hfix
  refine hCE e he ?_
  intro l hlLstar hlodd
  exact hfix l (Subgroup.subset_closure ⟨hlLstar, orderOf l, hlodd, pow_orderOf_eq_one l⟩)

theorem false_of_caseI {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {E Lstar : Subgroup G}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hQE : pCoreOf 2 t.GT ≤ E)
    (hZ₀E : t.Zv 1 ≤ E) (hZ₀Q : t.Zv 1 ⊓ pCoreOf 2 t.GT = ⊥)
    (hEQ₁ : E ≤ t.Qv 0) (hEQ₀ : E < t.Qv 1)
    (hEQ₂ : E ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ pCoreOf 2 t.GT) (hZ₁Z₀ : t.Zv 0 ≤ t.Zv 1)
    (hQ₁Z₀ : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hNQ : t.Qv 1 ⊓ normalizer (pCoreOf 2 t.GT : Set G) ≤ E)
    (hLstar : Lstar ≤ L2 ⊔ t.Qv 1)
    (hα : ∀ l ∈ Lstar, Odd (orderOf l) → ∀ x ∈ pCoreOf 2 t.GT, l * x * l⁻¹ = x)
    (hCE : ∀ e ∈ E, (∀ l ∈ Lstar, Odd (orderOf l) → l * e * l⁻¹ = e) →
      e ∈ pCoreOf 2 t.GT) : False := by
  obtain ⟨hZQ, hS, hW, hLstarL0⟩ :=
    caseI_floor_facts t hfr hEab hQE hZ₀E hZ₀Q hEQ₁ hEQ₂ hZ₁Z₀ hQ₁Z₀ hLstar
  have hDY := caseI_oTwoRes_commutator t hfr hZ₁Z₀ hQ₁Z₀ hZQ hS hW hLstarL0
  have hY := caseI_oTwoRes_centralizer (Q := pCoreOf 2 t.GT) (Lstar := Lstar) hα
  have hCE' := caseI_oTwoRes_fixed_points (E := E) (Q := pCoreOf 2 t.GT)
    (Lstar := Lstar) hCE
  exact CFSG.GroupTheory.false_of_lt_of_commutator_mem_of_centralizer_le
    (D := t.Qv 1) (E := E) (Q := pCoreOf 2 t.GT) (Z := t.Zv 1) (Y := oTwoRes Lstar)
    (t.isPGroup_Qv 1) hEQ₀ hEab hQE hZ₀E hDY hY.2 hCE' hNQ

end Track

end CFSG.Quasithin.Stroth.Rq

end
