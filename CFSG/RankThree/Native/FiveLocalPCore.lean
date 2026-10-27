module

public import CFSG.RankThree.Native.FiveLocalBasic
import CFSG.RankThree.Native.FiveLocalForms
import CFSG.RankThree.Native.FiveLocalPCoreAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.RankThree.Native.FiveLocal

open Subgroup CFSG.Monster.B.Pinned
open scoped Matrix

namespace Rel

section Steps

variable {G : Type*} [Group G] [Finite G] {x h z : G} {q : Fin 4 → G} (hR : Rel x h q z)
include hR

theorem P_le_centralizer : P x q ≤ centralizer ({z} : Set G) := by
  intro g hg
  rw [← hR.centralizer_ZQ]
  exact (Subgroup.mem_inf.1 (hR.P_le_H0 hg)).2

theorem pCore_centralizer_le_P (h5 : (Nat.card G).factorization 5 = 6) :
    (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype ≤
      P x q := by
  let C := centralizer ({z} : Set G)
  obtain ⟨S, hS⟩ := hR.P_sylow h5
  have hSC : (S : Subgroup G) ≤ C := hS ▸ hR.P_le_centralizer
  let S' : Sylow 5 ↥C := S.subtype hSC
  have hcarrier : (S' : Subgroup ↥C) = (P x q).subgroupOf C := by
    rw [Sylow.coe_subtype, hS]
  have hpCore_le : CFSG.pCore 5 ↥C ≤ (S' : Subgroup ↥C) :=
    IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 5) (G := ↥C)) S'
  rw [hcarrier] at hpCore_le
  calc (CFSG.pCore 5 ↥C).map C.subtype
      ≤ ((P x q).subgroupOf C).map C.subtype := Subgroup.map_mono hpCore_le
    _ = P x q ⊓ C := Subgroup.subgroupOf_map_subtype (P x q) C
    _ ≤ P x q := inf_le_left

omit [Finite G] in
theorem zpowers_le_pCore_centralizer :
    zpowers z ≤
      (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype := by
  let C := centralizer ({z} : Set G)
  have hzC : z ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hz_center : (⟨z, hzC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hle_center : zpowers (⟨z, hzC⟩ : C) ≤ Subgroup.center C := by
    rw [Subgroup.zpowers_le]
    exact hz_center
  have hnormal : (zpowers (⟨z, hzC⟩ : C)).Normal := Subgroup.normal_of_le_center hle_center
  have hcard : Nat.card (zpowers (⟨z, hzC⟩ : C)) = 5 ^ 1 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (⟨z, hzC⟩ : C), hR.orderOf_z]
    norm_num
  have hisPGroup : IsPGroup 5 (zpowers (⟨z, hzC⟩ : C)) := IsPGroup.of_card hcard
  have hmem : zpowers (⟨z, hzC⟩ : C) ∈ {K : Subgroup C | K.Normal ∧ IsPGroup 5 K} :=
    ⟨hnormal, hisPGroup⟩
  have hle : zpowers (⟨z, hzC⟩ : C) ≤ CFSG.pCore 5 C := le_sSup hmem
  have himg : (zpowers (⟨z, hzC⟩ : C)).map C.subtype = zpowers z := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [← himg]
  exact Subgroup.map_mono hle

omit hR [Finite G] in
theorem conj_mem_pCore_centralizer {g u : G} (hg : g ∈ centralizer ({z} : Set G))
    (hu : u ∈
      (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype) :
    g⁻¹ * u * g ∈
      (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype := by
  let C := centralizer ({z} : Set G)
  obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu
  have hw' : (⟨g, hg⟩ : C)⁻¹ * w * ⟨g, hg⟩ ∈ CFSG.pCore 5 C :=
    (inferInstance : (CFSG.pCore 5 C).Normal).conj_mem' w hw ⟨g, hg⟩
  have hval : C.subtype ((⟨g, hg⟩ : C)⁻¹ * w * ⟨g, hg⟩) = g⁻¹ * u * g := by
    rw [map_mul, map_mul, map_inv, hwu]
    rfl
  rw [← hval]
  exact Subgroup.mem_map_of_mem C.subtype hw'

theorem pCore_centralizer_le_Q (h5 : (Nat.card G).factorization 5 = 6) :
    (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype ≤
      Q q := by
  let C := centralizer ({z} : Set G)
  intro u huO
  have huP : u ∈ P x q := hR.pCore_centralizer_le_P h5 huO
  obtain ⟨i, hi, hAi⟩ := hR.exists_A_eq_pow_of_mem_P huP
  have hyH0 : i0Elt x h 1 ∈ H0 x h q := hR.i0Elt_mem_H0 1
  have hyC : i0Elt x h 1 ∈ centralizer ({z} : Set G) := by
    rw [← hR.centralizer_ZQ]
    exact (Subgroup.mem_inf.1 hyH0).2
  have hyuO : (i0Elt x h 1)⁻¹ * u * i0Elt x h 1 ∈
      (CFSG.pCore 5 C).map C.subtype :=
    conj_mem_pCore_centralizer hyC huO
  have hyuP : (i0Elt x h 1)⁻¹ * u * i0Elt x h 1 ∈ P x q :=
    hR.pCore_centralizer_le_P h5 hyuO
  obtain ⟨j, hj, hAj⟩ := hR.exists_A_eq_pow_of_mem_P hyuP
  have huK : u ∈ K x h q := hR.P_le_K huP
  have hconj := hR.A_conj_i0Elt_one huK
  have hEq : f5H * f5X ^ 4 * f5H ^ 7 * f5X ^ i * (f5H * f5X * f5H ^ 7) = f5X ^ j := by
    rw [hAi] at hconj
    rw [hAj] at hconj
    exact hconj.symm
  have hi0 : i = 0 := CFSG.RankThree.Native.f5_conj_pow_X_eq_pow_X hi hj hEq
  have hA : A q z u = 1 := by
    rw [hAi, hi0, pow_zero]
  exact hR.mem_Q_of_mem_P_of_A_eq_one huP hA

omit [Finite G] in
private theorem crd_pow {w : G} (hw : w ∈ Q q) (n : ℕ) :
    crd q z (w ^ n) = n • crd q z w := by
  induction n with
  | zero => rw [pow_zero, show crd q z 1 = 0 from hR.commData.coord_one, zero_smul]
  | succ n ih =>
    rw [pow_succ, show crd q z (w ^ n * w) = crd q z (w ^ n) + crd q z w from
      hR.commData.coord_mul (pow_mem hw n) hw, ih, succ_nsmul]

private def crdSubmodule (O : Subgroup G) (hO : O ≤ Q q) :
    Submodule (ZMod 5) (Fin 4 → ZMod 5) where
  carrier := {v | ∃ w ∈ O, crd q z w = v}
  zero_mem' := by
    refine ⟨1, O.one_mem, ?_⟩
    exact hR.commData.coord_one
  add_mem' := by
    rintro v w ⟨a, ha, hva⟩ ⟨b, hb, hvb⟩
    refine ⟨a * b, O.mul_mem ha hb, ?_⟩
    rw [← hva, ← hvb]
    exact hR.commData.coord_mul (hO ha) (hO hb)
  smul_mem' := by
    rintro c v ⟨a, ha, hva⟩
    refine ⟨a ^ c.val, O.pow_mem ha c.val, ?_⟩
    rw [← hva]
    have hsmul : c • crd q z a = c.val • crd q z a := by
      conv_lhs => rw [show c = (c.val : ZMod 5) from (ZMod.natCast_zmod_val c).symm]
      rw [Nat.cast_smul_eq_nsmul]
    rw [hsmul]
    exact crd_pow hR (hO ha) c.val

private def crdSubmodulePCore (hR' : Rel x h q z) (h5 : (Nat.card G).factorization 5 = 6) :
    Submodule (ZMod 5) (Fin 4 → ZMod 5) :=
  crdSubmodule hR' ((CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map
    (centralizer ({z} : Set G)).subtype) (hR'.pCore_centralizer_le_Q h5)

private theorem crdSubmodulePCore_vecMul_mem (h5 : (Nat.card G).factorization 5 = 6)
    {g : G} (hgH0 : g ∈ H0 x h q)
    {v : Fin 4 → ZMod 5} (hv : v ∈ crdSubmodulePCore hR h5) :
    v ᵥ* A q z g ∈ crdSubmodulePCore hR h5 := by
  obtain ⟨w, hwO, hvw⟩ := hv
  refine ⟨g⁻¹ * w * g, ?_, ?_⟩
  · have hgC : g ∈ centralizer ({z} : Set G) := by
      rw [← hR.centralizer_ZQ]
      exact (Subgroup.mem_inf.1 hgH0).2
    exact conj_mem_pCore_centralizer hgC hwO
  · rw [← hvw]
    exact hR.crd_conj (H0_le_K hgH0) ((hR.pCore_centralizer_le_Q h5) hwO)

private theorem crdSubmodulePCore_vecMul_f5I0Mat_mem (h5 : (Nat.card G).factorization 5 = 6)
    (k : Fin 5) {v : Fin 4 → ZMod 5} (hv : v ∈ crdSubmodulePCore hR h5) :
    v ᵥ* f5I0Mat k ∈ crdSubmodulePCore hR h5 := by
  rw [← hR.A_i0Elt k]
  exact crdSubmodulePCore_vecMul_mem hR h5 (hR.i0Elt_mem_H0 k) hv

theorem pCore_centralizer_eq_Q_of_crd_ne_zero (h5 : (Nat.card G).factorization 5 = 6) {u : G}
    (hu : u ∈
      (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype)
    (hcrd : crd q z u ≠ 0) :
    (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype =
      Q q := by
  let C := centralizer ({z} : Set G)
  let O := (CFSG.pCore 5 C).map C.subtype
  have hOleQ : O ≤ Q q := hR.pCore_centralizer_le_Q h5
  let S : Submodule (ZMod 5) (Fin 4 → ZMod 5) := crdSubmodulePCore hR h5
  have hv_mem : crd q z u ∈ S := by
    change ∃ w ∈ O, crd q z w = crd q z u
    exact ⟨u, hu, rfl⟩
  have hv_ne : crd q z u ≠ 0 := hcrd
  obtain ⟨a, b, hdet⟩ := CFSG.RankThree.Native.exists_det_rows_ne_zero hv_ne
  let R : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
    Matrix.of fun i => crd q z u ᵥ* f5I0Mat (a i) ᵥ* f5I0Mat (b i)
  have hRdet : R.det ≠ 0 := hdet
  have hrow_mem (i : Fin 4) : R i ∈ S := by
    change crd q z u ᵥ* f5I0Mat (a i) ᵥ* f5I0Mat (b i) ∈ S
    have h1 : crd q z u ᵥ* f5I0Mat (a i) ∈ S :=
      crdSubmodulePCore_vecMul_f5I0Mat_mem hR h5 (a i) hv_mem
    exact crdSubmodulePCore_vecMul_f5I0Mat_mem hR h5 (b i) h1
  have hall (w : Fin 4 → ZMod 5) : w ∈ S := by
    have hunit : IsUnit R.det := isUnit_iff_ne_zero.2 hRdet
    have hRinv : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hunit
    have hw_eq : w = (w ᵥ* R⁻¹) ᵥ* R := by
      rw [Matrix.vecMul_vecMul, hRinv, Matrix.vecMul_one]
    rw [hw_eq]
    rw [Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem (p := S) fun i _ => Submodule.smul_mem S _ (hrow_mem i)
  have hQ_le_O : Q q ≤ O := by
    intro g hgQ
    have hgS : crd q z g ∈ crdSubmodulePCore hR h5 := hall (crd q z g)
    obtain ⟨w, hwO, hwcrd⟩ := hgS
    have hwQ : w ∈ Q q := hOleQ hwO
    have hwgQ : w⁻¹ * g ∈ Q q := (Q q).mul_mem ((Q q).inv_mem hwQ) hgQ
    have hwcrd_coord : coord 5 q z f5M w = coord 5 q z f5M g := hwcrd
    have hcrd_wg : crd q z (w⁻¹ * g) = 0 := by
      change coord 5 q z f5M (w⁻¹ * g) = 0
      rw [hR.commData.coord_mul ((Q q).inv_mem hwQ) hgQ,
        hR.commData.coord_inv hwQ, hwcrd_coord]
      simp
    let t : Q q := ⟨w⁻¹ * g, hwgQ⟩
    have ht_ker : t ∈ hR.commData.coordHom.ker := by
      rw [MonoidHom.mem_ker, CommData.coordHom_apply]
      change Multiplicative.ofAdd (crd q z (w⁻¹ * g)) = 1
      rw [hcrd_wg]
      rfl
    have ht_zQ : t ∈ zQ q z := by
      rw [← CommData.ker_coordHom hR.commData]
      exact ht_ker
    have hwg_zpowers : w⁻¹ * g ∈ zpowers z := by
      change (t : G) ∈ zpowers z
      rw [← Subgroup.mem_subgroupOf]
      exact ht_zQ
    have hwg_O : w⁻¹ * g ∈ O := hR.zpowers_le_pCore_centralizer hwg_zpowers
    have e : w * (w⁻¹ * g) = g := by group
    rw [← e]
    exact O.mul_mem hwO hwg_O
  exact le_antisymm hOleQ hQ_le_O

theorem pCore_centralizer_eq_zpowers_of_crd_eq_zero (h5 : (Nat.card G).factorization 5 = 6)
    (hcrd : ∀ u ∈
      (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype,
      crd q z u = 0) :
    (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype =
      zpowers z := by
  let C := centralizer ({z} : Set G)
  let O := (CFSG.pCore 5 C).map C.subtype
  have hOleQ : O ≤ Q q := hR.pCore_centralizer_le_Q h5
  have hOle_zpowers : O ≤ zpowers z := by
    intro u huO
    have huQ : u ∈ Q q := hOleQ huO
    have hcrd_u : crd q z u = 0 := hcrd u huO
    have hu_ker : (⟨u, huQ⟩ : Q q) ∈ hR.commData.coordHom.ker := by
      rw [MonoidHom.mem_ker, CommData.coordHom_apply]
      change Multiplicative.ofAdd (crd q z u) = 1
      rw [hcrd_u]
      rfl
    have hu_zQ : (⟨u, huQ⟩ : Q q) ∈ zQ q z := by
      rw [← CommData.ker_coordHom hR.commData]
      exact hu_ker
    exact (Subgroup.mem_subgroupOf (H := zpowers z) (K := Q q)).1 hu_zQ
  have hle : zpowers z ≤ O := hR.zpowers_le_pCore_centralizer
  exact le_antisymm hOle_zpowers hle

end Steps

theorem pCore_centralizer_eq_Q_or_zpowers {G : Type*} [Group G] [Finite G] {x h z : G}
    {q : Fin 4 → G} (hR : Rel x h q z) (h5 : (Nat.card G).factorization 5 = 6) :
    (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype =
        Q q ∨
      (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype =
        zpowers z := by
  by_cases hc : ∃ u ∈ (CFSG.pCore 5 ↥(centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype, crd q z u ≠ 0
  · obtain ⟨u, hu, hcrd⟩ := hc
    exact Or.inl (hR.pCore_centralizer_eq_Q_of_crd_ne_zero h5 hu hcrd)
  · push Not at hc
    exact Or.inr (hR.pCore_centralizer_eq_zpowers_of_crd_eq_zero h5 hc)

end Rel

end CFSG.RankThree.Native.FiveLocal
