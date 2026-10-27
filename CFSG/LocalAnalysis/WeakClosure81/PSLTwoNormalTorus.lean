module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.Quasithin.Background.A1bBasic

import CFSG.GroupTheory.SylowCover
import CFSG.GroupTheory.CentralizerMapMulEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.PSL2ReflectedTorusCard
import CFSG.Quasithin.Vol2.Ch11SecU1L3IN
import CFSG.Quasithin.Background.E1Invariance
import CFSG.CGT.PushingUpLit.SolKAb.CyclicTI
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicQuotient
import CFSG.Goldschmidt.Steps.Rank2List

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter

variable {Q : Type} [Group Q] {L : Subgroup Q} {K : Type} [Field K] [Finite K]

private theorem exists_cyclic_torus_data (e : ↥L ≃* PSL2 K)
    (hK : IsOddPrimePower (Nat.card K)) {z : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) :
    ∃ (U : Subgroup Q) (T : Subgroup (PSL2 K)) (s : PSL2 K),
      U ≤ L ⊓ Subgroup.centralizer {z} ∧ IsCyclic ↥U ∧ z ∈ U ∧
      (∀ x : Q, x ∈ U ↔ ∃ y : ↥L, e y ∈ T ∧ (y : Q) = x) ∧
      s ∉ T ∧ s * s = 1 ∧ (∀ x ∈ T, s * x * s⁻¹ = x⁻¹) ∧
      (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      Subgroup.centralizer ({e ⟨z, hzL⟩} : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s := by
  classical
  let zL : ↥L := ⟨z, hzL⟩
  let t : PSL2 K := e zL
  have ht2 : orderOf t = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz2]
  have htI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t :=
    CFSG.Goldschmidt.Rank2List.isInvolution_of_orderOf ht2
  obtain ⟨T, s, hTcyc, htT, hsI, hsT, hinvT, hC, -, -⟩ :=
    CFSG.GorensteinWalter.psl2_reflected_torus_card hK htI
  have hssq : s * s = 1 := by simpa [pow_two] using hsI.2
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a :=
    CFSG.CGT.PushingUpLit.SolKAb.forall_mul_comm_of_isCyclic hTcyc
  let U : Subgroup Q := (T.map e.symm.toMonoidHom).map L.subtype
  have hUmem : ∀ x : Q, x ∈ U ↔ ∃ y : ↥L, e y ∈ T ∧ (y : Q) = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      obtain ⟨a, haT, hay⟩ := Subgroup.mem_map.mp hy
      refine ⟨y, ?_, hyx⟩
      rw [← hay]
      simpa using haT
    · rintro ⟨y, hyT, rfl⟩
      refine Subgroup.mem_map.mpr ⟨y, Subgroup.mem_map.mpr ⟨e y, hyT, ?_⟩, rfl⟩
      simp
  have hUL : U ≤ L := Subgroup.map_subtype_le _
  have hUcyc : IsCyclic ↥U := by
    have h1 : IsCyclic ↥(T.map e.symm.toMonoidHom) :=
      CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase.isCyclic_map_of_isCyclic
        e.symm.toMonoidHom hTcyc
    exact CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase.isCyclic_map_of_isCyclic L.subtype h1
  have hzU : z ∈ U := by
    rw [hUmem]
    exact ⟨zL, htT, rfl⟩
  have hUC : U ≤ L ⊓ Subgroup.centralizer ({z} : Set Q) := by
    intro u hu
    refine ⟨hUL hu, ?_⟩
    obtain ⟨y, hyT, hyu⟩ := (hUmem u).mp hu
    have hyC : e y ∈ Subgroup.centralizer ({t} : Set (PSL2 K)) := by
      rw [hC]
      exact Subgroup.mem_sup_left hyT
    have hcomm : e y * t = t * e y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyC
    have h1 : e (y * zL) = e (zL * y) := by
      rw [map_mul, map_mul]
      exact hcomm
    have h2 : y * zL = zL * y := e.injective h1
    have h3 : (y : Q) * z = z * (y : Q) := congrArg Subtype.val h2
    rw [hyu] at h3
    exact Subgroup.mem_centralizer_singleton_iff.mpr h3
  exact ⟨U, T, s, hUC, hUcyc, hzU, hUmem, hsT, hssq, hinvT, hcommT, hC⟩

theorem exists_cyclic_torus_inf_centralizer (e : ↥L ≃* PSL2 K)
    (hK : IsOddPrimePower (Nat.card K)) {z : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) :
    ∃ U : Subgroup Q, U ≤ L ⊓ Subgroup.centralizer {z} ∧ IsCyclic ↥U ∧ z ∈ U ∧
      ∀ d ∈ L ⊓ Subgroup.centralizer {z}, d ∉ U →
        d * d = 1 ∧ ∀ u ∈ U, d * u * d⁻¹ = u⁻¹ := by
  classical
  obtain ⟨U, T, s, hUC, hUcyc, hzU, hUmem, hsT, hssq, hinvT, hcommT, hC⟩ :=
    exists_cyclic_torus_data e hK hzL hz2
  let zL : ↥L := ⟨z, hzL⟩
  let t : PSL2 K := e zL
  refine ⟨U, hUC, hUcyc, hzU, ?_⟩
  intro d hd hdU
  have hdL : d ∈ L := hd.1
  have hdC : d ∈ Subgroup.centralizer ({z} : Set Q) := hd.2
  let dL : ↥L := ⟨d, hdL⟩
  have hcommdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  have hd'C : e dL ∈ Subgroup.centralizer ({t} : Set (PSL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : dL * zL = zL * dL := Subtype.ext hcommdz
    show e dL * e zL = e zL * e dL
    rw [← map_mul, ← map_mul, h1]
  have hd'sup : e dL ∈ T ⊔ Subgroup.zpowers s := by
    rw [← hC]
    exact hd'C
  have hd'T : e dL ∉ T := by
    intro hmem
    exact hdU ((hUmem d).mpr ⟨dL, hmem, rfl⟩)
  obtain ⟨u, huT, hdu⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.eq_mul_of_mem_sup_zpowers hssq hinvT hd'sup hd'T
  have hdsq : (e dL) * (e dL) = 1 := by
    rw [hdu, show u * s * (u * s) = u * (s * u * s⁻¹) * (s * s) by group,
      hinvT u huT, hssq]
    simp
  have hdL2 : dL * dL = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    exact hdsq
  have hdd : d * d = 1 := by
    simpa using congrArg Subtype.val hdL2
  refine ⟨hdd, ?_⟩
  intro w hwU
  obtain ⟨wL, hwT, hwval⟩ := (hUmem w).mp hwU
  have hwit : e dL * e wL * (e dL)⁻¹ = (e wL)⁻¹ :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.inverts_of_mem_sup_zpowers hcommT hssq hinvT
      hd'sup hd'T (e wL) hwT
  have hwL : dL * wL * dL⁻¹ = wL⁻¹ := by
    apply e.injective
    simpa [map_mul, map_inv] using hwit
  simpa [hwval] using congrArg Subtype.val hwL

theorem le_of_isPGroup_of_le_centralizer [Finite Q] {U : Subgroup Q}
    (hQL : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ L) {z : Q}
    (hD : ∀ d ∈ L ⊓ Subgroup.centralizer {z}, d ∉ U → d * d = 1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {P : Subgroup Q} (hP : IsPGroup r P)
    (hPz : P ≤ Subgroup.centralizer {z}) : P ≤ U := by
  have hPL : P ≤ L := by
    intro x hx
    obtain ⟨k, hk⟩ := hQL x
    obtain ⟨n, hn⟩ := hP.exists_orderOf_dvd_pow ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hn
    exact CFSG.GroupTheory.mem_of_pow_two_pow_mem_of_orderOf_dvd_prime_pow hr hr2 hn hk
  exact CFSG.GroupTheory.le_of_isPGroup_of_forall_notMem_mul_self
    (D := L ⊓ Subgroup.centralizer ({z} : Set Q)) (U := U)
    (fun d hd hdU => hD d hd hdU) hr hr2 hP (le_inf hPL hPz)

theorem centralizer_le_normalizer_of_isSylowIn [Finite Q] {U : Subgroup Q}
    (hUc : IsCyclic ↥U) (hQL : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ L) {z : Q}
    (hD : ∀ d ∈ L ⊓ Subgroup.centralizer {z}, d ∉ U → d * d = 1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {P : Subgroup Q}
    (hP : CFSG.Quasithin.IsSylowIn r P (Subgroup.centralizer {z})) :
    Subgroup.centralizer {z} ≤ Subgroup.normalizer (P : Set Q) := by
  intro c hc
  let cP : Subgroup Q := P.map (MulAut.conj c).toMonoidHom
  have hPU : P ≤ U :=
    le_of_isPGroup_of_le_centralizer hQL hD hr hr2 hP.isPGroup hP.le
  have hCS : CFSG.Quasithin.A1b.conjSub c (Subgroup.centralizer ({z} : Set Q)) =
      Subgroup.centralizer ({z} : Set Q) := by
    rw [CFSG.Quasithin.A1b.conjSub, CFSG.GroupTheory.centralizer_singleton_map_mulEquiv]
    congr 1
    rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have hcPSylow : CFSG.Quasithin.IsSylowIn r cP (Subgroup.centralizer ({z} : Set Q)) := by
    have h := (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv (p := r) (MulAut.conj c)).mpr hP
    change CFSG.Quasithin.IsSylowIn r cP
      (CFSG.Quasithin.A1b.conjSub c (Subgroup.centralizer ({z} : Set Q))) at h
    rwa [hCS] at h
  have hcPU : cP ≤ U :=
    le_of_isPGroup_of_le_centralizer hQL hD hr hr2 hcPSylow.isPGroup hcPSylow.le
  have hcard : Nat.card ↥(P.subgroupOf U) = Nat.card ↥(cP.subgroupOf U) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPU).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcPU).toEquiv]
    exact (Subgroup.card_map_of_injective (K := P)
      (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective).symm
  have heq : P.subgroupOf U = cP.subgroupOf U :=
    (@IsCyclic.subgroup_eq_iff_card_eq ↥U _ hUc (P.subgroupOf U) (cP.subgroupOf U) _ _).mpr
      hcard
  have hPeq : P = cP := by
    have h := congrArg (Subgroup.map U.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hPU,
      Subgroup.map_subgroupOf_eq_of_le hcPU] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hPeq.symm

end CFSG.LocalAnalysis.WeakClosure81

end
