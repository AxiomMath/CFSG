module

public import CFSG.RankThree.PartTwo.Sec13.Notation
import CFSG.RankThree.PartTwo.Sec15.Gagen1510Lift
import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.CharacterTheory.CyclicBlocks.Fusion

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

private lemma exists_inverting_of_quotient {L S : Subgroup G} (hSL : S ≤ L)
    (hS9 : Nat.card S = 9)
    (hinv : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card E = 9 →
      ∃ t : ↥L ⧸ aschbacherSolvableCore 3 ↥L, ∀ z ∈ E, t * z * t⁻¹ = z⁻¹)
    {c : G} (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) :
    ∃ T ∈ L, (∀ q ∈ S, T * q * T⁻¹ = q⁻¹) ∧ T * c * T⁻¹ = c := by
  classical
  have hS3 : IsPGroup 3 S := Proof1510Steps.isPGroup_of_card_nine hS9
  set θL : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hθ3 : ¬ 3 ∣ Nat.card θL := Proof1510Steps.not_three_dvd_card_theta L
  have hLθ : L ≤ Subgroup.normalizer (θL : Set G) := by
    rw [hθL]
    exact Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (aschbacherSolvableCore 3 ↥L))
  have hSθ : S ≤ Subgroup.normalizer (θL : Set G) := hSL.trans hLθ
  set Sbar : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (S.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) with hSbar
  have hSbar9 : Nat.card Sbar = 9 := Proof1510Steps.card_map_mk_of_card_nine hSL hS9
  obtain ⟨tbar, htbar⟩ := hinv Sbar hSbar9
  obtain ⟨t₁, ht₁⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) tbar
  have hf : ∀ q ∈ S, (t₁ : G) * q * (t₁ : G)⁻¹ * (q⁻¹)⁻¹ ∈ θL := by
    intro q hq
    have hqL : q ∈ L := hSL hq
    have hqS : (⟨q, hqL⟩ : ↥L) ∈ S.subgroupOf L := Subgroup.mem_subgroupOf.mpr hq
    have hqbar : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) (⟨q, hqL⟩ : ↥L) ∈ Sbar :=
      Subgroup.mem_map_of_mem _ hqS
    have h := htbar _ hqbar
    rw [← ht₁] at h
    have hone : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
        (t₁ * ⟨q, hqL⟩ * t₁⁻¹ * ⟨q, hqL⟩) = 1 := by
      have h2 := congrArg
        (fun z => z * (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨q, hqL⟩) h
      simpa [map_mul, map_inv, mul_assoc] using h2
    have hmemL : t₁ * ⟨q, hqL⟩ * t₁⁻¹ * ⟨q, hqL⟩ ∈ aschbacherSolvableCore 3 ↥L :=
      (QuotientGroup.eq_one_iff _).mp hone
    have hmem : ((t₁ * ⟨q, hqL⟩ * t₁⁻¹ * ⟨q, hqL⟩ : ↥L) : G) ∈ θL :=
      Subgroup.mem_map.mpr ⟨_, hmemL, rfl⟩
    simpa [Subgroup.coe_mul] using hmem
  obtain ⟨T, hTθ, hTinv⟩ := exists_mul_conj_eq_of_coprime
    (p := 3) (K := θL) (Q := S) hθ3 hS3 hSθ (h := (t₁ : G)) (f := fun x => x⁻¹)
    (fun q hq => S.inv_mem hq) hf
  have hθle : θL ≤ L := by
    rw [hθL]
    exact Subgroup.map_subtype_le _
  have hTL : T ∈ L := hθle hTθ
  refine ⟨T * t₁, L.mul_mem hTL t₁.2, hTinv, ?_⟩
  have hTc : T * c * T⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLc hTL)]
    group
  have ht₁c : (t₁ : G) * c * (t₁ : G)⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLc t₁.2)]
    group
  calc (T * t₁ : G) * c * (T * t₁)⁻¹ = T * ((t₁ : G) * c * (t₁ : G)⁻¹) * T⁻¹ := by group
    _ = T * c * T⁻¹ := by rw [ht₁c]
    _ = c := hTc

private lemma isPGroup_zpowers_of_pow_three {x : G} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)

private lemma zpow_conj_mem_of_mem {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    {a b : H} (hab : a * b * a⁻¹ * b⁻¹ ∈ N) (n : ℤ) :
    a * b ^ n * a⁻¹ * (b ^ n)⁻¹ ∈ N := by
  have hq : (MulAut.conj (QuotientGroup.mk' N a)) (QuotientGroup.mk' N b) =
      (QuotientGroup.mk' N b) := by
    have h : (QuotientGroup.mk' N) (a * b * a⁻¹ * b⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hab
    rw [MulAut.conj_apply]
    simpa [map_mul, map_inv, mul_assoc] using congrArg (fun z => z * (QuotientGroup.mk' N b)) h
  have hpow : (MulAut.conj (QuotientGroup.mk' N a)) ((QuotientGroup.mk' N b) ^ n) =
      (QuotientGroup.mk' N b) ^ n := by
    rw [map_zpow, hq]
  have h : (QuotientGroup.mk' N) (a * b ^ n * a⁻¹ * (b ^ n)⁻¹) = 1 := by
    have h' := congrArg (fun z => z * ((QuotientGroup.mk' N b) ^ n)⁻¹) hpow
    rw [MulAut.conj_apply] at h'
    simpa [map_mul, map_inv, mul_assoc] using h'
  exact (QuotientGroup.eq_one_iff _).mp h

private lemma zpow_conj_mul_self_mem_of_mem {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    {a b : H} (hab : a * b * a⁻¹ * b ∈ N) (n : ℤ) :
    a * b ^ n * a⁻¹ * b ^ n ∈ N := by
  have hq : (MulAut.conj (QuotientGroup.mk' N a)) (QuotientGroup.mk' N b) =
      ((QuotientGroup.mk' N b))⁻¹ := by
    have h : (QuotientGroup.mk' N) (a * b * a⁻¹ * b) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hab
    rw [MulAut.conj_apply]
    simpa [map_mul, map_inv, mul_assoc] using congrArg (fun z => z * ((QuotientGroup.mk' N) b)⁻¹) h
  have hpow : (MulAut.conj (QuotientGroup.mk' N a)) ((QuotientGroup.mk' N b) ^ n) =
      ((QuotientGroup.mk' N b) ^ n)⁻¹ := by
    rw [map_zpow, hq, inv_zpow]
  have h : (QuotientGroup.mk' N) (a * b ^ n * a⁻¹ * b ^ n) = 1 := by
    have h' := congrArg (fun z => z * ((QuotientGroup.mk' N b) ^ n)) hpow
    rw [MulAut.conj_apply] at h'
    simpa [map_mul, map_inv, mul_assoc] using h'
  exact (QuotientGroup.eq_one_iff _).mp h

private lemma zpow_conj_mem_of_mem_normalizer {N : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (N : Set G))
    (hb : b ∈ Subgroup.normalizer (N : Set G))
    (hab : a * b * a⁻¹ * b⁻¹ ∈ N) (n : ℤ) :
    a * b ^ n * a⁻¹ * (b ^ n)⁻¹ ∈ N := by
  let H : Subgroup G := Subgroup.normalizer (N : Set G)
  have hN : N ≤ H := Subgroup.le_normalizer
  have haH : a ∈ H := ha
  have hbH : b ∈ H := hb
  let aH : H := ⟨a, haH⟩
  let bH : H := ⟨b, hbH⟩
  let NH : Subgroup H := N.subgroupOf H
  have hNH : NH.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr le_rfl
  have habH : aH * bH * aH⁻¹ * bH⁻¹ ∈ NH := hab
  have h := zpow_conj_mem_of_mem (N := NH) habH n
  have h' : ((aH * bH ^ n * aH⁻¹ * (bH ^ n)⁻¹ : H) : G) ∈ N := h
  simpa [aH, bH, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h' 

private lemma zpow_conj_mul_self_mem_of_mem_normalizer {N : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (N : Set G))
    (hb : b ∈ Subgroup.normalizer (N : Set G))
    (hab : a * b * a⁻¹ * b ∈ N) (n : ℤ) :
    a * b ^ n * a⁻¹ * b ^ n ∈ N := by
  let H : Subgroup G := Subgroup.normalizer (N : Set G)
  have hN : N ≤ H := Subgroup.le_normalizer
  have haH : a ∈ H := ha
  have hbH : b ∈ H := hb
  let aH : H := ⟨a, haH⟩
  let bH : H := ⟨b, hbH⟩
  let NH : Subgroup H := N.subgroupOf H
  have hNH : NH.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr le_rfl
  have habH : aH * bH * aH⁻¹ * bH ∈ NH := hab
  have h := zpow_conj_mul_self_mem_of_mem (N := NH) habH n
  have h' : ((aH * bH ^ n * aH⁻¹ * bH ^ n : H) : G) ∈ N := h
  simpa [aH, bH, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h' 

private lemma exists_commuting_lift {L : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (L : Set G)) (he3 : e ^ 3 = 1)
    {t : ↥L ⧸ aschbacherSolvableCore 3 ↥L} {t₀ : ↥L}
    (ht₀ : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) t₀ = t)
    (ht : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) t = t) :
    ∃ t' : ↥L, (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) t' = t ∧
      (t' : G) * e * (t' : G)⁻¹ = e := by
  classical
  set θL : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hθ3 : ¬ 3 ∣ Nat.card θL := Proof1510Steps.not_three_dvd_card_theta L
  have hLθ : L ≤ Subgroup.normalizer (θL : Set G) := by
    rw [hθL]
    exact Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (aschbacherSolvableCore 3 ↥L))
  have heθ : e ∈ Subgroup.normalizer (θL : Set G) := by
    rw [hθL]
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (aschbacherSolvableCore 3 ↥L)) heN
  have hQ3 : IsPGroup 3 (Subgroup.zpowers e) := isPGroup_zpowers_of_pow_three he3
  have hQθ : Subgroup.zpowers e ≤ Subgroup.normalizer (θL : Set G) :=
    Subgroup.zpowers_le.mpr heθ
  let ce : ↥L := ⟨e * (t₀ : G) * e⁻¹,
    (Subgroup.mem_normalizer_iff.mp heN (t₀ : G)).mp t₀.2⟩
  have hce : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ce = t := by
    rw [← ht, ← ht₀]
    rfl
  have hq : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) (ce * t₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hce, ht₀, mul_inv_cancel]
  have hmemL : ce * t₀⁻¹ ∈ aschbacherSolvableCore 3 ↥L :=
    (QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 ↥L) _).mp hq
  have hmem : ((ce * t₀⁻¹ : ↥L) : G) ∈ θL :=
    Subgroup.mem_map.mpr ⟨_, hmemL, rfl⟩
  have hbase : (t₀ : G) * e * (t₀ : G)⁻¹ * e⁻¹ ∈ θL := by
    have hinv := θL.inv_mem hmem
    simpa [ce, Subgroup.coe_mul, mul_inv_rev, mul_assoc] using hinv
  have hf : ∀ q ∈ Subgroup.zpowers e, (t₀ : G) * q * (t₀ : G)⁻¹ * (id q)⁻¹ ∈ θL := by
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    simpa using zpow_conj_mem_of_mem_normalizer (hLθ t₀.2) heθ hbase n
  obtain ⟨n, hnθ, hcomm⟩ := exists_mul_conj_eq_of_coprime
    (p := 3) (K := θL) (Q := Subgroup.zpowers e) hθ3 hQ3 hQθ (h := (t₀ : G))
    (f := id) (fun q hq => hq) hf
  have hθle : θL ≤ L := by
    rw [hθL]
    exact Subgroup.map_subtype_le _
  have hnL : n ∈ L := hθle hnθ
  have hnq : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨n, hnL⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.mp hnθ
    have hxeq : x = ⟨n, hnL⟩ := Subtype.ext hxn
    simpa [hxeq] using hx
  refine ⟨⟨n * t₀, L.mul_mem hnL t₀.2⟩, ?_, ?_⟩
  · show (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) (⟨n, hnL⟩ * t₀) = t
    rw [map_mul, hnq, one_mul, ht₀]
  · have h := hcomm e (Subgroup.mem_zpowers e)
    simpa using h

private lemma exists_inverting_of_htb {L : Subgroup G} {c b e : G}
    (hbS : b ∈ L) (hb3 : b ^ 3 = 1) (heb : e * b = b * e)
    {t : ↥L ⧸ aschbacherSolvableCore 3 ↥L} {t' : ↥L}
    (ht' : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) t' = t)
    (htb : t * ((⟨b, hbS⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * t⁻¹ =
      (((⟨b, hbS⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L))⁻¹)
    (hcommute : (t' : G) * e * (t' : G)⁻¹ = e)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) :
    ∃ T : ↥L, (T : G) * e * (T : G)⁻¹ = e ∧ (T : G) * b * (T : G)⁻¹ = b⁻¹ ∧
      (T : G) * c * (T : G)⁻¹ = c := by
  classical
  set θL : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hθ3 : ¬ 3 ∣ Nat.card θL := Proof1510Steps.not_three_dvd_card_theta L
  have hLθ : L ≤ Subgroup.normalizer (θL : Set G) := by
    rw [hθL]
    exact Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (aschbacherSolvableCore 3 ↥L))
  have hθle : θL ≤ L := by
    rw [hθL]
    exact Subgroup.map_subtype_le _
  set K : Subgroup G := θL ⊓ Subgroup.centralizer ({e} : Set G) with hKdef
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h
    rw [hKdef] at h
    exact hθ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hQ3 : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_three hb3
  have hbθ : b ∈ Subgroup.normalizer (θL : Set G) := hLθ hbS
  have hbe : b ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact heb.symm
  have hbC : b ∈ Subgroup.normalizer (Subgroup.centralizer ({e} : Set G) : Set G) :=
    Subgroup.le_normalizer hbe
  have hbK : b ∈ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    rw [Subgroup.mem_normalizer_iff] at hbθ hbC ⊢
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨(hbθ x).mp hx.1, (hbC x).mp hx.2⟩,
      fun hx => ⟨(hbθ x).mpr hx.1, (hbC x).mpr hx.2⟩⟩
  have hQK : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hbK
  have hbaseθ : (t' : G) * b * (t' : G)⁻¹ * b ∈ θL := by
    have hq : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
        (t' * ⟨b, hbS⟩ * t'⁻¹ * ⟨b, hbS⟩) = 1 := by
      have h := htb
      rw [← ht'] at h
      have h2 := congrArg (fun z => z * (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
        ⟨b, hbS⟩) h
      simpa [map_mul, map_inv, mul_assoc] using h2
    have hmemL : t' * ⟨b, hbS⟩ * t'⁻¹ * ⟨b, hbS⟩ ∈ aschbacherSolvableCore 3 ↥L :=
      (QuotientGroup.eq_one_iff _).mp hq
    have hmem : ((t' * ⟨b, hbS⟩ * t'⁻¹ * ⟨b, hbS⟩ : ↥L) : G) ∈ θL :=
      Subgroup.mem_map.mpr ⟨_, hmemL, rfl⟩
    simpa [Subgroup.coe_mul] using hmem
  have hf0 : ∀ q ∈ Subgroup.zpowers b,
      (t' : G) * q * (t' : G)⁻¹ * q ∈ K := by
    intro q hq
    refine ⟨?_, ?_⟩
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      simpa using zpow_conj_mul_self_mem_of_mem_normalizer (hLθ t'.2) (hLθ hbS) hbaseθ n
    · have hqcomm : Commute q e := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (show Commute b e from heb.symm) n
      have ht'e : (t' : G) * e = e * (t' : G) := by
        have h := congrArg (fun z => z * (t' : G)) hcommute
        simpa [mul_assoc] using h
      have ht'comm : Commute (t' : G) e := ht'e
      have hcomm : Commute ((t' : G) * q * (t' : G)⁻¹ * q) e :=
        ((ht'comm.mul_left hqcomm).mul_left ht'comm.inv_left).mul_left hqcomm
      show ((t' : G) * q * (t' : G)⁻¹ * q) ∈ Subgroup.centralizer ({e} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.eq
  have hf : ∀ q ∈ Subgroup.zpowers b,
      (t' : G) * q * (t' : G)⁻¹ * ((fun x => x⁻¹) q)⁻¹ ∈ K := by
    simpa using hf0
  obtain ⟨T, hTK, hTinv⟩ := exists_mul_conj_eq_of_coprime
    (p := 3) (K := K) (Q := Subgroup.zpowers b)
    hK3 hQ3 hQK (h := (t' : G)) (f := fun x => x⁻¹)
    (fun q hq => (Subgroup.zpowers b).inv_mem hq) hf
  let Tt' : ↥L := ⟨T * t', L.mul_mem (hθle hTK.1) t'.2⟩
  refine ⟨Tt', ?_, ?_, ?_⟩
  · have hTe : (T : G) * e * (T : G)⁻¹ = e := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hTK.2]
      group
    calc (Tt' : G) * e * (Tt' : G)⁻¹
        = T * ((t' : G) * e * (t' : G)⁻¹) * T⁻¹ := by
          simp [Tt', Subgroup.coe_mul]; group
      _ = T * e * T⁻¹ := by rw [hcommute]
      _ = e := hTe
  · have h := hTinv b (Subgroup.mem_zpowers b)
    simpa [Tt', Subgroup.coe_mul] using h
  · rw [Subgroup.mem_centralizer_singleton_iff.mp (hLc Tt'.2)]
    group

private lemma zpow_neg_two_mul_eq_self {b : G} (hb3 : b ^ 3 = 1) {j : ℕ} (hj3 : j < 3) :
    b ^ (-(2 * (j : ℤ))) = b ^ j := by
  rw [zpow_eq_zpow_emod' (m := -(2 * (j : ℤ))) (n := 3) hb3]
  interval_cases j <;> simp [pow_succ, hb3]

private lemma inv_pow_two_mul_eq_pow {b : G} (hb3 : b ^ 3 = 1) {j : ℕ} (hj3 : j < 3) :
    (b ^ (2 * j))⁻¹ = b ^ j := by
  rw [← zpow_natCast (n := 2 * j), ← zpow_neg]
  simpa [Nat.cast_mul] using zpow_neg_two_mul_eq_self hb3 hj3

private lemma pow_four_mul_eq_pow {b : G} (hb3 : b ^ 3 = 1) (j : ℕ) :
    b ^ (4 * j) = b ^ j := by
  rw [show 4 * j = 3 * j + j by ring, pow_add, pow_mul, hb3, one_pow, one_mul]

private lemma inv_pow_eq_pow_two_mul {b : G} (hb3 : b ^ 3 = 1) {j : ℕ} (hj3 : j < 3) :
    (b ^ j)⁻¹ = b ^ (2 * j) := by
  rw [← zpow_natCast (n := j), ← zpow_neg]
  rw [zpow_eq_zpow_emod' (m := -(j : ℤ)) (n := 3) hb3]
  interval_cases j <;> simp [pow_succ, hb3]

private lemma zpowers_pow_two_eq_of_pow_three {x : G} (hx3 : x ^ 3 = 1) :
    Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2
  · rw [Subgroup.zpowers_le]
    have hx : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hx3, one_mul]
    have hmem : ((x ^ 2) ^ 2) ∈ Subgroup.zpowers (x ^ 2) :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers (x ^ 2)) 2
    rwa [← hx] at hmem

private lemma action_case_one {c b T₁ T₂' : G} {j : ℕ}
    (hb3 : b ^ 3 = 1) (hj3 : j < 3)
    (hfix : T₂' * (c * b ^ j) * T₂'⁻¹ = c * b ^ j)
    (hinv₂ : T₂' * b * T₂'⁻¹ = b⁻¹)
    (hinv₁ : T₁ * b * T₁⁻¹ = b⁻¹) (hfix₁ : T₁ * c * T₁⁻¹ = c) :
    (T₁ * T₂') * c * (T₁ * T₂')⁻¹ = c * b ^ j := by
  have hinv₂_all : ∀ q ∈ Subgroup.zpowers b, T₂' * q * T₂'⁻¹ = q⁻¹ :=
    fun q hq => CFSG.CyclicBlocks.conj_mem_zpowers_eq_inv hq hinv₂
  have hinv₁_all : ∀ q ∈ Subgroup.zpowers b, T₁ * q * T₁⁻¹ = q⁻¹ :=
    fun q hq => CFSG.CyclicBlocks.conj_mem_zpowers_eq_inv hq hinv₁
  have hα : T₂' * c * T₂'⁻¹ = c * b ^ (2 * j) := by
    have h := hfix
    rw [show T₂' * (c * b ^ j) * T₂'⁻¹ = (T₂' * c * T₂'⁻¹) * (b ^ j)⁻¹ by
      rw [show (b ^ j)⁻¹ = T₂' * b ^ j * T₂'⁻¹ from
        (hinv₂_all _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) j)).symm]
      group] at h
    calc T₂' * c * T₂'⁻¹ = (T₂' * c * T₂'⁻¹) * (b ^ j)⁻¹ * b ^ j := by group
      _ = (c * b ^ j) * b ^ j := by rw [h]
      _ = c * b ^ (2 * j) := by
        rw [show c * b ^ j * b ^ j = c * (b ^ j * b ^ j) by group]
        rw [← pow_add, show j + j = 2 * j by ring]
  calc (T₁ * T₂') * c * (T₁ * T₂')⁻¹
      = T₁ * (T₂' * c * T₂'⁻¹) * T₁⁻¹ := by group
    _ = T₁ * (c * b ^ (2 * j)) * T₁⁻¹ := by rw [hα]
    _ = (T₁ * c * T₁⁻¹) * (T₁ * b ^ (2 * j) * T₁⁻¹) := by group
    _ = c * (T₁ * b ^ (2 * j) * T₁⁻¹) := by rw [hfix₁]
    _ = c * (b ^ (2 * j))⁻¹ := by
      rw [hinv₁_all _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) (2 * j))]
    _ = c * b ^ j := by rw [inv_pow_two_mul_eq_pow hb3 hj3]

private lemma action_case_two {c b c' T₁ T₂' : G} {j : ℕ}
    (hc3 : c ^ 3 = 1) (hb3 : b ^ 3 = 1) (hcb : c * b = b * c) (hj3 : j < 3)
    (hc'j : c' = c ^ 2 * b ^ j) (hfix : T₂' * c' * T₂'⁻¹ = c')
    (hinv₂ : T₂' * b * T₂'⁻¹ = b⁻¹)
    (hinv₁ : T₁ * b * T₁⁻¹ = b⁻¹) (hfix₁ : T₁ * c * T₁⁻¹ = c) :
    (T₁ * T₂') * c * (T₁ * T₂')⁻¹ = (c') ^ 2 := by
  have hinv₂_all : ∀ q ∈ Subgroup.zpowers b, T₂' * q * T₂'⁻¹ = q⁻¹ :=
    fun q hq => CFSG.CyclicBlocks.conj_mem_zpowers_eq_inv hq hinv₂
  have hinv₁_all : ∀ q ∈ Subgroup.zpowers b, T₁ * q * T₁⁻¹ = q⁻¹ :=
    fun q hq => CFSG.CyclicBlocks.conj_mem_zpowers_eq_inv hq hinv₁
  have hfix2 : T₂' * (c') ^ 2 * T₂'⁻¹ = (c') ^ 2 := by
    have h := congrArg (fun z => z ^ 2) hfix
    simpa [pow_two, mul_assoc] using h
  have hc'2 : (c') ^ 2 = c * b ^ (2 * j) := by
    rw [hc'j]
    have hcomm2 : Commute (c ^ 2) (b ^ j) :=
      (Commute.pow_left (show Commute c b from hcb) 2).pow_right j
    calc (c ^ 2 * b ^ j) ^ 2 = (c ^ 2) ^ 2 * (b ^ j) ^ 2 := hcomm2.mul_pow 2
      _ = c * b ^ (2 * j) := by
        rw [← pow_mul, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3]
        rw [show j * 2 = 2 * j by ring]
        group
  have hfix2' : T₂' * (c * b ^ (2 * j)) * T₂'⁻¹ = c * b ^ (2 * j) := by
    rw [← hc'2]; exact hfix2
  have hα : T₂' * c * T₂'⁻¹ = c * b ^ j := by
    have h := hfix2'
    rw [show T₂' * (c * b ^ (2 * j)) * T₂'⁻¹ =
        (T₂' * c * T₂'⁻¹) * (b ^ (2 * j))⁻¹ by
      rw [show (b ^ (2 * j))⁻¹ = T₂' * b ^ (2 * j) * T₂'⁻¹ from
        (hinv₂_all _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) (2 * j))).symm]
      group] at h
    calc T₂' * c * T₂'⁻¹ =
        (T₂' * c * T₂'⁻¹) * (b ^ (2 * j))⁻¹ * b ^ (2 * j) := by group
      _ = (c * b ^ (2 * j)) * b ^ (2 * j) := by rw [h]
      _ = c * b ^ (4 * j) := by
        rw [show c * b ^ (2 * j) * b ^ (2 * j) = c * (b ^ (2 * j) * b ^ (2 * j)) by group]
        rw [← pow_add, show 2 * j + 2 * j = 4 * j by ring]
      _ = c * b ^ j := by rw [pow_four_mul_eq_pow hb3 j]
  calc (T₁ * T₂') * c * (T₁ * T₂')⁻¹
      = T₁ * (T₂' * c * T₂'⁻¹) * T₁⁻¹ := by group
    _ = T₁ * (c * b ^ j) * T₁⁻¹ := by rw [hα]
    _ = (T₁ * c * T₁⁻¹) * (T₁ * b ^ j * T₁⁻¹) := by group
    _ = c * (T₁ * b ^ j * T₁⁻¹) := by rw [hfix₁]
    _ = c * (b ^ j)⁻¹ := by
      rw [hinv₁_all _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) j)]
    _ = c * b ^ (2 * j) := by rw [inv_pow_eq_pow_two_mul hb3 hj3]
    _ = (c') ^ 2 := by rw [hc'2]

private lemma conj_zpowers_eq_of_action {L : Subgroup G} {c b x T₁ T₂' : G}
    (hbL : b ∈ L) (hcL : c ∉ L)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hcb : c * b = b * c)
    (hxB : x ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) : Set G))
    (hxb : (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b)
    (hfix : T₂' * (x * c * x⁻¹) * T₂'⁻¹ = x * c * x⁻¹)
    (hinv₂ : T₂' * b * T₂'⁻¹ = b⁻¹)
    (hinv₁ : T₁ * b * T₁⁻¹ = b⁻¹) (hfix₁ : T₁ * c * T₁⁻¹ = c) :
    (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom =
      (Subgroup.zpowers c).map (MulAut.conj (T₁ * T₂')).toMonoidHom := by
  classical
  set B : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers b with hB
  have hBcard_b : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hc_notb : c ∉ Subgroup.zpowers b := fun h => hcL (Subgroup.zpowers_le.mpr hbL h)
  have hcomm_bc : ∀ a ∈ Subgroup.zpowers b, a * c = c * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (show Commute b c from hcb.symm) n).eq
  obtain ⟨hBea_bc, hBcard_bc⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
      (X := Subgroup.zpowers b) hBcard_b hcord hc_notb hcomm_bc
  have hBea : CFSG.Open.IsElemAbelian 3 B := by
    rw [hB, sup_comm]
    exact hBea_bc
  have hB9 : Nat.card B = 9 := by
    rw [hB, sup_comm, hBcard_bc]
    norm_num
  set c' : G := x * c * x⁻¹ with hc'def
  have hcB : c ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hc'B : c' ∈ B := (Subgroup.mem_normalizer_iff.mp hxB c).mp hcB
  have hc'3 : c' ^ 3 = 1 := by
    rw [hc'def]
    change (MulAut.conj x) c ^ 3 = 1
    rw [← map_pow, hc3, map_one]
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    rw [hc'def] at h
    calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hc'_card : Nat.card (Subgroup.zpowers c') = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc'3 hc'1]
  have hc'notb : c' ∉ Subgroup.zpowers b := by
    intro h
    have heq : Subgroup.zpowers c' = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h) (by
        rw [hc'_card, hBcard_b])
    have hxmap : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom =
        Subgroup.zpowers c' := by
      rw [MonoidHom.map_zpowers, hc'def]
      rfl
    have hmap : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom =
        (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom := by
      rw [hxmap, heq, hxb]
    have hc_eq : Subgroup.zpowers c = Subgroup.zpowers b :=
      Subgroup.map_injective (MulAut.conj x).injective hmap
    exact hc_notb (hc_eq ▸ Subgroup.mem_zpowers c)
  obtain ⟨i, hi3, b', hb', hc'mul⟩ :=
    exists_pow_mul_of_mem (A := B) (B := Subgroup.zpowers b) (a := c) hBea
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) rfl hc'B
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hc'notb
    rw [hc'mul, pow_zero, one_mul]
    exact hb'
  have hfin_b : IsOfFinOrder b :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hb3⟩
  obtain ⟨n, hn⟩ := hfin_b.mem_powers_iff_mem_zpowers.mpr hb'
  let j : ℕ := n % 3
  have hj3 : j < 3 := Nat.mod_lt _ (by norm_num)
  have hborder : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hbj : b ^ j = b' := by
    have h1 : b ^ j = b ^ n := by
      rw [show j = n % 3 from rfl, ← hborder, pow_mod_orderOf]
    rw [h1, ← hn]
  set w : G := T₁ * T₂' with hw
  have hi12 : i = 1 ∨ i = 2 := by omega
  have hmain : w * c * w⁻¹ = (c') ^ i := by
    rcases hi12 with rfl | rfl
    ·
      have hc'j : c' = c * b ^ j := by rw [hc'mul, hbj, pow_one]
      have hfixj : T₂' * (c * b ^ j) * T₂'⁻¹ = c * b ^ j := by
        rw [← hc'j]; exact hfix
      have h := action_case_one hb3 hj3 hfixj hinv₂ hinv₁ hfix₁
      simpa [w, hw, hc'j, pow_one] using h
    ·
      have hc'j : c' = c ^ 2 * b ^ j := by rw [hc'mul, hbj]
      have h := action_case_two hc3 hb3 hcb hj3 hc'j hfix hinv₂ hinv₁ hfix₁
      simpa [w, hw] using h
  have hzp : Subgroup.zpowers ((c') ^ i) = Subgroup.zpowers c' := by
    rcases hi12 with rfl | rfl
    · rw [pow_one]
    · exact zpowers_pow_two_eq_of_pow_three hc'3
  calc (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom
      = Subgroup.zpowers (x * c * x⁻¹) := by
        rw [MonoidHom.map_zpowers]
        rfl
    _ = Subgroup.zpowers c' := by rw [hc'def]
    _ = Subgroup.zpowers ((c') ^ i) := hzp.symm
    _ = Subgroup.zpowers (w * c * w⁻¹) := by rw [hmain]
    _ = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        rfl

private lemma mem_normalizer_sup_of_fixes {S : Subgroup G} {T c : G}
    (hc : T * c * T⁻¹ = c) (hS : ∀ q ∈ S, T * q * T⁻¹ = q⁻¹) :
    T ∈ Subgroup.normalizer ((Subgroup.zpowers c ⊔ S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hSmap : S.map (MulAut.conj T).toMonoidHom = S := by
    apply le_antisymm
    · rintro _ ⟨q, hq, rfl⟩
      change T * q * T⁻¹ ∈ S
      rw [hS q hq]
      exact S.inv_mem hq
    · intro q hq
      refine ⟨q⁻¹, S.inv_mem hq, ?_⟩
      change T * q⁻¹ * T⁻¹ = q
      rw [hS q⁻¹ (S.inv_mem hq)]
      simp
  erw [hSmap]
  simp [MulAut.conj_apply, hc]

private lemma mem_normalizer_sup_zpowers_of_mem_normalizer {A : Subgroup G} {T e : G}
    (hA : T ∈ Subgroup.normalizer (A : Set G)) (he : T * e * T⁻¹ = e) :
    T ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA ⊢
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  rw [hA]
  simp [MulAut.conj_apply, he]

private lemma mem_normalizer_map_conj_of_mem_normalizer {A : Subgroup G} {x T : G}
    (hT : T ∈ Subgroup.normalizer (A.map (MulAut.conj x⁻¹).toMonoidHom : Set G)) :
    x * T * x⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hT ⊢
  calc A.map (MulAut.conj (x * T * x⁻¹)).toMonoidHom
      = ((A.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj T).toMonoidHom).map
          (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext y
        change (MulAut.conj (x * T * x⁻¹)) y =
          (MulAut.conj x) ((MulAut.conj T) ((MulAut.conj x⁻¹) y))
        simp only [MulAut.conj_apply]
        group
    _ = (A.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [show Subgroup.map (MulAut.conj T).toMonoidHom
            (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom A) =
            Subgroup.map (MulAut.conj x⁻¹).toMonoidHom A from hT]
    _ = A := by
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj x).toMonoidHom.comp
            (MulAut.conj x⁻¹).toMonoidHom = (MulAut.conj (1 : G)).toMonoidHom := by
          ext y
          change (MulAut.conj x) ((MulAut.conj x⁻¹) y) = (MulAut.conj (1 : G)) y
          simp only [MulAut.conj_apply]
          group
        rw [hcomp, Late.map_conj_one]

theorem mem_omegaA_of_torus {A L : Subgroup G} {c b x e : G}
    (hcΩ : Subgroup.zpowers c ∈ omegaA A)
    (hS9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hinv : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card E = 9 →
      ∃ t : ↥L ⧸ aschbacherSolvableCore 3 ↥L, ∀ z ∈ E, t * z * t⁻¹ = z⁻¹)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcL : c ∉ L)
    (hbS : b ∈ A ⊓ L) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hxB : x ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) : Set G))
    (hxb : (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b)
    (hA' : A.map (MulAut.conj x⁻¹).toMonoidHom =
      Subgroup.zpowers c ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers e)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) (he3 : e ^ 3 = 1)
    (heb : e * b = b * e) {t : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (ht : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩) t = t)
    (htb : t * ((⟨b, hbS.2⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * t⁻¹ =
      (((⟨b, hbS.2⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L))⁻¹) :
    (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈ omegaA A := by
  classical
  set S : Subgroup G := A ⊓ L with hSdef
  have hSL : S ≤ L := inf_le_right
  obtain ⟨T₁, -, hT₁inv, hT₁c⟩ :=
    exists_inverting_of_quotient hSL hS9 hinv hLc
  have hT₁b : T₁ * b * T₁⁻¹ = b⁻¹ := hT₁inv b hbS
  obtain ⟨t₀, ht₀⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) t
  obtain ⟨t', ht'mk, ht'e⟩ := exists_commuting_lift heN he3 ht₀ ht
  obtain ⟨T₂, hT₂e, hT₂b, hT₂c⟩ :=
    exists_inverting_of_htb hbS.2 hb3 heb ht'mk htb ht'e hLc
  set T₂' : G := x * (T₂ : G) * x⁻¹ with hT₂'def
  have hT₂_inv_all : ∀ q ∈ Subgroup.zpowers b, (T₂ : G) * q * (T₂ : G)⁻¹ = q⁻¹ :=
    fun q hq => CFSG.CyclicBlocks.conj_mem_zpowers_eq_inv hq hT₂b
  have hT₂_cb : (T₂ : G) ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_fixes hT₂c hT₂_inv_all
  have hT₂Ax : (T₂ : G) ∈ Subgroup.normalizer
      ((A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [hA']
    exact mem_normalizer_sup_zpowers_of_mem_normalizer hT₂_cb hT₂e
  have hT₂'A : T₂' ∈ Subgroup.normalizer (A : Set G) := by
    rw [hT₂'def]
    exact mem_normalizer_map_conj_of_mem_normalizer hT₂Ax
  have hT₁A : T₁ ∈ Subgroup.normalizer (A : Set G) := by
    rw [hAeq]
    exact mem_normalizer_sup_of_fixes hT₁c hT₁inv
  have hT₂'_fix : T₂' * (x * c * x⁻¹) * T₂'⁻¹ = x * c * x⁻¹ := by
    rw [hT₂'def]
    calc (x * (T₂ : G) * x⁻¹) * (x * c * x⁻¹) * (x * (T₂ : G) * x⁻¹)⁻¹
        = x * ((T₂ : G) * c * (T₂ : G)⁻¹) * x⁻¹ := by group
      _ = x * c * x⁻¹ := by rw [hT₂c]
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxb
  have hb1_mem : x⁻¹ * b * x ∈ Subgroup.zpowers b := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) b).mp (Subgroup.mem_zpowers b)
    simpa using h
  have hT₂'_b : T₂' * b * T₂'⁻¹ = b⁻¹ := by
    rw [hT₂'def]
    calc (x * (T₂ : G) * x⁻¹) * b * (x * (T₂ : G) * x⁻¹)⁻¹
        = x * ((T₂ : G) * (x⁻¹ * b * x) * (T₂ : G)⁻¹) * x⁻¹ := by group
      _ = x * (x⁻¹ * b * x)⁻¹ * x⁻¹ := by rw [hT₂_inv_all _ hb1_mem]
      _ = b⁻¹ := by group
  have hc3 : c ^ 3 = 1 := by
    have h : orderOf c = 3 := by
      rw [← Nat.card_zpowers]
      exact (zpowers_mem_omegaA_iff.mp hcΩ).2.1
    rw [← h]
    exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    exact hcL (h ▸ Subgroup.one_mem L)
  have hcb : c * b = b * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hLc hbS.2)).symm
  have hBeq := conj_zpowers_eq_of_action hbS.2 hcL hc3 hc1 hb3 hb1 hcb hxB hxb
    hT₂'_fix hT₂'_b hT₁b hT₁c
  set w : G := T₁ * T₂' with hwdef
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := by
    rw [hwdef]
    exact Subgroup.mul_mem _ hT₁A hT₂'A
  have hBeq' : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom =
      (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
    simpa [hwdef] using hBeq
  rw [hBeq']
  exact (Sec13.map_conj_mem_omegaA_iff hwA).mpr hcΩ

end CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse
