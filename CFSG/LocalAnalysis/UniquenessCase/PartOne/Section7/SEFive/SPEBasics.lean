module

import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]

theorem pPrimeCore_eq_bot_of_centralizer_le {N R : Subgroup X} (hRN : R ≤ N)
    (hR : IsPGroup p R) (hnorm : N ≤ Subgroup.normalizer (R : Set X))
    (hC : Subgroup.centralizer (R : Set X) ≤ R) : CFSG.pPrimeCore p ↥N = ⊥ := by
  classical
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hKnorm hKcop
  have hRN' : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr hnorm
  have hcardRN : Nat.card (R.subgroupOf N) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have hcopKR : Nat.Coprime (Nat.card K) (Nat.card (R.subgroupOf N)) := by
    rw [hcardRN, hn]
    exact hKcop.symm.pow_right n
  have hdisj : Disjoint K (R.subgroupOf N) :=
    Subgroup.disjoint_of_coprime_natCard hcopKR
  have hcomm : ∀ k ∈ K, ∀ r ∈ R.subgroupOf N, Commute k r :=
    fun k hk r hr =>
      Subgroup.commute_of_normal_of_disjoint K (R.subgroupOf N) hKnorm hRN' hdisj k r hk hr
  have hKmap_le_R : K.map N.subtype ≤ R := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrN : r ∈ N := hRN hr
    have hkcomm : Commute k ⟨r, hrN⟩ :=
      hcomm k hk ⟨r, hrN⟩ (Subgroup.mem_subgroupOf.mpr hr)
    exact congrArg N.subtype hkcomm.symm
  have hKmap_p : IsPGroup p (K.map N.subtype) := hR.to_le hKmap_le_R
  have hKmap_card : Nat.card (K.map N.subtype) = Nat.card K :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hKmap_cop : Nat.Coprime p (Nat.card (K.map N.subtype)) := by
    rw [hKmap_card]
    exact hKcop
  have hKmap_bot : K.map N.subtype = ⊥ := by
    by_contra hne
    rcases hKmap_p.card_eq_or_dvd with h1 | h1
    · exact hne (Subgroup.card_eq_one.mp h1)
    · exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hKmap_cop) h1
  exact (Subgroup.map_eq_bot_iff_of_injective K N.subtype_injective).mp hKmap_bot

theorem exists_pElement_not_mem_of_centralizer_not_le {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) {x y : X} (hx1 : x ≠ 1)
    (hxp : IsPGroup p (Subgroup.zpowers x)) (hxy : x * y = y * x)
    (hC : ¬ Subgroup.centralizer ({y} : Set X) ≤ N) :
    ∃ c : X, c * y = y * c ∧ IsPGroup p (Subgroup.zpowers c) ∧ c ∉ N := by
  classical
  by_contra hno
  push Not at hno
  let C : Subgroup X := Subgroup.centralizer ({y} : Set X)
  have hxC : x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hxy.symm
  have hall : ∀ c : ↥C, CFSG.IsPElement p c → (c : X) ∈ N := by
    intro c hc
    apply hno (c : X)
    · exact (Subgroup.mem_centralizer_iff.mp c.2 y (by simp)).symm
    · obtain ⟨k, hk⟩ := hc
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hk]
  let Px : Subgroup ↥C := (Subgroup.zpowers x).comap C.subtype
  have hPxp : IsPGroup p Px := hxp.comap_of_injective C.subtype C.subtype_injective
  have hxPx : (⟨x, hxC⟩ : ↥C) ∈ Px := by
    change x ∈ Subgroup.zpowers x
    exact Subgroup.mem_zpowers x
  obtain ⟨Q, hQle⟩ := hPxp.exists_le_sylow
  have hxQ : (⟨x, hxC⟩ : ↥C) ∈ Q := hQle hxPx
  let Qm : Subgroup X := (Q : Subgroup ↥C).map C.subtype
  have hQm_p : IsPGroup p Qm := Q.isPGroup'.map C.subtype
  have hxQm : x ∈ Qm := ⟨⟨x, hxC⟩, hxQ, rfl⟩
  have hQm_ne : Qm ≠ ⊥ := by
    intro hbot
    have : x ∈ (⊥ : Subgroup X) := by rw [← hbot]; exact hxQm
    exact hx1 (by simpa using this)
  have hQm_leN : Qm ≤ N := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_orderOf_eq_pow ⟨q, hq⟩
    have hkq : orderOf q = p ^ k := by
      change orderOf ((⟨q, hq⟩ : ↥Q) : ↥C) = p ^ k
      rw [Subgroup.orderOf_coe]
      exact hk
    exact hall q ⟨k, hkq⟩
  have hNormQm_le : Subgroup.normalizer (Qm : Set X) ≤ N :=
    hN.normalizer_le hQm_ne hQm_p hQm_leN
  let R : Subgroup ↥C := CFSG.pElementsSubgroup p ↥C
  have hQR : Q ≤ R := by
    intro q hq
    change q ∈ CFSG.pElementsSubgroup p ↥C
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_orderOf_eq_pow ⟨q, hq⟩
    have hkq : orderOf q = p ^ k := by
      change orderOf ((⟨q, hq⟩ : ↥Q) : ↥C) = p ^ k
      rw [Subgroup.orderOf_coe]
      exact hk
    exact Subgroup.subset_closure ⟨k, hkq⟩
  have hRchar : R.Characteristic :=
    CFSG.pElementsSubgroup_characteristic p ↥C
  haveI : R.Characteristic := hRchar
  haveI : R.Normal := Subgroup.normal_of_characteristic R
  haveI : Finite (Sylow p ↥R) := Sylow.finite_of_finiteIndex (Q.subtype hQR)
  have hfr := Sylow.normalizer_sup_eq_top (N := R) (P := Q.subtype hQR)
  have hmapQ : Subgroup.map R.subtype ↑(Q.subtype hQR) = (Q : Subgroup ↥C) := by
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQR]
  rw [hmapQ] at hfr
  have hRleN : R ≤ N.comap C.subtype := by
    change Subgroup.closure {c : ↥C | CFSG.IsPElement p c} ≤ N.comap C.subtype
    rw [Subgroup.closure_le]
    intro c hc
    exact hall c hc
  have hRmapN : R.map C.subtype ≤ N := by
    rintro z ⟨r, hr, rfl⟩
    exact hRleN hr
  have hNCmap : (Subgroup.normalizer (Q : Set ↥C)).map C.subtype ≤ N :=
    (Subgroup.le_normalizer_map (H := (Q : Subgroup ↥C)) C.subtype).trans hNormQm_le
  have htop : (⊤ : Subgroup ↥C).map C.subtype ≤ N := by
    rw [← hfr, Subgroup.map_sup]
    exact sup_le hNCmap hRmapN
  have htop_eq : (⊤ : Subgroup ↥C).map C.subtype = C := by
    ext z
    constructor
    · intro hz
      exact Subgroup.map_subtype_le (H := C) (K := ⊤) hz
    · intro hz
      exact ⟨⟨z, hz⟩, Subgroup.mem_top _, rfl⟩
  rw [htop_eq] at htop
  exact hC htop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
