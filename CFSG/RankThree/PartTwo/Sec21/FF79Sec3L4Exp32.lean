module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Exp3
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs

import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Lift2
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Syl
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem exists_sylowOf_three_ge {H Z : Subgroup G} (hZH : Z ≤ H) (hZ : IsPGroup 3 Z) :
    ∃ R : Subgroup G, IsSylowOf 3 R H ∧ Z ≤ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ' : IsPGroup 3 (Z.subgroupOf H) := hZ.of_equiv (Subgroup.subgroupOfEquivOfLe hZH).symm
  obtain ⟨P, hP⟩ := hZ'.exists_le_sylow
  refine ⟨(P : Subgroup H).map H.subtype, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact P.isPGroup'.map H.subtype
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (P.not_dvd_index)
  · intro x hx
    exact ⟨⟨x, hZH hx⟩, hP (show (⟨x, hZH hx⟩ : ↥H) ∈ Z.subgroupOf H from hx), rfl⟩

theorem exp3_lift {b : G} (hb : orderOf b = 3) {C : Subgroup G} (hbC : b ∈ Nor C) (hbnot : b ∉ C)
    (Q : Subgroup ↥C) [Q.Normal] (hQ : Nat.Coprime 3 (Nat.card Q))
    (S : Subgroup (↥C ⧸ Q)) (hS3 : IsPGroup 3 S)
    (hinv : ∀ x : ↥C, (QuotientGroup.mk x : ↥C ⧸ Q) ∈ S →
      (QuotientGroup.mk (conjAut C b hbC x) : ↥C ⧸ Q) ∈ S) :
    ∃ R : Subgroup G, IsPGroup 3 R ∧ b ∈ R ∧ R ≤ C ⊔ Subgroup.zpowers b ∧
      ∀ s ∈ S, ∃ x : ↥C, (x : G) ∈ R ∧ (QuotientGroup.mk x : ↥C ⧸ Q) = s := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.zpowers b with hZ
  set S1 : Subgroup ↥C := S.comap (QuotientGroup.mk' Q) with hS1
  set St : Subgroup G := S1.map C.subtype with hSt
  have hStC : St ≤ C := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hStmem : ∀ x : ↥C, (x : G) ∈ St ↔ (QuotientGroup.mk x : ↥C ⧸ Q) ∈ S := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hbSt : ∀ y ∈ St, b * y * b⁻¹ ∈ St := by
    intro y hy
    have hyC := hStC hy
    have := hinv ⟨y, hyC⟩ ((hStmem ⟨y, hyC⟩).mp hy)
    exact (hStmem (conjAut C b hbC ⟨y, hyC⟩)).mpr this
  have hZSt : Z ≤ Subgroup.normalizer (St : Set G) :=
    (Subgroup.zpowers_le).mpr (L41.mem_nor_of_forall hbSt)
  have hbnotSt : b ∉ St := fun h => hbnot (hStC h)
  have hcZ : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hb]
  have hZ3 : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hcZ]; norm_num)
  set M : Subgroup G := St ⊔ Z with hM
  have hMcard : Nat.card M = Nat.card St * 3 := by
    rw [hM, CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZSt
      (sec34S_inf_zpowers hb hbnotSt), hcZ]
  obtain ⟨R, hRsyl, hZR⟩ := exists_sylowOf_three_ge (le_sup_right : Z ≤ M) hZ3
  have hR3 : IsPGroup 3 R := hRsyl.2.1
  have hbR : b ∈ R := hZR (Subgroup.mem_zpowers b)
  have hRN : R ≤ C ⊔ Z := hRsyl.1.trans (sup_le_sup hStC le_rfl)
  refine ⟨R, hR3, hbR, hRN, ?_⟩
  have hPC : R ⊓ St ≤ C := inf_le_right.trans hStC
  let f : ↥(R ⊓ St) →* (↥C ⧸ Q) := (QuotientGroup.mk' Q).comp (Subgroup.inclusion hPC)
  have hQh : Nat.Coprime 3 (Nat.card (Q.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]; exact hQ
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Subgroup.inclusion hPC x ∈ Q := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : ((x : G)) ∈ Q.map C.subtype := ⟨Subgroup.inclusion hPC x, h1, rfl⟩
    exact Subtype.ext (eq_one_of_pgroup_of_coprime hR3 hQh x.2.1 h2)
  have hfS : f.range ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact (hStmem (Subgroup.inclusion hPC x)).mp x.2.2
  have hcardP : Nat.card f.range = Nat.card ↥(R ⊓ St) :=
    Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm
  have hS1card : Nat.card S1 = Nat.card St :=
    (Subgroup.card_map_of_injective C.subtype_injective).symm
  have hsurj : Function.Surjective
      (((QuotientGroup.mk' Q).comp S1.subtype).codRestrict S (fun c => c.2)) := by
    rintro ⟨t, ht⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
    exact ⟨⟨c, ht⟩, rfl⟩
  have hSdvd : Nat.card S ∣ Nat.card St := hS1card ▸ Subgroup.card_dvd_of_surjective hsurj
  obtain ⟨k, hk⟩ := hS3.exists_card_eq
  have hkle : k ≤ (Nat.card St).factorization 3 := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp ?_
    rwa [hk] at hSdvd
  have hRcard := L41.isSylowOf_card_p hRsyl
  have hvM : (Nat.card M).factorization 3 = (Nat.card St).factorization 3 + 1 := by
    rw [hMcard, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply]
    simp [Nat.Prime.factorization Nat.prime_three]
  have hrel1 : St.relIndex R * Nat.card ↥(St ⊓ R) = Nat.card R :=
    Subgroup.relIndex_mul_card St R
  have hrel2 : St.relIndex M * Nat.card ↥(St ⊓ M) = Nat.card M :=
    Subgroup.relIndex_mul_card St M
  have hStM : St ⊓ M = St := inf_eq_left.mpr le_sup_left
  have hrelM : St.relIndex M = 3 := by
    rw [hStM, hMcard] at hrel2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hrel2, mul_comm])
  have hrelR : St.relIndex R ≤ 3 := by
    rw [← hrelM]
    exact Subgroup.relIndex_le_of_le_right hRsyl.1 (by rw [hrelM]; norm_num)
  have hinf : St ⊓ R = R ⊓ St := inf_comm _ _
  rw [hinf] at hrel1
  have hSle : Nat.card S ≤ Nat.card ↥(R ⊓ St) := by
    have h1 : 3 ^ ((Nat.card St).factorization 3 + 1) ≤ 3 * Nat.card ↥(R ⊓ St) := by
      rw [← hvM, ← hRcard, ← hrel1]
      exact Nat.mul_le_mul_right _ hrelR
    have h2 : 3 ^ k ≤ 3 ^ (Nat.card St).factorization 3 :=
      Nat.pow_le_pow_right (by norm_num) hkle
    rw [hk]
    rw [pow_succ] at h1
    nlinarith
  have hrange : f.range = S :=
    Subgroup.eq_of_le_of_card_ge hfS (by rw [hcardP]; exact hSle)
  intro s hs
  rw [← hrange] at hs
  obtain ⟨x, hx⟩ := hs
  exact ⟨Subgroup.inclusion hPC x, x.2.1, hx⟩

variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem sec34_ap_exp3 (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D)
    (hU : FF79Sec34UFacts b a J A) :
    ∀ S : Subgroup (CQ (U34 b a J A)), IsMulCommutative S → IsPGroup 3 S →
      (∀ s ∈ S, cqβ (U34 b a J A) b hU.b_nor s ∈ S) →
      ∀ s ∈ S, cqβ (U34 b a J A) b hU.b_nor (cqβ (U34 b a J A) b hU.b_nor s * s⁻¹) =
        cqβ (U34 b a J A) b hU.b_nor s * s⁻¹ → s ^ 3 = 1 := by
  intro S _ hS3 hSinv s hsS hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (pPrimeCore 3 ↥(CenS (U34 b a J A))).Normal := pPrimeCore_normal
  have hb3 : orderOf b = 3 := h.hyp.ord
  have hbC : b ∈ Nor (CenS (U34 b a J A)) := nor_cenS_of_nor hU.b_nor
  have hbnot : b ∉ CenS (U34 b a J A) := sec34S_b_not_mem hU
  obtain ⟨As, hAs⟩ := h.star
  have hAsyl := sec34_As_syl hs h hU hAs
  obtain ⟨-, hAsyl', hcomm, hbAs, -, -, -, hlast⟩ := hAs
  have hmk : ∀ x : ↥(CenS (U34 b a J A)),
      (QuotientGroup.mk (conjAut (CenS (U34 b a J A)) b hbC x) : CQ (U34 b a J A)) =
        cqβ (U34 b a J A) b hU.b_nor (QuotientGroup.mk x) := fun x =>
    (mk_conjAut_eq hU.b_nor x).symm
  obtain ⟨R, hR3, hbR, hRN, hlift⟩ := exp3_lift hb3 hbC hbnot
    (pPrimeCore 3 ↥(CenS (U34 b a J A))) pPrimeCore_coprime_card S hS3
    (fun x hx => by rw [hmk]; exact hSinv _ hx)
  obtain ⟨sh, hshR, hshs⟩ := hlift s hsS
  set β' := conjAut (CenS (U34 b a J A)) b hbC with hβ'
  set th : ↥(CenS (U34 b a J A)) := β' sh * sh⁻¹ with hth
  set u : ↥(CenS (U34 b a J A)) := β' th * th⁻¹ with hu
  have hu1 : (QuotientGroup.mk u : CQ (U34 b a J A)) = 1 := by
    have h1 : (QuotientGroup.mk th : CQ (U34 b a J A)) =
        cqβ (U34 b a J A) b hU.b_nor s * s⁻¹ := by
      rw [hth, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, hshs]
    rw [hu, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, h1]
    exact mul_inv_eq_one.mpr hfix
  have huQ : u ∈ pPrimeCore 3 ↥(CenS (U34 b a J A)) := (QuotientGroup.eq_one_iff u).mp hu1
  have hQh : Nat.Coprime 3
      (Nat.card ((pPrimeCore 3 ↥(CenS (U34 b a J A))).map (CenS (U34 b a J A)).subtype)) := by
    rw [Subgroup.card_map_of_injective (CenS (U34 b a J A)).subtype_injective]
    exact pPrimeCore_coprime_card
  set sg : G := (sh : G) with hsg
  have hthG : (th : G) = b * sg * b⁻¹ * sg⁻¹ := rfl
  have huG : (u : G) = b * (b * sg * b⁻¹ * sg⁻¹) * b⁻¹ * (b * sg * b⁻¹ * sg⁻¹)⁻¹ := rfl
  have hRu : (u : G) ∈ R := by
    rw [huG]
    refine R.mul_mem (R.mul_mem (R.mul_mem hbR ?_) (R.inv_mem hbR)) (R.inv_mem ?_) <;>
    exact R.mul_mem (R.mul_mem (R.mul_mem hbR hshR) (R.inv_mem hbR)) (R.inv_mem hshR)
  have hu1G : (u : G) = 1 :=
    eq_one_of_pgroup_of_coprime hR3 hQh hRu ⟨u, huQ, rfl⟩
  rw [huG] at hu1G
  have hu' : b * (b * sg * b⁻¹ * sg⁻¹) * b⁻¹ = b * sg * b⁻¹ * sg⁻¹ := mul_inv_eq_one.mp hu1G
  obtain ⟨c, hc, hcR, hcb⟩ := sylow_conj_core hb3 hbC hbnot hAsyl hbAs hR3 hbR hRN
  have hx : c * sg * c⁻¹ ∈ As := hcR sg ⟨hshR, sh.2⟩
  have hw := hcb
  have hwb : (c * b * c⁻¹ * b⁻¹) * b = c * b * c⁻¹ := by group
  have hcomm' := exp3_comm hcomm hbAs hx hw (by
    rw [hwb]
    calc c * b * c⁻¹ * (c * b * c⁻¹ * (c * sg * c⁻¹) * (c * b * c⁻¹)⁻¹ * (c * sg * c⁻¹)⁻¹) *
          (c * b * c⁻¹)⁻¹ = c * (b * (b * sg * b⁻¹ * sg⁻¹) * b⁻¹) * c⁻¹ := by group
      _ = c * (b * sg * b⁻¹ * sg⁻¹) * c⁻¹ := by rw [hu']
      _ = c * b * c⁻¹ * (c * sg * c⁻¹) * (c * b * c⁻¹)⁻¹ * (c * sg * c⁻¹)⁻¹ := by group)
  have hxA : c * sg * c⁻¹ ∈ A := (hlast _ hx).mp hcomm'
  haveI := h.elemA.1
  have hx3 : (c * sg * c⁻¹) ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian
    (A := A) _ hxA
  have hsg3 : sg ^ 3 = 1 := by
    have : (c * sg * c⁻¹) ^ 3 = c * sg ^ 3 * c⁻¹ := conj_pow
    rw [this] at hx3
    have h2 : sg ^ 3 = c⁻¹ * (c * sg ^ 3 * c⁻¹) * c := by group
    rw [h2, hx3]; group
  have : sh ^ 3 = 1 := Subtype.ext hsg3
  rw [← hshs, ← QuotientGroup.mk_pow, this]
  rfl

end CFSG.RankThree.PartTwo.Sec21.FF79
