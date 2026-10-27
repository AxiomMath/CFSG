module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open scoped Pointwise

private lemma orderOf_quotient_mk'_eq_of_odd {G : Type*} [Group G]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup 2 ↥N) {x : G} (hx : Odd (orderOf x)) :
    orderOf (QuotientGroup.mk' N x) = orderOf x := by
  classical
  let K : Subgroup G := Subgroup.zpowers x
  have hcop : Nat.Coprime 2 (Nat.card ↥K) := by
    simpa [K, Nat.card_zpowers] using hx.coprime_two_left
  have hKp : IsPGroup (Nat.card ↥K) ↥K := IsPGroup.card
  have hdisj : Disjoint N K := IsPGroup.disjoint_of_coprime hN hKp hcop
  have hbot : N.subgroupOf K = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisj
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hker : (f.domRestrict K).ker = ⊥ := by
    rw [MonoidHom.ker_restrict, QuotientGroup.ker_mk']
    exact hbot
  have hinj : Function.Injective (f.domRestrict K) :=
    (MonoidHom.ker_eq_bot_iff (f.domRestrict K)).mp hker
  have hcard : Nat.card ↥(Subgroup.map (f.domRestrict K) ⊤) =
      Nat.card ↥(⊤ : Subgroup ↥K) :=
    Subgroup.card_map_of_injective hinj
  have hmap : Subgroup.map (f.domRestrict K) ⊤ = Subgroup.zpowers (f x) := by
    rw [Subgroup.map_top, MonoidHom.domRestrict_range K f, MonoidHom.map_zpowers]
  calc
    orderOf (f x) = Nat.card ↥(Subgroup.zpowers (f x)) := (Nat.card_zpowers (f x)).symm
    _ = Nat.card ↥(Subgroup.map (f.domRestrict K) ⊤) := by rw [hmap]
    _ = Nat.card ↥(⊤ : Subgroup ↥K) := hcard
    _ = Nat.card ↥K := Subgroup.card_top
    _ = orderOf x := Nat.card_zpowers x


theorem zpowers_mul_eq_mul_zpowers {G : Type*} [Group G] [Finite G] {H S T L : Subgroup G}
    (hSH : S ≤ H) (hS2 : IsPGroup 2 ↥S)
    (hSmax : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 ↥P → S ≤ P → P = S)
    (hTH : T ≤ Subgroup.normalizer (H : Set G)) (hT2 : IsPGroup 2 ↥T) (hST : S ≤ T)
    (hTL : T ≤ L)
    (hcyc : ∀ B : Subgroup G, B ≤ H ⊓ L → Odd (Nat.card ↥B) → IsCyclic ↥B)
    {a : G} (haH : a ∈ H) (haL : a ∈ L) (haS : a ∈ Subgroup.normalizer (S : Set G))
    (ha : Odd (orderOf a)) :
    (Subgroup.zpowers a : Set G) * (T : Set G) = (T : Set G) * (Subgroup.zpowers a : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (S : Set G)
  let P : Subgroup G := N ⊓ H ⊓ L
  have hSeq : T ⊓ H = S := by
    refine hSmax (T ⊓ H) inf_le_right (hT2.to_le inf_le_left) (le_inf hST hSH)
  have hT_normS : T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    have h1 : t ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer (H := T) ht
    have h2 : t ∈ Subgroup.normalizer (H : Set G) := hTH ht
    have h3 : t ∈ Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G) :=
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := H)) ⟨h1, h2⟩
    simpa [hSeq] using h3
  have hT_normP : T ≤ Subgroup.normalizer (P : Set G) := by
    intro t ht
    have htN : t ∈ N := hT_normS ht
    have h1 : t ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer (H := N) htN
    have h2 : t ∈ Subgroup.normalizer (H : Set G) := hTH ht
    have h3 : t ∈ Subgroup.normalizer ((N ⊓ H : Subgroup G) : Set G) :=
      (Subgroup.inf_normalizer_le_normalizer_inf (H := N) (K := H)) ⟨h1, h2⟩
    have htL : t ∈ L := hTL ht
    have h4 : t ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer (H := L) htL
    exact (Subgroup.inf_normalizer_le_normalizer_inf (H := N ⊓ H) (K := L)) ⟨h3, h4⟩
  have hS_le_P : S ≤ P := by
    intro x hx
    exact ⟨⟨Subgroup.le_normalizer (H := S) hx, hSH hx⟩, hST.trans hTL hx⟩
  have hP_le_N : P ≤ N := inf_le_left.trans inf_le_left
  have hP_le_H : P ≤ H := inf_le_left.trans inf_le_right
  have hP_le_L : P ≤ L := inf_le_right
  have hS_normalP : (S.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_P).mpr hP_le_N
  have haP : a ∈ P := ⟨⟨haS, haH⟩, haL⟩
  have hS2P : IsPGroup 2 ↥(S.subgroupOf P) := hS2.comap_subtype
  obtain ⟨Q, hQle⟩ := hS2P.exists_le_sylow
  have hmapS : (S.subgroupOf P).map P.subtype = S :=
    Subgroup.map_subgroupOf_eq_of_le hS_le_P
  have hQleH : (Q : Subgroup ↥P).map P.subtype ≤ H :=
    (Subgroup.map_subtype_le (Q : Subgroup ↥P)).trans hP_le_H
  have hQ2 : IsPGroup 2 ↥((Q : Subgroup ↥P).map P.subtype) :=
    Q.isPGroup'.map P.subtype
  have hSQ : S ≤ (Q : Subgroup ↥P).map P.subtype := by
    rw [← hmapS]
    exact Subgroup.map_mono (f := P.subtype) hQle
  have hQmap : (Q : Subgroup ↥P).map P.subtype = S :=
    hSmax _ hQleH hQ2 hSQ
  have hQeq : (Q : Subgroup ↥P) = S.subgroupOf P := by
    exact Subgroup.map_injective P.subtype_injective (by rw [hQmap, hmapS])
  have hcop : Nat.Coprime (Nat.card ↥(S.subgroupOf P)) (S.subgroupOf P).index := by
    have h := Sylow.card_coprime_index Q
    rwa [hQeq] at h
  haveI : (S.subgroupOf P).Normal := hS_normalP
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := S.subgroupOf P) hcop
  have hC_comm : Subgroup.IsComplement' C (S.subgroupOf P) :=
    Subgroup.isComplement'_comm.mpr hC
  have hoddC : Odd (Nat.card ↥C) := by
    rw [← hC_comm.index_eq_card]
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ?_)
    have h := Sylow.not_dvd_index Q
    rwa [hQeq] at h
  have hB_le : C.map P.subtype ≤ H ⊓ L :=
    le_inf ((Subgroup.map_subtype_le C).trans hP_le_H)
      ((Subgroup.map_subtype_le C).trans hP_le_L)
  have hBodd : Odd (Nat.card ↥(C.map P.subtype)) := by
    rw [Subgroup.card_subtype P C]
    exact hoddC
  have hBcyc : IsCyclic ↥(C.map P.subtype) := hcyc _ hB_le hBodd
  have hCcyc : IsCyclic ↥C :=
    (Subgroup.equivMapOfInjective C P.subtype P.subtype_injective).isCyclic.mpr hBcyc
  have hRcyc : IsCyclic ((↥P) ⧸ (S.subgroupOf P)) :=
    hC_comm.QuotientMulEquiv.isCyclic.mpr hCcyc
  let X : Subgroup G := Subgroup.zpowers a
  let Y : Subgroup G := X ⊔ S
  have hX_le_normS : X ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.zpowers_le]
    exact haS
  have hYmul : (Y : Set G) = (X : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X S hX_le_normS
  have hT_normY : T ≤ Subgroup.normalizer (Y : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hbP : t * a * t⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hT_normP ht) a).mp haP
    let b : G := t * a * t⁻¹
    let xa : ↥P := ⟨a, haP⟩
    let xb : ↥P := ⟨b, hbP⟩
    have hsem : SemiconjBy t a b := by
      dsimp [b, SemiconjBy]
      group
    have hxa_odd : Odd (orderOf xa) := by
      rw [show xa = ⟨a, haP⟩ from rfl, Subgroup.orderOf_mk]
      exact ha
    have hxb_odd : Odd (orderOf xb) := by
      rw [show xb = ⟨b, hbP⟩ from rfl, Subgroup.orderOf_mk]
      simpa [hsem.orderOf_eq t] using ha
    have hord_a : orderOf (QuotientGroup.mk' (S.subgroupOf P) xa) = orderOf xa :=
      orderOf_quotient_mk'_eq_of_odd hS2P hxa_odd
    have hord_b : orderOf (QuotientGroup.mk' (S.subgroupOf P) xb) = orderOf xb :=
      orderOf_quotient_mk'_eq_of_odd hS2P hxb_odd
    have hord_eq : orderOf (QuotientGroup.mk' (S.subgroupOf P) xa) =
        orderOf (QuotientGroup.mk' (S.subgroupOf P) xb) := by
      rw [hord_a, hord_b, show orderOf xa = orderOf a from Subgroup.orderOf_mk a haP,
        show orderOf xb = orderOf b from Subgroup.orderOf_mk b hbP]
      exact hsem.orderOf_eq t
    haveI : IsCyclic ((↥P) ⧸ (S.subgroupOf P)) := hRcyc
    have hsub_eq : Subgroup.zpowers (QuotientGroup.mk' (S.subgroupOf P) xa) =
        Subgroup.zpowers (QuotientGroup.mk' (S.subgroupOf P) xb) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hord_eq]
    have hb_image : QuotientGroup.mk' (S.subgroupOf P) xb ∈
        Subgroup.zpowers (QuotientGroup.mk' (S.subgroupOf P) xa) := by
      rw [hsub_eq]
      exact Subgroup.mem_zpowers _
    have hmem_comap : xb ∈ Subgroup.comap (QuotientGroup.mk' (S.subgroupOf P))
        (Subgroup.map (QuotientGroup.mk' (S.subgroupOf P)) (Subgroup.zpowers xa)) := by
      rw [Subgroup.mem_comap, MonoidHom.map_zpowers]
      exact hb_image
    have hmem_sup : xb ∈ (S.subgroupOf P) ⊔ Subgroup.zpowers xa := by
      rw [← QuotientGroup.comap_map_mk' (N := S.subgroupOf P)
        (H := Subgroup.zpowers xa)]
      exact hmem_comap
    have hsup_eq : ((S.subgroupOf P) ⊔ Subgroup.zpowers xa).map P.subtype = Y := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hS_le_P,
        MonoidHom.map_zpowers]
      dsimp [Y, X]
      rw [show (xa : G) = a from rfl, sup_comm]
    have hbY : b ∈ Y := by
      have hb_map : P.subtype xb ∈ ((S.subgroupOf P) ⊔ Subgroup.zpowers xa).map P.subtype :=
        Subgroup.mem_map_of_mem P.subtype hmem_sup
      rwa [hsup_eq] at hb_map
    have hle : Y.map (MulAut.conj t) ≤ Y := by
      rw [show Y = Subgroup.zpowers a ⊔ S from rfl, Subgroup.map_sup,
        MonoidHom.map_zpowers]
      have hSmap : S.map (MulAut.conj t : G →* G) = S :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hT_normS ht)
      rw [hSmap]
      refine sup_le ?_ le_sup_right
      change Subgroup.zpowers (t * a * t⁻¹) ≤ Y
      exact Subgroup.zpowers_le_of_mem hbY
    have hcard : Nat.card ↥(Y.map (MulAut.conj t : G →* G)) = Nat.card ↥Y :=
      Subgroup.card_map_of_injective (f := (MulAut.conj t : G →* G))
        (MulAut.conj t).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hSTmul : (S : Set G) * (T : Set G) = (T : Set G) := by
    ext x
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact T.mul_mem (hST hs) ht
    · intro hx
      exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  have hTSmul : (T : Set G) * (S : Set G) = (T : Set G) := by
    ext x
    constructor
    · rintro ⟨t, ht, s, hs, rfl⟩
      exact T.mul_mem ht (hST hs)
    · intro hx
      exact ⟨x, hx, 1, S.one_mem, mul_one x⟩
  have hTY : (T : Set G) * (Y : Set G) = (Y : Set G) * (T : Set G) :=
    Subgroup.set_mul_normalizer_comm (T : Set G) Y hT_normY
  have hXSmul : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G) :=
    Subgroup.set_mul_normalizer_comm (X : Set G) S hX_le_normS
  calc
    (X : Set G) * (T : Set G)
        = (X : Set G) * ((S : Set G) * (T : Set G)) := by rw [hSTmul]
    _ = ((X : Set G) * (S : Set G)) * (T : Set G) := by rw [mul_assoc]
    _ = (Y : Set G) * (T : Set G) := by rw [← hYmul]
    _ = (T : Set G) * (Y : Set G) := hTY.symm
    _ = (T : Set G) * ((X : Set G) * (S : Set G)) := by rw [hYmul]
    _ = (T : Set G) * ((S : Set G) * (X : Set G)) := by rw [hXSmul]
    _ = ((T : Set G) * (S : Set G)) * (X : Set G) := by rw [← mul_assoc]
    _ = (T : Set G) * (X : Set G) := by rw [hTSmul]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
