module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Module
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.QSylowNor
public import CFSG.Mathlib.GroupTheory.SylowOfUniqueSubgroup
public import CFSG.CGT.PushingUpLit.SYMB.ProdCard

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open scoped Pointwise

structure SylowData {G : Type} [Group G] (b : G) (B₂ A : Subgroup G) (c : G) : Prop where
  isP : IsPGroup 3 (A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) : Subgroup G)
  max : ∀ P : Subgroup G, IsPGroup 3 P →
    A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) ≤ P →
      P = A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c)
  wc : ∀ g : G, (∀ x ∈ B₂, g * x * g⁻¹ ∈ A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c)) →
    ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂

private theorem card_sup_zpowers_le_nine {G : Type} [Group G] [Finite G] {b c : G}
    (hb : orderOf b = 3) (hbc : Commute b c) (hc : c ^ 3 = 1) :
    Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) ≤ 9 := by
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hbc i j).eq
  have hprod := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
    (C := Subgroup.zpowers b) (D := Subgroup.zpowers c) hcomm
  rw [Nat.card_zpowers, hb, Nat.card_zpowers] at hprod
  have hcle : orderOf c ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hc)
  have hpos : 1 ≤ Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers c : Subgroup G) := Nat.card_pos
  have h1 : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) *
      Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers c : Subgroup G) ≤ 9 := by
    rw [hprod]
    simpa using Nat.mul_le_mul_left 3 hcle
  calc Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G)
      = Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) * 1 :=
        (Nat.mul_one _).symm
    _ ≤ Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) *
          Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers c : Subgroup G) :=
        Nat.mul_le_mul_left _ hpos
    _ ≤ 9 := h1

theorem sylowData {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ A : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c) :
    SylowData b B₂ A c := by
  let Q : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers c
  let S : Subgroup G := A ⊔ Q
  have hcb : c * b = b * c :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hτc.c_mem)
  have hbc : Commute b c := hcb.symm
  have hc_nor_bOne : c ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    rw [show (bOne z : Subgroup G) =
        Subgroup.closure ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G) from
      CFSG.StandardType.GGFF.SettingCore.tor_eq_closure z]
    refine CFSG.StandardType.GGFF.mem_nor_of_closure
      (S := ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G)) ?_
    rintro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · rw [hτc.cyc₀]; exact Subgroup.subset_closure (by simp)
    · rw [hτc.cyc₁]; exact Subgroup.subset_closure (by simp)
    · rw [hτc.cyc₂]; exact Subgroup.subset_closure (by simp)
  have hQd : Q ≤ dGrp b z := by
    refine sup_le le_sup_left ?_
    have hc_d : c ∈ L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
      ⟨hτc.c_mem, hc_nor_bOne⟩
    exact (Subgroup.zpowers_le.mpr hc_d).trans le_sup_right
  have hQA : Q ≤ Subgroup.normalizer (A : Set G) :=
    fun g hg => CFSG.StandardType.GGFF.mem_nor_of_conj_mem (fun x hx => hA.nor g (hQd hg) x hx)
  have hb_norB₂ : b ∈ Subgroup.normalizer (B₂ : Set G) :=
    CFSG.StandardType.GGFF.mem_nor_of_conj_mem hB₂.b_nor
  have hc_norB₂ : c ∈ Subgroup.normalizer (B₂ : Set G) :=
    CFSG.StandardType.GGFF.mem_nor_of_conj_mem
      (fun x hx => hB₂.D_nor c ⟨hτc.c_mem, hc_nor_bOne⟩ x hx)
  have hQB₂ : Q ≤ Subgroup.normalizer (B₂ : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hb_norB₂) (Subgroup.zpowers_le.mpr hc_norB₂)
  have hQab : CFSG.Open.IsElemAbelian 3 Q := by
    have hb3 : b ^ 3 = 1 := by rw [← h.hypA.ord]; exact pow_orderOf_eq_one b
    exact CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers hb3)
      (CFSG.Open.isElemAbelian_zpowers hτc.c_cube)
      (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow hbc i j).eq)
  have hQisP : IsPGroup 3 Q := hQab.isPGroup
  have hSisP : IsPGroup 3 S := hA.isP.to_sup_of_normal_left' hQisP hQA
  have hS_norB₂ : S ≤ Subgroup.normalizer (B₂ : Set G) :=
    sup_le (hA.le_cen.trans (Subgroup.centralizer_le_normalizer (B₂ : Set G))) hQB₂
  have hB₂_le_S : B₂ ≤ S := hA.B₂_le.trans le_sup_left
  have hS_norA : S ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hQA
  have hQcard_le : Nat.card Q ≤ 9 := card_sup_zpowers_le_nine h.hypA.ord hbc hτc.c_cube
  have huniq : ∀ U : Subgroup G, U ≤ S → CFSG.Open.IsElemAbelian 3 U →
      Nat.card U = Nat.card B₂ → U = B₂ := by
    intro U hUS hUab hUcard
    set E : Subgroup G := U ⊓ A with hEdef
    let A' : Subgroup S := A.subgroupOf S
    have hA'norm : A'.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : A ≤ S)).mpr hS_norA
    let f : ↥U →* S ⧸ A' := (QuotientGroup.mk' A').comp (Subgroup.inclusion hUS)
    have hker : f.ker = A.subgroupOf U := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_inclusion_subgroupOf]
    have hker_card : Nat.card f.ker = Nat.card E := by
      rw [hker, hEdef]
      rw [← Subgroup.card_subtype U (A.subgroupOf U), Subgroup.subgroupOf_map_subtype, inf_comm]
    have hsurj : Function.Surjective
        (fun q : ↥Q => (QuotientGroup.mk' A') (Subgroup.inclusion (le_sup_right : Q ≤ S) q)) := by
      intro y
      obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective A' y
      have hs_mul : (s.1 : G) ∈ (A : Set G) * (Q : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA]
        exact s.2
      obtain ⟨a, ha, q, hq, haq⟩ := Set.mem_mul.mp hs_mul
      refine ⟨⟨q, hq⟩, ?_⟩
      have hs_eq : s = Subgroup.inclusion (le_sup_left : A ≤ S) ⟨a, ha⟩ *
          Subgroup.inclusion (le_sup_right : Q ≤ S) ⟨q, hq⟩ := by
        apply Subtype.ext
        simpa using haq.symm
      rw [hs_eq, map_mul]
      have h1 : (QuotientGroup.mk' A')
          (Subgroup.inclusion (le_sup_left : A ≤ S) ⟨a, ha⟩) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using ha
      rw [h1, one_mul]
    have hrange_le : Nat.card f.range ≤ 9 := by
      have h1 : Nat.card f.range ≤ Nat.card (S ⧸ A') := Subgroup.card_le_card_group f.range
      have h2 : Nat.card (S ⧸ A') ≤ Nat.card Q := Nat.card_le_card_of_surjective _ hsurj
      exact le_trans h1 (le_trans h2 hQcard_le)
    have hE_ge : 3 ^ 4 ≤ Nat.card E := by
      have hcard := Subgroup.card_ker_mul_card_range f
      rw [hker_card, hUcard, hB₂.card] at hcard
      have h729 : 729 ≤ Nat.card E * 9 := by
        calc 729 = Nat.card E * Nat.card f.range := by rw [hcard]; norm_num
          _ ≤ Nat.card E * 9 := Nat.mul_le_mul_left _ hrange_le
      have h81 : 81 ≤ Nat.card E := by omega
      have hpow : (3 : ℕ) ^ 4 = 81 := by norm_num
      rw [hpow]; exact h81
    have hEB₂ : E ≤ B₂ := by
      intro x hx
      rw [hEdef] at hx
      exact hA.omega x hx.2 (hUab.2 x hx.1)
    have hUA : U ≤ A := by
      intro u hu
      have hu_mul : u ∈ (A : Set G) * (Q : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA]
        exact hUS hu
      obtain ⟨a, ha, q, hq, haq⟩ := Set.mem_mul.mp hu_mul
      have hq_cen : q ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [hEdef] at hx
        have hxU : x ∈ U := hx.1
        have hxA : x ∈ A := hx.2
        have hux : u * x = x * u := by
          have := hUab.1.is_comm.comm ⟨u, hu⟩ ⟨x, hxU⟩
          exact congrArg Subtype.val this
        have hax : a * x = x * a := hA.comm a ha x hxA
        have hq_eq : q = a⁻¹ * u := by rw [← haq]; group
        rw [hq_eq]
        have haix : a⁻¹ * x = x * a⁻¹ := (show Commute a x from hax).inv_left.eq
        calc x * (a⁻¹ * u) = (x * a⁻¹) * u := by group
          _ = (a⁻¹ * x) * u := by rw [haix]
          _ = a⁻¹ * (x * u) := by group
          _ = a⁻¹ * (u * x) := by rw [hux]
          _ = (a⁻¹ * u) * x := by group
      have hE_le_cent : E ≤ Subgroup.centralizer ({q} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hq_cen x hx
      by_cases hq1 : q = 1
      · rw [hq1, mul_one] at haq
        rwa [← haq]
      · let K : Subgroup G := B₂ ⊓ Subgroup.centralizer ({q} : Set G)
        have hE_le : E ≤ K := fun x hx => ⟨hEB₂ hx, hE_le_cent hx⟩
        have hcard_le := card_centralizer_le h hB₂ hτc hq hq1
        have hEcard_le : Nat.card E ≤ Nat.card K := Subgroup.card_le_of_le hE_le
        have : (3 : ℕ) ^ 4 ≤ 3 ^ 3 := le_trans hE_ge (le_trans hEcard_le hcard_le)
        norm_num at this
    have hUB₂ : U ≤ B₂ := fun x hx => hA.omega x (hUA hx) (hUab.2 x hx)
    exact Subgroup.eq_of_le_of_card_ge hUB₂ (le_of_eq hUcard.symm)
  refine ⟨hSisP, ?_, ?_⟩
  · intro P hP hSP
    exact CFSG.SylowOfUniqueSubgroup.eq_of_isPGroup_of_le (p := 3) (S := S) (W := B₂)
      hSisP hB₂_le_S hB₂.abel huniq hS_norB₂
      (maximal_in_normalizer h hB₂ hA hτc) hP hSP
  · intro g hg x hx
    let U : Subgroup G := B₂.map (MulAut.conj g).toMonoidHom
    have hUS : U ≤ S := by
      rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      rw [Subgroup.mem_comap]
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] using hg y hy
    have hUab : CFSG.Open.IsElemAbelian 3 U := hB₂.abel.map (MulAut.conj g).toMonoidHom
    have hUcard : Nat.card U = Nat.card B₂ :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hUB₂ : U = B₂ := huniq U hUS hUab hUcard
    have hmem : (MulAut.conj g).toMonoidHom x ∈ U := Subgroup.mem_map_of_mem _ hx
    rw [hUB₂] at hmem
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] using hmem

end CFSG.StandardType.FF81.PropOne

end
