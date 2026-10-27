module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.GGXInLE6Sylow

theorem mem_E_of_commute_mod_N
    {H : Type} [Group H] [Finite H] (N E : Subgroup H) [N.Normal] (hN : IsPGroup 2 N)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsc : ∀ g : H, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    {t : H} (ht : t ^ 3 ∈ N) (hcomm : ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ N) :
    ∃ e ∈ E, e⁻¹ * t ∈ N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup H := (N ⊔ E) ⊔ Subgroup.zpowers t
  have hNM : N ≤ M := le_trans le_sup_left le_sup_left
  have hEM : E ≤ M := le_trans le_sup_right le_sup_left
  have hTM : Subgroup.zpowers t ≤ M := le_sup_right
  have htM : t ∈ M := hTM (Subgroup.mem_zpowers t)
  let tM : M := ⟨t, htM⟩
  let N' : Subgroup M := N.subgroupOf M
  let E' : Subgroup M := E.subgroupOf M
  let T' : Subgroup M := (Subgroup.zpowers t).subgroupOf M
  haveI : N'.Normal := inferInstance
  have hN'2 : IsPGroup 2 N' := by
    change IsPGroup 2 (N.subgroupOf M)
    rw [← Subgroup.comap_subtype]
    exact hN.comap_subtype
  have hE3g : IsPGroup 3 E :=
    isPGroup_iff_pow_pow_eq_one.mpr fun e => ⟨1, by
      apply Subtype.ext
      simpa using hE3 (e : H) e.2⟩
  have hE'3 : IsPGroup 3 E' := by
    change IsPGroup 3 (E.subgroupOf M)
    rw [← Subgroup.comap_subtype]
    exact hE3g.comap_subtype
  let q : M →* M ⧸ N' := QuotientGroup.mk' N'
  have hsup : N' ⊔ E' ⊔ T' = ⊤ := by
    change N.subgroupOf M ⊔ E.subgroupOf M ⊔ (Subgroup.zpowers t).subgroupOf M = ⊤
    have h1 : ((N ⊔ E) ⊔ Subgroup.zpowers t).subgroupOf M
        = (N ⊔ E).subgroupOf M ⊔ (Subgroup.zpowers t).subgroupOf M :=
      Subgroup.subgroupOf_sup (sup_le hNM hEM) hTM
    have h2 : (N ⊔ E).subgroupOf M = N.subgroupOf M ⊔ E.subgroupOf M :=
      Subgroup.subgroupOf_sup hNM hEM
    have h3 : ((N ⊔ E) ⊔ Subgroup.zpowers t).subgroupOf M = ⊤ := by
      change M.subgroupOf M = ⊤
      rw [Subgroup.subgroupOf_self]
    rw [h1, h2] at h3
    exact h3
  have hmapN : Subgroup.map q N' = ⊥ := by
    rw [eq_bot_iff, Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_bot, ← MonoidHom.mem_ker]
    rwa [QuotientGroup.ker_mk']
  have hT'le : T' ≤ Subgroup.zpowers tM := by
    intro x hx
    change x ∈ (Subgroup.zpowers t).subgroupOf M at hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext hk⟩
  have hmap_le : Subgroup.map q T' ≤ Subgroup.zpowers (q tM) :=
    (Subgroup.map_mono (f := q) hT'le).trans (le_of_eq (MonoidHom.map_zpowers q tM))
  have hmap_top : Subgroup.map q (N' ⊔ E' ⊔ T') = ⊤ := by
    rw [hsup, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N')]
  have hmap_ge : ⊤ ≤ Subgroup.map q E' ⊔ Subgroup.zpowers (q tM) := by
    rw [← hmap_top]
    calc Subgroup.map q (N' ⊔ E' ⊔ T')
        = Subgroup.map q N' ⊔ Subgroup.map q E' ⊔ Subgroup.map q T' := by
          rw [Subgroup.map_sup, Subgroup.map_sup]
      _ ≤ ⊥ ⊔ Subgroup.map q E' ⊔ Subgroup.zpowers (q tM) := by
          apply sup_le_sup
          · apply sup_le_sup
            · rw [hmapN]
            · exact le_rfl
          · exact hmap_le
      _ = Subgroup.map q E' ⊔ Subgroup.zpowers (q tM) := by rw [bot_sup_eq]
  have hsup_map : Subgroup.map q E' ⊔ Subgroup.zpowers (q tM) = ⊤ := top_le_iff.mp hmap_ge
  let k : Set (M ⧸ N') := (Subgroup.map q E' : Set (M ⧸ N')) ∪ {q tM}
  have hk : Subgroup.closure k = Subgroup.map q E' ⊔ Subgroup.zpowers (q tM) := by
    rw [show k = (Subgroup.map q E' : Set (M ⧸ N')) ∪ {q tM} from rfl,
      Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  have htop : Subgroup.closure k = ⊤ := hk.trans hsup_map
  have hke : ∀ a ∈ Subgroup.map q E', ∀ b ∈ Subgroup.map q E', a * b = b * a := by
    intro a ha b hb
    obtain ⟨ea, hea, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨eb, heb, rfl⟩ := Subgroup.mem_map.mp hb
    have heac : (ea : M) * (eb : M) = (eb : M) * (ea : M) := by
      apply Subtype.ext
      show (ea : H) * (eb : H) = (eb : H) * (ea : H)
      exact hEc _ (Subgroup.mem_subgroupOf.mp hea) _ (Subgroup.mem_subgroupOf.mp heb)
    rw [← map_mul, ← map_mul, heac]
  have hkte : ∀ e : E', Commute (q e) (q tM) := by
    intro e
    have hmem : (e : M) * tM * (e : M)⁻¹ * tM⁻¹ ∈ N' := by
      change (e : M) * tM * (e : M)⁻¹ * tM⁻¹ ∈ N.subgroupOf M
      rw [Subgroup.mem_subgroupOf]
      simpa using hcomm (e : H) (Subgroup.mem_subgroupOf.mp e.2)
    have hq1 : q ((e : M) * tM * (e : M)⁻¹ * tM⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    have hq2 : q (e : M) * q tM * (q (e : M))⁻¹ * (q tM)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using hq1
    show q e * q tM = q tM * q e
    have hq3' : (q (e : M) * q tM) * (q (e : M))⁻¹ * (q tM)⁻¹ = 1 := hq2
    rw [mul_assoc, ← mul_inv_rev] at hq3'
    exact mul_inv_eq_one.mp hq3'
  have hkcomm : k.Pairwise Commute := by
    apply Set.Pairwise.of_forall₂
    intro a ha b hb
    have ha' : a ∈ Subgroup.map q E' ∨ a ∈ ({(q tM)} : Set (M ⧸ N')) := by
      change a ∈ (Subgroup.map q E' : Set (M ⧸ N')) ∪ ({q tM} : Set (M ⧸ N')) at ha
      exact Set.mem_or_mem_of_mem_union ha
    have hb' : b ∈ Subgroup.map q E' ∨ b ∈ ({(q tM)} : Set (M ⧸ N')) := by
      change b ∈ (Subgroup.map q E' : Set (M ⧸ N')) ∪ ({q tM} : Set (M ⧸ N')) at hb
      exact Set.mem_or_mem_of_mem_union hb
    rcases ha' with ha' | ha'
    · rcases hb' with hb' | hb'
      · exact (show Commute a b from hke a ha' b hb')
      · rw [Set.mem_singleton_iff] at hb'
        subst b
        obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha'
        exact hkte ⟨e, he⟩
    · rw [Set.mem_singleton_iff] at ha'
      subst a
      rcases hb' with hb' | hb'
      · obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hb'
        exact (hkte ⟨e, he⟩).symm
      · rw [Set.mem_singleton_iff] at hb'
        subst b
        exact Commute.refl _
  haveI hQcomm : IsMulCommutative (M ⧸ N') := by
    have hcommk : IsMulCommutative (Subgroup.closure k) :=
      Subgroup.isMulCommutative_closure hkcomm
    rw [htop] at hcommk
    exact IsMulCommutative.of_comm fun a b =>
      congrArg Subtype.val
        (mul_comm' (⟨a, trivial⟩ : (⊤ : Subgroup (M ⧸ N'))) ⟨b, trivial⟩)
  have hE'cube : ∀ e : E', (e : M) ^ 3 = 1 := by
    intro e
    apply Subtype.ext
    show ((e : M) : H) ^ 3 = 1
    exact hE3 _ (Subgroup.mem_subgroupOf.mp e.2)
  have htM3 : tM ^ 3 ∈ N' := by
    change tM ^ 3 ∈ N.subgroupOf M
    rw [Subgroup.mem_subgroupOf]
    simpa using ht
  have hq3 : (q tM) ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (tM ^ 3)).mpr htM3
  have hQcube : ∀ x : M ⧸ N', x ^ 3 = 1 := by
    intro x
    have hx : x ∈ Subgroup.closure k := by rw [htop]; trivial
    refine Subgroup.closure_induction (p := fun y _ => y ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      have hy' : y ∈ Subgroup.map q E' ∨ y ∈ ({(q tM)} : Set (M ⧸ N')) := by
        change y ∈ (Subgroup.map q E' : Set (M ⧸ N')) ∪ ({q tM} : Set (M ⧸ N')) at hy
        exact Set.mem_or_mem_of_mem_union hy
      rcases hy' with hy' | hy'
      · obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy'
        rw [← map_pow, hE'cube ⟨e, he⟩, map_one]
      · rw [Set.mem_singleton_iff] at hy'
        subst y
        exact hq3
    · exact one_pow 3
    · intro y z _ _ hy3 hz3
      have hc : Commute y z := mul_comm' y z
      rw [hc.mul_pow 3, hy3, hz3, one_mul]
    · intro y _ hy3
      rw [inv_pow, hy3, inv_one]
  have hQ3 : IsPGroup 3 (M ⧸ N') :=
    isPGroup_iff_pow_pow_eq_one.mpr fun x => ⟨1, by simpa using hQcube x⟩
  obtain ⟨S, hES⟩ := hE'3.exists_le_sylow
  let Ssub : Subgroup M := (S : Subgroup M)
  have hES' : E' ≤ Ssub := hES
  have hS3 : IsPGroup 3 Ssub := S.isPGroup'
  have hdisj : Disjoint Ssub N' :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) Ssub N' hS3 hN'2
  have hdisj_bot : Ssub ⊓ N' = ⊥ := disjoint_iff.mp hdisj
  obtain ⟨kQ, hkQ⟩ := hQ3.exists_card_eq
  have hcardM1 : Nat.card M = Nat.card (M ⧸ N') * Nat.card N' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  have hcardM2 : Nat.card Ssub * Ssub.index = Nat.card M := Ssub.card_mul_index
  have heq : Nat.card Ssub * Ssub.index = Nat.card (M ⧸ N') * Nat.card N' := by
    rw [hcardM2, hcardM1]
  have hcop1 : Nat.Coprime (Nat.card Ssub) (Nat.card N') :=
    IsPGroup.coprime_card_of_ne 3 2 (by norm_num) Ssub N' hS3 hN'2
  have hdvd1' : Nat.card Ssub ∣ Nat.card (M ⧸ N') * Nat.card N' := by
    rw [← heq]
    exact dvd_mul_right _ _
  have hdvd1 : Nat.card Ssub ∣ Nat.card (M ⧸ N') := (hcop1.dvd_mul_right).mp hdvd1'
  have hcop3 : Nat.Coprime 3 Ssub.index :=
    Nat.prime_three.coprime_iff_not_dvd.mpr S.not_dvd_index
  have hcop2 : Nat.Coprime (Nat.card (M ⧸ N')) Ssub.index := by
    rw [hkQ]
    exact hcop3.pow_left kQ
  have hdvd2' : Nat.card (M ⧸ N') ∣ Nat.card Ssub * Ssub.index := by
    rw [heq]
    exact dvd_mul_right _ _
  have hdvd2 : Nat.card (M ⧸ N') ∣ Nat.card Ssub := (hcop2.dvd_mul_right).mp hdvd2'
  have hcard_eq : Nat.card Ssub = Nat.card (M ⧸ N') := Nat.dvd_antisymm hdvd1 hdvd2
  let qS : Ssub →* (M ⧸ N') := q.comp Ssub.subtype
  have hqS_inj : Function.Injective qS := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_bot_iff.mp
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxN : (x : M) ∈ N' := by
      apply (QuotientGroup.eq_one_iff (x : M)).mp
      simpa [qS, q] using hx
    have hxinf : (x : M) ∈ Ssub ⊓ N' := ⟨x.2, hxN⟩
    rw [hdisj_bot] at hxinf
    exact Subtype.ext (by simpa using hxinf)
  have hbij : Function.Bijective qS :=
    hqS_inj.bijective_of_nat_card_le (by rw [hcard_eq])
  haveI hScomm : IsMulCommutative Ssub :=
    IsMulCommutative.of_comm fun a b => hqS_inj (by rw [map_mul, map_mul, mul_comm'])
  obtain ⟨y, hy⟩ := hbij.2 (q tM)
  have hyq : q (y : M) = q tM := hy
  have hyn : (y : M)⁻¹ * tM ∈ N' := by
    rw [← QuotientGroup.eq_one_iff]
    change q ((y : M)⁻¹ * tM) = 1
    rw [map_mul, map_inv, hyq, inv_mul_cancel]
  have hynH : (y : H)⁻¹ * t ∈ N := by
    simpa using Subgroup.mem_subgroupOf.mp hyn
  have hcommE : ∀ e ∈ E, (y : H) * e = e * (y : H) := by
    intro e he
    have heM : (⟨e, hEM he⟩ : M) ∈ E' := by
      change (⟨e, hEM he⟩ : M) ∈ E.subgroupOf M
      rw [Subgroup.mem_subgroupOf]
      exact he
    have heS : (⟨e, hEM he⟩ : M) ∈ Ssub := hES' heM
    have h := mul_comm' y (⟨⟨e, hEM he⟩, heS⟩ : Ssub)
    simpa using congrArg (fun z : Ssub => ((z : M) : H)) h
  have hy3M : (y : M) ^ 3 = 1 := by
    have hmemN : (y : M) ^ 3 ∈ N' := by
      rw [← QuotientGroup.eq_one_iff]
      change q ((y : M) ^ 3) = 1
      rw [map_pow, hQcube (q (y : M))]
    have hmemS : (y : M) ^ 3 ∈ Ssub := Ssub.pow_mem y.2 3
    have hx : (y : M) ^ 3 ∈ Ssub ⊓ N' := ⟨hmemS, hmemN⟩
    rw [hdisj_bot] at hx
    exact hx
  have hy3 : (y : H) ^ 3 = 1 := by
    have := congrArg (fun z : M => (z : H)) hy3M
    simpa using this
  exact ⟨(y : H), hsc (y : H) hcommE hy3, hynH⟩

end CFSG.StandardType.GGXInLE6Sylow

end
