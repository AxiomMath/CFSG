module

public import CFSG.Monster.GMS.Fi23LocalSlice
public import CFSG.Monster.GMS.S37Four

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Blueprint.Fischer (LocalClass)
open CFSG.Monster.GMS.Fi23Local

namespace CommonNbr

section Fi22

open CFSG.Sporadic.Fi22 (D J a a_mem_D a_sq conjPt mem_D_iff orb_size orderOf_a_conjPt_sub
  orderOf_of_mem_D subRoot_lt_orb)
open CFSG.Sporadic.Fi22.Native (subRoot)

theorem fi22_exists_commuting_pair :
    ∃ p q : D, p ≠ q ∧ (p : J) * (q : J) = (q : J) * p := by
  have hq : conjPt subRoot ∈ D :=
    mem_D_iff.2 ⟨subRoot, by rw [← orb_size]; exact subRoot_lt_orb, rfl⟩
  have haa : (a : J) * a = 1 := by rw [← pow_two]; exact a_sq
  have hqq : conjPt subRoot * conjPt subRoot = 1 := by
    rw [← pow_two, ← orderOf_of_mem_D hq]; exact pow_orderOf_eq_one _
  have hsq : (a * conjPt subRoot) * (a * conjPt subRoot) = 1 := by
    rw [← pow_two, ← orderOf_a_conjPt_sub]; exact pow_orderOf_eq_one _
  have hcomm : a * conjPt subRoot = conjPt subRoot * a :=
    mul_comm_of_mul_self_eq_one (G := J) haa hqq hsq
  refine ⟨⟨a, a_mem_D⟩, ⟨_, hq⟩, ?_, ?_⟩
  · intro h
    have h' : a = conjPt subRoot := Subtype.mk.inj h
    have h2 := orderOf_a_conjPt_sub
    rw [← h', ← pow_two, a_sq, orderOf_one] at h2
    omega
  · exact hcomm

end Fi22

section Star

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_commuting_pair_star
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) {b x : G} (hb : IsConj a b) (hx : IsConj a x)
    (hbx : orderOf (b * x) = 3) {t : G} (ht : t ∈ twoANbr a b ∩ twoANbr a x)
    {φ : Subgroup.centralizer ({t} : Set G) →* B} (hφ : IsBabyCover t φ) :
    ∃ f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) t,
      ∃ f' ∈ LocalClass (twoANbr a b ∩ twoANbr a x) t,
        coverMap φ f ≠ coverMap φ f' ∧ f * f' = f' * f := by
  obtain ⟨hr, hs, hrs⟩ := babyData I hG hb hx hbx ht hφ
  obtain ⟨⟨χ, hχc, -⟩, -⟩ := hS _ _ hr hs hrs
  have hbij := babyStar_bijOn I hG hb hx hbx ht hφ
  obtain ⟨p, q, hpq, hpqc⟩ := fi22_exists_commuting_pair
  obtain ⟨f, hf, hfe⟩ := hbij.surjOn (χ.symm p).2
  obtain ⟨f', hf', hf'e⟩ := hbij.surjOn (χ.symm q).2
  refine ⟨f, hf, f', hf', ?_, ?_⟩
  · rw [hfe, hf'e]
    intro h
    exact hpq (χ.symm.injective (Subtype.ext h))
  · rw [commute_iff_coverMap I hG hb hx hbx ht hφ hf hf', hfe, hf'e]
    apply (hχc (χ.symm p) (χ.symm q)).mpr
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hpqc

end Star

section TwoB

variable {G : Type} [Group G] {a z₀ b' z' u' t : G}

theorem isTwoACls_of_mem_twoANbr (htA : IsConj a t) (hB : TwoClasses t z₀ b' z' u') {f : G}
    (hf : f ∈ twoANbr a t) : IsTwoACls t b' f := by
  obtain ⟨-, g, hg, e⟩ := hB.exists_conj_of_mem_twoANbr_self (by rwa [← twoANbr_congr htA])
  exact ⟨g, hg, Or.inl e⟩

end TwoB

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem isConj_twoB_of_commuting_star
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {b x : G} (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {t : G}
    (ht : t ∈ twoANbr a b ∩ twoANbr a x) {φ : Subgroup.centralizer ({t} : Set G) →* B}
    (hφ : IsBabyCover t φ) {f f' : G} (hf : f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) t)
    (hf' : f' ∈ LocalClass (twoANbr a b ∩ twoANbr a x) t)
    (hne : coverMap φ f ≠ coverMap φ f') (hc : f * f' = f' * f) :
    IsConj z₀ (t * (f * f')) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have htA : IsConj a t := ht.1.1
  obtain ⟨b', z', u', hB⟩ := h.exists_of_isConj htA
  have hIV := I.tableIV t b' z' u' (isTwoBabyCentralizer_of_isConj I.sls hG htA) hB.tableV
  have hfC := mem_centralizer_of_mem_localClass hf
  have hf'C := mem_centralizer_of_mem_localClass hf'
  have htt : t * t = 1 := mul_self_eq_one_of_isConj_a h htA
  have hff : f * f = 1 := mul_self_eq_one_of_isConj_a h hf.1.1.1
  have hff' : f' * f' = 1 := mul_self_eq_one_of_isConj_a h hf'.1.1.1
  have hne' : f ≠ f' ∧ f ≠ t * f' := by
    refine ⟨fun e => hne (by rw [e]), fun e => hne ?_⟩
    exact ((hφ.coverMap_eq_iff hf'C hfC).mpr (Or.inr e)).symm
  have hfC' : f * f' ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mul_mem _ hfC hf'C
  have hsq : (f * f') * (f * f') = 1 := by
    calc (f * f') * (f * f') = f * (f' * f) * f' := by group
      _ = f * (f * f') * f' := by rw [hc]
      _ = (f * f) * (f' * f') := by group
      _ = 1 := by rw [hff, hff', one_mul]
  have hcancel : f = f * f' * f' := by rw [mul_assoc, hff', mul_one]
  have hne1 : f * f' ≠ 1 := fun e => hne'.1 (by rw [hcancel, e, one_mul])
  have hnet : f * f' ≠ t := fun e => hne'.2 (by rw [hcancel, e])
  have hA : IsConj a (f * f') :=
    commute_mem_twoANbr I hG hb hx hbx hf'.1 hf.1 hne'.1 hc
  have hnotb : ¬ IsTwoACls t b' (f * f') :=
    hIV f hfC f' hf'C
      (isTwoACls_of_mem_twoANbr htA hB (mem_twoANbr_of_mem_localClass I hG hb hx hbx ht hf))
      (isTwoACls_of_mem_twoANbr htA hB (mem_twoANbr_of_mem_localClass I hG hb hx hbx ht hf'))
      hc hne'.1 hne'.2
  obtain ⟨g, hg, hcase⟩ := hB.tableV.cover (f * f') hfC' (orderOf_eq_two_of_mul_self hsq hne1) hnet
  have hgA : ∀ y, g * (f * f') * g⁻¹ = y → IsConj t y := fun y e => by
    rw [← e]
    exact (htA.symm.trans hA).trans (isConj_conj_self g (f * f'))
  rcases hcase with e | e | e | e
  · exact absurd ⟨g, hg, Or.inl e⟩ hnotb
  · exact absurd ((hgA _ e).trans hB.isConj_z.symm) hB.not_isConj
  · have e' : g * (t * (f * f')) * g⁻¹ = z' := by
      rw [conj_mul_of_mem_centralizer hg, e, ← mul_assoc, htt, one_mul]
    exact hB.isConj_z.trans (isConj_iff.mpr ⟨g, e'⟩).symm
  · exact absurd ((hgA _ e).trans hB.isConj_u.symm) hB.not_isConj

end Main

end CommonNbr

section Final

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem commonNbrTwoB_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hS : BabyFi22Slice) :
    CommonNbrTwoB a z₀ := by
  intro x y t hx ht hyt hxy
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hy : IsConj a y := hyt.1
  have hD : t ∈ twoANbr a x ∩ twoANbr a y := ⟨ht, mem_twoANbr_symm h ht.1 hyt⟩
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG ht.1).exists_cover
  obtain ⟨f, hf, f', hf', hne, hc⟩ := CommonNbr.exists_commuting_pair_star I hG hS hx hy hxy hD hφ
  refine ⟨t * (f * f'), ?_,
    CommonNbr.isConj_twoB_of_commuting_star I hG hx hy hxy hD hφ hf hf' hne hc⟩
  exact Subgroup.mul_mem _ (mem_inf_of_mem h hx hy hD)
    (Subgroup.mul_mem _ (mem_inf_of_mem h hx hy hf.1) (mem_inf_of_mem h hx hy hf'.1))

theorem commonNbr_threeA_nonempty
    {b x : G} (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hS : BabyFi22Slice) (hb : IsConj a b) (hx : x ∈ typeSet a z₀ b .threeA) :
    (twoANbr a b ∩ twoANbr a x).Nonempty :=
  S37.exists_commonNbr_threeA I hG (commonNbrTwoB_of I hG hS) hb hx

end Final

end CFSG.Monster.GMS
