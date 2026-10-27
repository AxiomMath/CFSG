module

public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_map_normalizerMonoidHom {X : Subgroup G} (a : normalizer (X : Set G))
    (K : Subgroup X) :
    (K.map (X.normalizerMonoidHom a).toMonoidHom).map X.subtype =
      (K.map X.subtype).map (MulAut.conj (a : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem conj_eq_or_commutator_eq_bot {X : Subgroup G} {K : Subgroup X}
    (hK : CFSG.IsComponent K) (a a' : normalizer (X : Set G)) :
    (K.map X.subtype).map (MulAut.conj (a : G)).toMonoidHom =
        (K.map X.subtype).map (MulAut.conj (a' : G)).toMonoidHom ∨
      ⁅(K.map X.subtype).map (MulAut.conj (a : G)).toMonoidHom,
        (K.map X.subtype).map (MulAut.conj (a' : G)).toMonoidHom⁆ = ⊥ := by
  have hKa := CFSG.LocalCores.isComponent_map_mulEquiv (X.normalizerMonoidHom a) hK
  have hKa' := CFSG.LocalCores.isComponent_map_mulEquiv (X.normalizerMonoidHom a') hK
  rw [← map_subtype_map_normalizerMonoidHom, ← map_subtype_map_normalizerMonoidHom]
  rcases CFSG.LocalCores.distinct_components_commute hKa hKa' with h | h
  · left
    rw [h]
  · right
    rw [← Subgroup.map_commutator, h, Subgroup.map_bot]

omit [Finite G] in
theorem inv_mul_mem_normalizer_of_map_eq {H : Subgroup G} {a a' : G}
    (h : H.map (MulAut.conj a).toMonoidHom = H.map (MulAut.conj a').toMonoidHom) :
    a'⁻¹ * a ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have h1 := congrArg (fun K : Subgroup G => K.map (MulAut.conj a'⁻¹).toMonoidHom) h
  simp only [Subgroup.map_map] at h1
  have e1 : ((MulAut.conj a'⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom) =
      (MulAut.conj (a'⁻¹ * a)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  have e2 : ((MulAut.conj a'⁻¹).toMonoidHom.comp (MulAut.conj a').toMonoidHom) =
      MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  rw [e1, e2, Subgroup.map_id] at h1
  exact h1

section Certified


theorem not_odd_card_inf_centralizer_of_isComponent {X A : Subgroup G}
    (hXK : CFSG.IsKGroup X) (hX3 : ¬ 3 ∣ Nat.card X) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAX : A ≤ normalizer (X : Set G)) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    ¬ Odd (Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set KG : Subgroup G := K.map X.subtype with hKG
  have hKGX : KG ≤ X := map_subtype_le K
  have hKGcard : Nat.card KG ∣ Nat.card X := Subgroup.card_dvd_of_le hKGX
  set eK : K ≃* KG := K.equivMapOfInjective X.subtype X.subtype_injective with heK
  have hKq : CFSG.IsQuasisimple KG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have : IsSimpleGroup (KG ⧸ center KG) := hKq.2.1
  have hcat : CFSG.Assembly.InCatalog (KG ⧸ center KG) :=
    CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hXK K
      (KG ⧸ center KG) ((QuotientGroup.mk' (center KG)).comp eK.toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp eK.surjective)
  have h3Q : ¬ 3 ∣ Nat.card (KG ⧸ center KG) := fun h =>
    hX3 (h.trans ((Subgroup.card_quotient_dvd_card _).trans hKGcard))
  obtain ⟨f, hSz⟩ :=
    KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd _ hKq.2.2 hcat h3Q
  set B : Subgroup G := A ⊓ normalizer (KG : Set G) with hB
  have hB3 : IsPGroup 3 B := fun b => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, hA3 b b.2.1, Subgroup.coe_one])⟩
  set β : B →* MulAut KG := KG.normalizerMonoidHom.comp (inclusion inf_le_right) with hβ
  have hβ_apply : ∀ (b : B) (k : KG), ((β b k : KG) : G) = (b : G) * k * (b : G)⁻¹ :=
    fun b k => normalizerMonoidHom_apply_apply_coe _ _ _
  have hN : ∀ b : B, ∀ n ∈ center KG, β b n ∈ center KG := by
    intro b n hn
    rw [mem_center_iff] at hn ⊢
    intro g
    obtain ⟨g', rfl⟩ := (β b).surjective g
    rw [← map_mul, ← map_mul, hn g']
  set ρ := CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction β (center KG) hN
    with hρ
  obtain ⟨tbar, ht2, htfix⟩ := KFacts.KP7.exists_involution_fixed_of_suzukiModel hSz ρ
    (E := ⊤) (fun x _ => Subtype.ext (by rw [Subgroup.coe_pow, hA3 x x.2.1, Subgroup.coe_one]))
  have hcop : ¬ 3 ∣ Nat.card (center KG) := fun h =>
    hX3 (h.trans ((Subgroup.card_subgroup_dvd_card _).trans hKGcard))
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hB3 β (center KG) hN
    hcop
  have htmem : tbar ∈ {q : KG ⧸ center KG | ∀ b : B, ρ b q = q} := fun b =>
    htfix b (Subgroup.mem_top b)
  rw [hlift] at htmem
  obtain ⟨s, hsfix, hst⟩ := htmem
  have hsB : ∀ b ∈ B, b * (s : G) * b⁻¹ = s := fun b hb => by
    have := congrArg Subtype.val (hsfix ⟨b, hb⟩)
    rwa [hβ_apply] at this
  set g : A → G := fun a => (a : G) * s * (a : G)⁻¹ with hg
  have hgX : ∀ a : A, g a ∈ X := fun a => by
    have h1 := (mem_normalizer_iff.mp (hAX a.2) s).mp (hKGX s.2)
    exact h1
  have hgmem : ∀ a : A, g a ∈ KG.map (MulAut.conj (a : G)).toMonoidHom := fun a =>
    ⟨s, s.2, rfl⟩
  have hdich : ∀ a a' : A, KG.map (MulAut.conj (a : G)).toMonoidHom =
        KG.map (MulAut.conj (a' : G)).toMonoidHom ∨
      ⁅KG.map (MulAut.conj (a : G)).toMonoidHom, KG.map (MulAut.conj (a' : G)).toMonoidHom⁆ = ⊥ :=
    fun a a' => conj_eq_or_commutator_eq_bot hK ⟨a, hAX a.2⟩ ⟨a', hAX a'.2⟩
  have hcomm : ∀ a a' : A, g a * g a' = g a' * g a := by
    intro a a'
    rcases hdich a a' with h | h
    · have hn : (a' : G)⁻¹ * a ∈ B :=
        ⟨A.mul_mem (A.inv_mem a'.2) a.2, inv_mul_mem_normalizer_of_map_eq h⟩
      have hga : g a = g a' := by
        have h1 := hsB _ hn
        simp only [hg]
        calc (a : G) * s * (a : G)⁻¹ =
            (a' : G) * (((a' : G)⁻¹ * a) * s * ((a' : G)⁻¹ * a)⁻¹) * (a' : G)⁻¹ := by group
          _ = (a' : G) * s * (a' : G)⁻¹ := by rw [h1]
      rw [hga]
    · have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h (hgmem a)
      exact (mem_centralizer_iff.mp h1 (g a') (hgmem a')).symm
  have : Fintype A := Fintype.ofFinite A
  set E₀ := closure (Set.range g) with hE₀
  have hE₀comm : (Set.range g).Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ -
    exact hcomm a a'
  have : IsMulCommutative E₀ := isMulCommutative_closure hE₀comm
  set e : A → E₀ := fun a => ⟨g a, subset_closure ⟨a, rfl⟩⟩ with he
  set y : E₀ := ∏ a : A, e a with hy
  have hE₀X : E₀ ≤ X := by
    rw [hE₀, closure_le]
    rintro _ ⟨a, rfl⟩
    exact hgX a
  have hyA : ∀ a₀ ∈ A, a₀ * (y : G) * a₀⁻¹ = y := by
    intro a₀ ha₀
    have hmap : E₀.map (MulAut.conj a₀).toMonoidHom ≤ E₀ := by
      rw [hE₀, MonoidHom.map_closure, closure_le]
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      refine subset_closure ⟨⟨a₀ * a, mul_mem ha₀ a.2⟩, ?_⟩
      simp only [hg, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    set φ : E₀ →* E₀ :=
      { toFun := fun x => ⟨a₀ * x * a₀⁻¹, hmap ⟨x, x.2, rfl⟩⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x x' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) } with hφ
    have hφe' : ∀ a : A, φ (e a) = e (⟨a₀, ha₀⟩ * a) := fun a => Subtype.ext (by
      change a₀ * ((a : G) * s * (a : G)⁻¹) * a₀⁻¹ = (a₀ * a) * s * (a₀ * a)⁻¹
      group)
    have h1 : φ y = y := by
      rw [hy, map_prod]
      simp only [hφe']
      exact Equiv.prod_comp (Equiv.mulLeft (⟨a₀, ha₀⟩ : A)) e
    have h2 := congrArg Subtype.val h1
    exact h2
  set B' : Subgroup A := (normalizer (KG : Set G)).subgroupOf A with hB'
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset A)
    (fun a => a ∈ B') e
  set m := (Finset.univ.filter fun a : A => a ∈ B').card with hm
  have he1 : ∀ a ∈ Finset.univ.filter (fun a : A => a ∈ B'),
      e a = ⟨s, subset_closure ⟨1, by simp [hg]⟩⟩ := by
    intro a ha
    rw [Finset.mem_filter] at ha
    apply Subtype.ext
    exact hsB a ⟨a.2, Subgroup.mem_subgroupOf.mp ha.2⟩
  rw [Finset.prod_eq_pow_card he1] at hsplit
  set z := ∏ a ∈ Finset.univ.filter (fun a : A => a ∉ B'), e a with hz
  have hzC : (z : G) ∈ centralizer (KG : Set G) := by
    rw [hz]
    refine Finset.prod_induction _ (fun x : E₀ => (x : G) ∈ centralizer (KG : Set G))
      (fun x x' hx hx' => mul_mem hx hx') (one_mem _) ?_
    intro a ha
    rw [Finset.mem_filter] at ha
    rcases hdich a 1 with h | h
    · exfalso
      apply ha.2
      rw [Subgroup.mem_subgroupOf]
      have h1 := inv_mul_mem_normalizer_of_map_eq h
      simpa using h1
    · have hone : KG.map (MulAut.conj ((1 : A) : G)).toMonoidHom = KG := by
        ext x
        simp
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h (hgmem a)
      rwa [hone] at h1
  have hmodd : Odd m := by
    have hcard : m = Nat.card B' := by
      rw [hm, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    have hA3' : IsPGroup 3 A := fun a => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, hA3 a a.2, Subgroup.coe_one])⟩
    obtain ⟨n, hn⟩ := hA3'.exists_card_eq
    rw [hcard]
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (hn ▸ Subgroup.card_subgroup_dvd_card B')
  have hyXA : (y : G) ∈ X ⊓ centralizer (A : Set G) := by
    refine ⟨hE₀X y.2, mem_centralizer_iff.mpr fun a ha => ?_⟩
    have h1 := hyA a ha
    calc a * (y : G) = a * (y : G) * a⁻¹ * a := by group
      _ = y * a := by rw [h1]
  intro hodd
  have hk : Odd (orderOf (y : G)) := by
    have h1 : orderOf (⟨y, hyXA⟩ : ↥(X ⊓ centralizer (A : Set G))) ∣
        Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  set k := orderOf (y : G) with hkdef
  have hyk : y ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_orderOf_eq_one,
    Subgroup.coe_one])
  rw [hy, ← hsplit, mul_pow, ← pow_mul] at hyk
  have hsk : (s : G) ^ (m * k) ∈ centralizer (KG : Set G) := by
    have h1 : (⟨s, subset_closure ⟨1, by simp [hg]⟩⟩ : E₀) ^ (m * k) = (z ^ k)⁻¹ :=
      eq_inv_of_mul_eq_one_left hyk
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_pow, Subgroup.coe_inv] at h2
    rw [h2]
    exact inv_mem (pow_mem hzC k)
  have hcen : s ^ (m * k) ∈ center KG := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    exact (mem_centralizer_iff.mp hsk x x.2)
  have h1 : tbar ^ (m * k) = 1 := by
    rw [← hst, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcen
  have h2 : 2 ∣ m * k := ht2 ▸ orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h)
  · exact (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr h)

end Certified

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
