module

public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.ThetaFree

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped Pointwise

variable {X : Type*} [Group X]

@[expose] def conjOrbit (B J : Subgroup X) : Set (Subgroup X) :=
  Set.range fun b : B => J.map (MulAut.conj (b : X)).toMonoidHom

@[expose] def orbitProd (B J : Subgroup X) : Subgroup X := sSup (conjOrbit B J)

theorem conjOrbit_eq_orbit (B J : Subgroup X) :
    letI := Theta.conjAction B
    conjOrbit B J = MulAction.orbit B J := rfl

theorem self_mem_conjOrbit (B J : Subgroup X) : J ∈ conjOrbit B J :=
  ⟨1, by ext; simp⟩

theorem map_conj_mem_conjOrbit {B J K : Subgroup X} (hK : K ∈ conjOrbit B J) {b : X}
    (hb : b ∈ B) : K.map (MulAut.conj b).toMonoidHom ∈ conjOrbit B J := by
  obtain ⟨a, rfl⟩ := hK
  exact ⟨⟨b, hb⟩ * a, (map_conj_map_conj J (a : X) b).symm⟩

theorem le_orbitProd {B J K : Subgroup X} (hK : K ∈ conjOrbit B J) : K ≤ orbitProd B J :=
  le_sSup hK

theorem isComponent_of_mem_conjOrbit [Finite X] {B J K : Subgroup X} (hJ : IsComponent J)
    (hK : K ∈ conjOrbit B J) : IsComponent K := by
  obtain ⟨a, rfl⟩ := hK
  exact LocalCores.isComponent_map_mulEquiv _ hJ

theorem le_normalizer_orbitProd (B J : Subgroup X) :
    B ≤ normalizer (orbitProd B J : Set X) := by
  have key : ∀ c ∈ B, (orbitProd B J).map (MulAut.conj c).toMonoidHom ≤ orbitProd B J := by
    intro c hc
    rw [orbitProd, (gc_map_comap _).l_sSup]
    exact iSup₂_le fun K hK => le_sSup (map_conj_mem_conjOrbit hK hc)
  exact fun b hb => Theta.mem_normalizer_of_map_conj_le (key b hb) (key b⁻¹ (inv_mem hb))

variable [Finite X] {B J : Subgroup X}

theorem isComponent_subgroupOf_orbitProd (hJ : IsComponent J) {K : Subgroup X}
    (hK : K ∈ conjOrbit B J) : IsComponent (K.subgroupOf (orbitProd B J)) := by
  have hKc := isComponent_of_mem_conjOrbit hJ hK
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (le_orbitProd hK)).symm hKc.1,
    hKc.2.subgroupOf⟩

omit [Finite X] in
theorem sSup_subgroupOf_orbitProd (B J : Subgroup X) :
    sSup ((fun K => K.subgroupOf (orbitProd B J)) '' conjOrbit B J) = ⊤ := by
  apply map_injective (orbitProd B J).subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype]
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    exact sSup_le fun _ ⟨K, hK, hKe⟩ => hKe ▸ comap_mono (le_sSup hK)
  · refine sSup_le fun K hK x hx => ?_
    have hxS : x ∈ orbitProd B J := le_orbitProd hK hx
    have hle : K.subgroupOf (orbitProd B J) ≤
        sSup ((fun K => K.subgroupOf (orbitProd B J)) '' conjOrbit B J) :=
      le_sSup (Set.mem_image_of_mem (fun K => K.subgroupOf (orbitProd B J)) hK)
    exact ⟨⟨x, hxS⟩, hle (mem_subgroupOf.2 hx), rfl⟩

theorem layer_orbitProd_eq_top (hJ : IsComponent J) : layer (orbitProd B J) = ⊤ := by
  rw [eq_top_iff, ← sSup_subgroupOf_orbitProd B J]
  exact sSup_le fun _ ⟨K, hK, hKe⟩ =>
    hKe ▸ LocalCores.component_le_layer (isComponent_subgroupOf_orbitProd hJ hK)

theorem exists_eq_subgroupOf_of_isComponent (hJ : IsComponent J)
    {C : Subgroup (orbitProd B J)} (hC : IsComponent C) :
    ∃ K ∈ conjOrbit B J, C = K.subgroupOf (orbitProd B J) := by
  by_contra hne
  push Not at hne
  have hcent : ∀ K ∈ conjOrbit B J,
      K.subgroupOf (orbitProd B J) ≤ centralizer (C : Set (orbitProd B J)) := fun K hK =>
    le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1
      ((LocalCores.distinct_components_commute hC
        (isComponent_subgroupOf_orbitProd hJ hK)).resolve_left (hne K hK)))
  have htop : (⊤ : Subgroup (orbitProd B J)) ≤ centralizer (C : Set (orbitProd B J)) := by
    rw [← sSup_subgroupOf_orbitProd B J]
    exact sSup_le fun _ ⟨K, hK, hKe⟩ => hKe ▸ hcent K hK
  have hCC : C ≤ centralizer (C : Set (orbitProd B J)) := fun x _ => htop (mem_top x)
  have hbot : C = ⊥ := by
    rw [← (Subgroup.isPerfect_iff.mp hC.1.1)]
    exact commutator_eq_bot_iff_le_centralizer.2 hCC
  have hnt : Nontrivial C := LocalCores.isQuasisimple_nontrivial hC.1
  rw [hbot] at hnt
  obtain ⟨x, hx⟩ := exists_ne (1 : (⊥ : Subgroup (orbitProd B J)))
  exact hx (Subtype.ext (mem_bot.1 x.2))

theorem map_center_orbitProd_le (hJ : IsComponent J) :
    (center (orbitProd B J)).map (orbitProd B J).subtype ≤
      layer X ⊓ centralizer (layer X : Set X) := by
  rintro _ ⟨z, hz, rfl⟩
  have hSlayer : orbitProd B J ≤ layer X :=
    sSup_le fun K hK => LocalCores.component_le_layer (isComponent_of_mem_conjOrbit hJ hK)
  refine ⟨hSlayer z.2, ?_⟩
  have hle : layer X ≤ centralizer ({(z : X)} : Set X) := by
    refine sSup_le fun K hKc => ?_
    by_cases hKO : K ∈ conjOrbit B J
    · intro k hk
      rw [mem_centralizer_singleton_iff]
      have h := mem_center_iff.1 hz ⟨k, le_orbitProd hKO hk⟩
      exact congrArg Subtype.val h
    · have hSK : orbitProd B J ≤ centralizer (K : Set X) := by
        refine sSup_le fun K' hK' => ?_
        have hne : K ≠ K' := fun h => hKO (h ▸ hK')
        exact le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1
          ((LocalCores.distinct_components_commute hKc
            (isComponent_of_mem_conjOrbit hJ hK')).resolve_left hne))
      intro k hk
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 (hSK z.2) k hk)
  show (z : X) ∈ centralizer (layer X : Set X)
  rw [mem_centralizer_iff]
  intro g hg
  exact mem_centralizer_singleton_iff.1 (hle hg)

theorem layer_inf_centralizer_le_pCore_three (hθ : aschbacherSolvableCore 3 X = ⊥) :
    layer X ⊓ centralizer (layer X : Set X) ≤ pCore 3 X := by
  have hr : ∀ r : ℕ, r.Prime → r ≠ 3 → pCore r X = ⊥ := fun r hr hr3 => le_bot_iff.1
    (hθ ▸ (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.2.2.2 r hr hr3)
  have hF : fittingSubgroup X ≤ pCore 3 X := by
    rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun r => ?_
    by_cases h : (r : ℕ) = 3
    · rw [h]
    · rw [hr r (Nat.prime_of_mem_primeFactors r.2) h]
      exact bot_le
  have : (layer X).Characteristic := LocalCores.layer_characteristic
  set N : Subgroup X := layer X ⊓ centralizer (layer X : Set X) with hN
  have hNc : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.1 b.2.2 a a.2.1)⟩⟩
  exact (LocalCores.fitting_characteristic.2.2 N inferInstance inferInstance).trans hF

theorem isPGroup_center_orbitProd (hθ : aschbacherSolvableCore 3 X = ⊥) (hJ : IsComponent J) :
    IsPGroup 3 (center (orbitProd B J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := (pCore_isPGroup (p := 3) (G := X)).to_le
    ((map_center_orbitProd_le (B := B) hJ).trans (layer_inf_centralizer_le_pCore_three hθ))
  exact h.of_equiv ((center (orbitProd B J)).equivMapOfInjective _
    (orbitProd B J).subtype_injective).symm

omit [Finite X] in
theorem normal_subgroupOf_sup {S V : Subgroup X} (hV : V ≤ normalizer (S : Set X)) :
    (S.subgroupOf (S ⊔ V)).Normal :=
  (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hV)

omit [Finite X] in
theorem isPGroup_quotient_sup {S V : Subgroup X} (hV : V ≤ normalizer (S : Set X))
    (hV3 : IsPGroup 3 V) :
    haveI := normal_subgroupOf_sup hV
    IsPGroup 3 ((S ⊔ V : Subgroup X) ⧸ S.subgroupOf (S ⊔ V)) := by
  have := normal_subgroupOf_sup hV
  intro q
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
  have ht : (t : X) ∈ (S : Set X) * (V : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left S V hV]
    exact t.2
  obtain ⟨s, hs, v, hv, hsv⟩ := ht
  obtain ⟨k, hk⟩ := hV3 ⟨v, hv⟩
  refine ⟨k, ?_⟩
  have hte : t = (⟨s, (le_sup_left : S ≤ S ⊔ V) hs⟩ : (S ⊔ V : Subgroup X)) *
      ⟨v, (le_sup_right : V ≤ S ⊔ V) hv⟩ := Subtype.ext hsv.symm
  have hs1 : ((⟨s, (le_sup_left : S ≤ S ⊔ V) hs⟩ : (S ⊔ V : Subgroup X)) :
      (S ⊔ V : Subgroup X) ⧸ S.subgroupOf (S ⊔ V)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hs)
  have hv1 : (⟨v, (le_sup_right : V ≤ S ⊔ V) hv⟩ : (S ⊔ V : Subgroup X)) ^ 3 ^ k = 1 :=
    Subtype.ext (by
      have h := congrArg Subtype.val hk
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h ⊢
      exact h)
  rw [hte, QuotientGroup.mk_mul, hs1, one_mul, ← QuotientGroup.mk_pow, hv1, QuotientGroup.mk_one]

theorem aschbacherSolvableCore_sup_eq_bot (hJ : IsComponent J) {V : Subgroup X}
    (hV : V ≤ normalizer (orbitProd B J : Set X)) (hV3 : IsPGroup 3 V)
    (hZ : IsPGroup 3 (center (orbitProd B J))) :
    aschbacherSolvableCore 3 (orbitProd B J ⊔ V : Subgroup X) = ⊥ := by
  set S := orbitProd B J with hSdef
  set T : Subgroup X := S ⊔ V with hTdef
  have := normal_subgroupOf_sup hV
  have hquot := isPGroup_quotient_sup hV hV3
  obtain ⟨hΘs, hΘc, hΘ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := T) Nat.prime_three
  set Θ := aschbacherSolvableCore 3 T with hΘdef
  have : Θ.Normal := by
    have := hΘc
    infer_instance
  have hΘS : Θ ≤ S.subgroupOf T := by
    intro θ hθ
    have hcop : Nat.Coprime (Nat.card Θ) 3 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hΘ3 |>.symm
    obtain ⟨k, hk⟩ := hquot (θ : T ⧸ S.subgroupOf T)
    have h1 : orderOf (θ : T ⧸ S.subgroupOf T) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (θ : T ⧸ S.subgroupOf T) ∣ Nat.card Θ :=
      (orderOf_map_dvd (QuotientGroup.mk' (S.subgroupOf T)) θ).trans
        (Subgroup.orderOf_dvd_natCard Θ hθ)
    have h3 : orderOf (θ : T ⧸ S.subgroupOf T) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k hcop).symm h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  set R : Subgroup X := Θ.map T.subtype with hRdef
  have hRS : R ≤ S := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact mem_subgroupOf.1 (hΘS hθ)
  have hRcard : Nat.card R = Nat.card Θ := card_map_of_injective T.subtype_injective
  have hconj : ∀ s ∈ S, R.map (MulAut.conj s).toMonoidHom ≤ R := by
    rintro s hs _ ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    have hsT : s ∈ T := (le_sup_left : S ≤ T) hs
    exact ⟨⟨s, hsT⟩ * θ * ⟨s, hsT⟩⁻¹, (inferInstance : Θ.Normal).conj_mem θ hθ ⟨s, hsT⟩, rfl⟩
  have hSN : S ≤ normalizer (R : Set X) := fun s hs =>
    Theta.mem_normalizer_of_map_conj_le (hconj s hs) (hconj s⁻¹ (inv_mem hs))
  have hRn : (R.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hRS).2 hSN
  have hRs : Group.IsSolvable (R.subgroupOf S) := by
    have e : R.subgroupOf S ≃* Θ := (subgroupOfEquivOfLe hRS).trans
      (Θ.equivMapOfInjective T.subtype T.subtype_injective).symm
    have := hΘs
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hRZ : R.subgroupOf S ≤ center S := by
    have hcomm := (LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).2
    rw [layer_orbitProd_eq_top hJ] at hcomm
    intro r hr
    rw [mem_center_iff]
    intro g
    have := commutator_eq_bot_iff_le_centralizer.1 hcomm (mem_top g)
    exact (mem_centralizer_iff.1 this r hr).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : IsPGroup 3 (R.subgroupOf S) := hZ.to_le hRZ
  obtain ⟨m, hm⟩ := hR3.exists_card_eq
  have hcard' : Nat.card (R.subgroupOf S) = Nat.card Θ :=
    (Nat.card_congr (subgroupOfEquivOfLe hRS).toEquiv).trans hRcard
  have hRbot : R.subgroupOf S = ⊥ := by
    rw [← card_eq_one, hm]
    rcases m with _ | m
    · rfl
    · exfalso
      apply hΘ3
      rw [← hcard', hm]
      exact dvd_pow_self 3 (Nat.succ_ne_zero m)
  have hR : R = ⊥ := by
    have h := congrArg (fun H : Subgroup S => H.map S.subtype) hRbot
    simp only [subgroupOf_map_subtype, inf_of_le_left hRS, Subgroup.map_bot] at h
    exact h
  exact (map_eq_bot_iff_of_injective _ T.subtype_injective).1 hR

end CFSG.RankThree.ThetaFree
