module

public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsTwo

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.ABGLocalTools (IsSylowOf)

namespace Step1012ClaimProof

variable {G : Type} [Group G] [Finite G]

theorem theta_inf_le_theta {H K : Subgroup G} (hKH : K ≤ H) :
    inSubgroup (aschbacherSolvableCore 3) H ⊓ K ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨hs, h3⟩ := Sec6.theta_solvable_and_not_dvd H
  refine Sec6.le_theta_of_normal inf_le_right (fun k hk => ?_) ?_ ?_
  · exact SteinbergBY.mem_normalizer_inf (Sec6.le_normalizer_theta H (hKH hk))
      (Subgroup.le_normalizer hk)
  · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
  · exact fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))

omit [Finite G] in
theorem surjective_mk_comp_inclusion {N T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (N : Set G))
    [(N.subgroupOf (N ⊔ T)).Normal] :
    Function.Surjective ((QuotientGroup.mk' (N.subgroupOf (N ⊔ T))).comp
      (Subgroup.inclusion (le_sup_right : T ≤ N ⊔ T))) := by
  intro q
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hv : (v : G) ∈ ((T ⊔ N : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact v.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at hv
  obtain ⟨t, ht, n, hn, htn⟩ := hv
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have h : ((Subgroup.inclusion (le_sup_right : T ≤ N ⊔ T) ⟨t, ht⟩)⁻¹ * v : ↥(N ⊔ T)) =
      (t⁻¹ * v : G) := rfl
  rw [h, ← htn, inv_mul_cancel_left]
  exact hn

omit [Finite G] in
theorem not_dvd_card_sup_of_le_normalizer {p : ℕ} (hp : p.Prime) {N T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : ¬ p ∣ Nat.card N)
    (hT : ¬ p ∣ Nat.card T) : ¬ p ∣ Nat.card (N ⊔ T : Subgroup G) := by
  set V := N ⊔ T with hV
  have hNV : N ≤ V := le_sup_left
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hTN
  have : (N.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mpr hVN
  have hf := surjective_mk_comp_inclusion hTN
  have hQ : Nat.card (V ⧸ N.subgroupOf V) ∣ Nat.card T := Subgroup.card_dvd_of_surjective hf
  have hNcard : Nat.card (N.subgroupOf V) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNV).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf V), hNcard]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · exact hT (h1.trans hQ)
  · exact hN h1

theorem theta_inf_centralizer_le_theta {H S : Subgroup G}
    (hS : IsSylowOf 2 S (inSubgroup (aschbacherSolvableCore 3) H)) :
    inSubgroup (aschbacherSolvableCore 3) (H ⊓ Subgroup.centralizer (S : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3) H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Θ := inSubgroup (aschbacherSolvableCore 3) H with hΘ
  set C := H ⊓ Subgroup.centralizer (S : Set G) with hC
  set θC := inSubgroup (aschbacherSolvableCore 3) C with hθC
  have hΘH : Θ ≤ H := Sec6.theta_le H
  have hθCH : θC ≤ H := (Sec6.theta_le C).trans inf_le_left
  have hSΘ : S ≤ Θ := hS.le
  obtain ⟨hΘs, hΘ3⟩ := Sec6.theta_solvable_and_not_dvd H
  obtain ⟨hθCs, hθC3⟩ := Sec6.theta_solvable_and_not_dvd C
  have hHΘ : H ≤ Subgroup.normalizer (Θ : Set G) := Sec6.le_normalizer_theta H
  set T := Θ ⊔ θC with hT
  have hTH : T ≤ H := sup_le hΘH hθCH
  have hHT : H ≤ Subgroup.normalizer (T : Set G) := by
    intro h hh
    set S' := S.map (MulAut.conj h).toMonoidHom with hS'
    have hS'Θ : S' ≤ Θ := by
      rintro _ ⟨s, hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hHΘ hh) s).mp (hSΘ hs)
    have hS'syl : IsSylowOf 2 S' Θ := CFSG.ABGLocalTools.isSylowOf_of_card hS'Θ (by
      rw [hS', Subgroup.card_map_of_injective (MulAut.conj h).injective]
      exact hS.card_eq)
    obtain ⟨k, hkΘ, hk⟩ := hS.exists_mem_conj hS'syl
    have hm : k⁻¹ * h ∈ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨s, hs, rfl⟩
        have h1 : h * s * h⁻¹ ∈ S' := ⟨s, hs, rfl⟩
        have h2 := (hk _).mp h1
        change k⁻¹ * h * s * (k⁻¹ * h)⁻¹ ∈ S
        have h3 : k⁻¹ * h * s * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * s * h⁻¹) * k := by group
        rw [h3]
        exact h2
      · rw [Subgroup.card_map_of_injective (MulAut.conj (k⁻¹ * h)).injective]
    have hmH : k⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hΘH hkΘ)) hh
    have hmT : k⁻¹ * h ∈ Subgroup.normalizer (T : Set G) :=
      Sec10XSteps.mem_normalizer_sup_of_mem (hHΘ hmH)
        (Sec6.normalizer_le_normalizer_theta C (SteinbergBY.mem_normalizer_inf
          (Subgroup.le_normalizer hmH) (Sec10XSteps.normalizer_le_normalizer_centralizer_of hm)))
    have hkT : k ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.le_normalizer ((le_sup_left : Θ ≤ T) hkΘ)
    have heq : h = k * (k⁻¹ * h) := by group
    rw [heq]
    exact Subgroup.mul_mem _ hkT hmT
  have hθCN : θC ≤ Subgroup.normalizer (Θ : Set G) := hθCH.trans hHΘ
  have hTs : Group.IsSolvable T := isSolvable_sup_of_le_normalizer hθCN hΘs hθCs
  have hT3 : ¬ 3 ∣ Nat.card T := not_dvd_card_sup_of_le_normalizer Nat.prime_three hθCN hΘ3 hθC3
  exact le_sup_right.trans (Sec6.le_theta_of_normal hTH hHT hTs hT3)

theorem exists_isSylowOf_theta_normalized {H A U X : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAab : IsMulCommutative A) (hAH : A ≤ H) (hU2 : IsPGroup 2 U)
    (hUΘ : U ≤ inSubgroup (aschbacherSolvableCore 3) H)
    (hUA : A ≤ Subgroup.normalizer (U : Set G)) (hX2 : IsPGroup 2 X) (hXH : X ≤ H)
    (hXA : A ≤ Subgroup.normalizer (X : Set G)) (hXU : X ≤ Subgroup.normalizer (U : Set G)) :
    ∃ S : Subgroup G, IsSylowOf 2 S (inSubgroup (aschbacherSolvableCore 3) H) ∧
      A ≤ Subgroup.normalizer (S : Set G) ∧ U ≤ S ∧ X ≤ Subgroup.normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Θ := inSubgroup (aschbacherSolvableCore 3) H with hΘ
  obtain ⟨hΘs, hΘ3⟩ := Sec6.theta_solvable_and_not_dvd H
  have hΘH : Θ ≤ H := Sec6.theta_le H
  have hHΘ : H ≤ Subgroup.normalizer (Θ : Set G) := Sec6.le_normalizer_theta H
  set Y := Θ ⊔ X with hY
  have hYH : Y ≤ H := sup_le hΘH hXH
  have hXΘ : X ≤ Subgroup.normalizer (Θ : Set G) := hXH.trans hHΘ
  have hXs : Group.IsSolvable X := by
    have := hX2.isNilpotent
    infer_instance
  have hYs : Group.IsSolvable Y := isSolvable_sup_of_le_normalizer hXΘ hΘs hXs
  have hX3 : ¬ 3 ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hY3 : ¬ 3 ∣ Nat.card Y := not_dvd_card_sup_of_le_normalizer Nat.prime_three hXΘ hΘ3 hX3
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
    Sec10XSteps.mem_normalizer_sup_of_mem (hHΘ (hAH hx)) (hXA hx)
  set ρ : A →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hAY) with hρ
  have hρapp : ∀ (x : A) (y : Y), ((ρ x y : Y) : G) = (x : G) * y * (x : G)⁻¹ := fun x y =>
    Sec4.normalizerMonoidHom_apply_coe (hAY x.2) y
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Y) := by
    obtain ⟨k, hk⟩ := hA3.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)
  have hAs : Group.IsSolvable A := Group.isSolvable_of_comm fun x y => hAab.1.comm x y
  have hXU2 : IsPGroup 2 (X ⊔ U : Subgroup G) := IsPGroup.to_sup_of_normal_right' hX2 hU2 hXU
  have hXUY : X ⊔ U ≤ Y := sup_le le_sup_right (hUΘ.trans le_sup_left)
  set V' := (X ⊔ U).subgroupOf Y with hV'
  have hV'2 : IsPGroup 2 V' := hXU2.comap_subtype (K := Y)
  have hV'inv : ∀ x : A, ∀ v ∈ V', ρ x v ∈ V' := fun x v hv => by
    rw [Subgroup.mem_subgroupOf, hρapp]
    exact (Subgroup.mem_normalizer_iff.mp (Sec10XSteps.mem_normalizer_sup_of_mem (hXA x.2)
      (hUA x.2)) v).mp (Subgroup.mem_subgroupOf.mp hv)
  obtain ⟨Q, hVQ, hQinv⟩ :=
    (PGroups.solvable_coprime_invariant_sylow_containment hcop ρ Nat.prime_two).1 V' hV'2 hV'inv
  have hQinv' : ∀ x : A, ∀ y ∈ (Q : Subgroup Y), ρ x y ∈ (Q : Subgroup Y) := fun x y hy => by
    rw [← hQinv x]
    exact ⟨y, hy, rfl⟩
  set P := (Q : Subgroup Y).map Y.subtype with hP
  have hPsyl : IsSylowOf 2 P Y := ⟨Q, rfl⟩
  have hPA : A ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨ρ ⟨x, hx⟩ s, hQinv' ⟨x, hx⟩ s hs, hρapp ⟨x, hx⟩ s⟩
    · rintro ⟨s, hs, hsz⟩
      refine ⟨ρ ⟨x, hx⟩⁻¹ s, hQinv' _ s hs, ?_⟩
      have h1 := hρapp ⟨x, hx⟩⁻¹ s
      simp only [Subgroup.coe_subtype] at hsz ⊢
      rw [h1, hsz]
      simp only [Subgroup.coe_inv, inv_inv]
      group
  have hXP : X ≤ P := fun x hx =>
    have hx' : x ∈ X ⊔ U := (le_sup_left : X ≤ X ⊔ U) hx
    ⟨⟨x, hXUY hx'⟩, hVQ (Subgroup.mem_subgroupOf.mpr hx'), rfl⟩
  have hUP : U ≤ P := fun u hu =>
    have hu' : u ∈ X ⊔ U := (le_sup_right : U ≤ X ⊔ U) hu
    ⟨⟨u, hXUY hu'⟩, hVQ (Subgroup.mem_subgroupOf.mpr hu'), rfl⟩
  refine ⟨P ⊓ Θ, hPsyl.inf_of_le_normalizer le_sup_left (hYH.trans hHΘ),
    fun x hx => SteinbergBY.mem_normalizer_inf (hPA hx) (hHΘ (hAH hx)), le_inf hUP hUΘ,
    fun x hx => SteinbergBY.mem_normalizer_inf (Subgroup.le_normalizer (hXP hx)) (hXΘ hx)⟩

theorem mem_maxInvariantPiSubgroups_of_isSylowOf {Θ A' S : Subgroup G}
    (hS : IsSylowOf 2 S Θ) (hSA : A' ≤ Subgroup.normalizer (S : Set G)) :
    S ∈ maxInvariantPiSubgroups Θ A' (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [mem_maxInvariantPiSubgroups_iff]
  refine ⟨⟨hS.le, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS.isPGroup, hSA⟩,
    fun Y hY hSY => ?_⟩
  obtain ⟨hYΘ, hY2, -⟩ := hY
  exact hS.eq_of_le hSY hYΘ ((isPiSubgroup_piOf_iff Nat.prime_two Y).mp hY2)

theorem not_le_centralizer {U S X : Subgroup G} {e d : G}
    (hS : IsSylowOf 2 S
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G))))
    (hUS : U ≤ S)
    (hXU : X ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (U : Set G)))
    (hXe : X ≤ Subgroup.centralizer ({e} : Set G)) (hXd : X ≤ Subgroup.centralizer ({d} : Set G))
    (hXθ : ¬ X ≤ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ((Subgroup.closure {e, d} : Subgroup G) : Set G))) :
    ¬ X ≤ Subgroup.centralizer (S : Set G) := by
  intro hXS
  apply hXθ
  have hK : Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer (S : Set G) ≤
      Subgroup.centralizer (U : Set G) := inf_le_right.trans (Subgroup.centralizer_le hUS)
  have h1 : X ≤ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer (S : Set G)) :=
    (le_inf hXU (le_inf hXe hXS)).trans (theta_inf_le_theta hK)
  have h2 := h1.trans (theta_inf_centralizer_le_theta hS)
  exact (le_inf h2 hXd).trans (Sec10XProof.theta_inf_centralizer_le e d)

end Step1012ClaimProof

end CFSG.RankThree.PartTwo.Sec10
