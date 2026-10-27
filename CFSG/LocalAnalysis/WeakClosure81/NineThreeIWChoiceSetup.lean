module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_A_mem_omega (hc : Nine3Choice V T A K S X p g x) :
    A ∈ omegaIn V K (nineE V K) :=
  ⟨hc.core.A_mem_nineOmegaIn.1, hc.core.A_mem_nineOmegaIn.2.trans hc.core.S_le_K⟩

theorem nine3_comm_of_mem_omega (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    ⁅nineI V K, U⁆ = U ⊓ pCoreOf 2 K := by
  obtain ⟨k, hk, hUk⟩ :=
    nine_two_transitive hc.core.hyp7 hc.core.rk_gt hc.core.hyp.base.toTwoPTwoIrred
      A (nine3_A_mem_omega hc) U hU
  have h := congrArg (fun H : Subgroup G => conjSubgroup H k)
    (hI.comm A hc.core.A_mem_nineOmegaIn)
  rw [E3.conjSubgroup_commutator, E3.conjSubgroup_inf,
    Nine3Core.conjSubgroup_nineI hk, Nine3Core.conjSubgroup_pCoreOf K hk] at h
  simpa [hUk] using h

theorem nine3_relIndex_of_mem_omega (hc : Nine3Choice V T A K S X p g x)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    (U ⊓ pCoreOf 2 K).relIndex U = 2 := by
  obtain ⟨k, hk, hUk⟩ :=
    nine_two_transitive hc.core.hyp7 hc.core.rk_gt hc.core.hyp.base.toTwoPTwoIrred
      A (nine3_A_mem_omega hc) U hU
  have hbase : (pCoreOf 2 K).relIndex A = 2 :=
    nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hc.core.A_mem_nineOmegaIn
  have hA : (A ⊓ pCoreOf 2 K).relIndex A = 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact hbase
  have hmap := Subgroup.relIndex_map_map_of_injective (H := A ⊓ pCoreOf 2 K) (K := A)
    (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective
  have hleft : (conjSubgroup (A ⊓ pCoreOf 2 K) k).relIndex (conjSubgroup A k) =
      (A ⊓ pCoreOf 2 K).relIndex A := by
    simpa only [CFSG.Quasithin.conjSubgroup] using hmap
  rw [hUk, ← Nine3Core.conjSubgroup_pCoreOf K hk, ← E3.conjSubgroup_inf]
  exact hleft.trans hA

theorem nine3_inf_S_X (hc : Nine3Choice V T A K S X p g x) : S ⊓ X = ⊥ := by
  haveI : Fact (Nat.Prime p) := ⟨hc.core.hyp.base.prime⟩
  rw [inf_comm]
  exact (IsPGroup.disjoint_of_ne p 2 hc.core.hyp.base.odd X S
    hc.core.hyp.base.sylowP.isPGroup hc.core.hyp.base.sylowTwo.isPGroup).eq_bot

theorem nine3_card_K (hc : Nine3Choice V T A K S X p g x) :
    Nat.card K = Nat.card S * p := by
  have hSK : S ≤ K := hc.core.S_le_K
  have hXK : X ≤ K := hc.core.hyp.base.sylowP.le
  have hmul : (K : Set G) = (S : Set G) * (X : Set G) :=
    TwoPTwo.mul_eq hc.core.hyp.base.toTwoPTwo
  have hdisj : S ⊓ X = ⊥ := nine3_inf_S_X hc
  have hcompl : (S.subgroupOf K).IsComplement' (X.subgroupOf K) := by
    rw [Subgroup.isComplement'_def, isComplement_iff_existsUnique]
    intro q
    have hq : (q : G) ∈ (S : Set G) * (X : Set G) := hmul ▸ q.2
    obtain ⟨s, hs, u, hu, hsu⟩ := Set.mem_mul.mp hq
    refine ⟨(⟨⟨s, hSK hs⟩, hs⟩, ⟨⟨u, hXK hu⟩, hu⟩), ?_, ?_⟩
    · apply Subtype.ext
      exact hsu
    · rintro ⟨⟨⟨s', hs'K⟩, hs'⟩, ⟨⟨u', hu'K⟩, hu'⟩⟩ h
      have hmem : (⟨s', hs'K⟩ : ↥K) * ⟨u', hu'K⟩ = ⟨s, hSK hs⟩ * ⟨u, hXK hu⟩ := by
        rw [h]
        apply Subtype.ext
        exact hsu.symm
      have hval : s' * u' = s * u := congrArg Subtype.val hmem
      have heq : s'⁻¹ * s = u' * u⁻¹ := by
        calc s'⁻¹ * s = s'⁻¹ * (s' * u' * u⁻¹) := by rw [hval]; group
          _ = u' * u⁻¹ := by group
      have hmemS : s'⁻¹ * s ∈ S := S.mul_mem (S.inv_mem hs') hs
      have hmemX : s'⁻¹ * s ∈ X := by
        rw [heq]
        exact X.mul_mem hu' (X.inv_mem hu)
      have hbot : s'⁻¹ * s ∈ (⊥ : Subgroup G) := by
        rw [← hdisj]
        exact ⟨hmemS, hmemX⟩
      have h1 : s'⁻¹ * s = 1 := Subgroup.mem_bot.mp hbot
      have hs_eq : s' = s := by
        have h := congrArg (fun x => s' * x) h1
        simpa [mul_assoc] using h.symm
      have hu_eq : u' = u := by
        have h := hval
        rw [hs_eq] at h
        exact mul_left_cancel h
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (Subtype.ext hs_eq)
      · exact Subtype.ext (Subtype.ext hu_eq)
  have hcard := hcompl.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv, hc.core.card] at hcard
  exact hcard.symm

theorem nine3_exists_a_not_mem_pCore (hc : Nine3Choice V T A K S X p g x) :
    ∃ a ∈ A, a ∉ pCoreOf 2 K := by
  by_contra h
  push Not at h
  have hle : A ≤ pCoreOf 2 K := h
  have hrel : (pCoreOf 2 K).relIndex A = 2 :=
    nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hc.core.A_mem_nineOmegaIn
  rw [Subgroup.relIndex_eq_one.mpr hle] at hrel
  omega

theorem nine3_c_mem_sup (hc : Nine3Choice V T A K S X p g x) {a x : G}
    (ha : a ∈ A) (hx : x ∈ X) :
    a * (x⁻¹ * a * x) ∈ pCoreOf 2 K ⊔ X := by
  have haK : a ∈ K := hc.core.S_le_K (hc.core.A_mem_nineOmegaIn.2 ha)
  have hsupK : pCoreOf 2 K ⊔ X ≤ K :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hc.core.hyp.base.sylowP.le
  have hKnorm : K ≤ Subgroup.normalizer ((pCoreOf 2 K ⊔ X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsupK).mp
      (TwoPTwo.normal_pCoreOf_sup hc.core.hyp.base.toTwoPTwo)
  have hle : ⁅K, pCoreOf 2 K ⊔ X⁆ ≤ pCoreOf 2 K ⊔ X :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hKnorm
  have hxP : x⁻¹ ∈ pCoreOf 2 K ⊔ X := Subgroup.mem_sup_right (X.inv_mem hx)
  have hmem : ⁅a, x⁻¹⁆ ∈ ⁅K, pCoreOf 2 K ⊔ X⁆ :=
    Subgroup.commutator_mem_commutator haK hxP
  have ha2 : a * a = 1 := by
    have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1
      hc.core.A_mem_nineOmegaIn.1).2 a ha
    simpa [pow_two] using h
  have hcomm : ⁅a, x⁻¹⁆ = a * (x⁻¹ * a * x) := by
    rw [commutatorElement_def, inv_inv, inv_eq_of_mul_eq_one_left ha2]
    group
  rw [hcomm] at hmem
  exact hle hmem

theorem nine3_c_pow_two_ne_one (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) {a x : G} (ha : a ∈ A) (haR : a ∉ pCoreOf 2 K)
    (hx : x ∈ X) (hx1 : x ≠ 1) :
    ∀ n : ℕ, (a * (x⁻¹ * a * x)) ^ 2 ^ n ≠ 1 := by
  intro n hn
  set c : G := a * (x⁻¹ * a * x) with hcdef
  have hcSup : c ∈ pCoreOf 2 K ⊔ X := nine3_c_mem_sup hc ha hx
  have hcR : c ∈ pCoreOf 2 K :=
    TwoPTwo.mem_pCoreOf_of_mem_sup hc.core.hyp.base.toTwoPTwo hcSup hn
  have hxK : x ∈ K := hc.core.hyp.base.sylowP.le hx
  have hxc : x * c * x⁻¹ ∈ pCoreOf 2 K :=
    (Nine3Core.mem_pCoreOf_conj_iff K hxK).mp hcR
  have ha2 : a * a = 1 := by
    have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1
      hc.core.A_mem_nineOmegaIn.1).2 a ha
    simpa [pow_two] using h
  have hxa : ⁅x, a⁆ ∈ pCoreOf 2 K := by
    have heq : ⁅x, a⁆ = x * c * x⁻¹ := by
      rw [hcdef, commutatorElement_def, inv_eq_of_mul_eq_one_left ha2]
      group
    rwa [heq]
  have hcommA : ∀ b ∈ A, ⁅x, b⁆ ∈ pCoreOf 2 K := by
    intro b hb
    by_cases hbR : b ∈ pCoreOf 2 K
    · have hxbR : x * b * x⁻¹ ∈ pCoreOf 2 K :=
        (Nine3Core.mem_pCoreOf_conj_iff K hxK).mp hbR
      rw [commutatorElement_def]
      exact (pCoreOf 2 K).mul_mem hxbR ((pCoreOf 2 K).inv_mem hbR)
    · have hrel : (A ⊓ pCoreOf 2 K).relIndex A = 2 := by
        rw [inf_comm, Subgroup.inf_relIndex_right]
        exact nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp
          hc.core.A_mem_nineOmegaIn
      have hba : b * a ∈ A ⊓ pCoreOf 2 K := by
        have hbH : (⟨b, hb⟩ : ↥A) ∉ (A ⊓ pCoreOf 2 K).subgroupOf A := by
          intro hmem
          exact hbR (Subgroup.mem_subgroupOf.mp hmem).2
        have haH : (⟨a, ha⟩ : ↥A) ∉ (A ⊓ pCoreOf 2 K).subgroupOf A := by
          intro hmem
          exact haR (Subgroup.mem_subgroupOf.mp hmem).2
        have hmem : (⟨b, hb⟩ * ⟨a, ha⟩ : ↥A) ∈ (A ⊓ pCoreOf 2 K).subgroupOf A := by
          rw [Subgroup.mul_mem_iff_of_index_two hrel]
          exact iff_of_false hbH haH
        exact Subgroup.mem_subgroupOf.mp hmem
      have hbaR : b * a ∈ pCoreOf 2 K := hba.2
      have h1 : ⁅x, b * a⁆ ∈ pCoreOf 2 K :=
        (by
          have hxb : x * (b * a) * x⁻¹ ∈ pCoreOf 2 K :=
            (Nine3Core.mem_pCoreOf_conj_iff K hxK).mp hbaR
          rw [commutatorElement_def]
          exact (pCoreOf 2 K).mul_mem hxb ((pCoreOf 2 K).inv_mem hbaR))
      have h2 : (b * a) * ⁅x, a⁆ * (b * a)⁻¹ ∈ pCoreOf 2 K :=
        (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).mul_mem hbaR hxa)
          ((pCoreOf 2 K).inv_mem hbaR)
      have hb_eq : b = (b * a) * a := by
        have ha2 : a * a = 1 := by
          have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1
            hc.core.A_mem_nineOmegaIn.1).2 a ha
          simpa [pow_two] using h
        rw [mul_assoc, ha2, mul_one]
      rw [hb_eq, commutatorElement_mul_right_eq_mul_conj]
      simpa [mul_assoc] using (pCoreOf 2 K).mul_mem h1 h2
  have hxR : x ∈ pCoreOf 2 K :=
    nine_two_centralizer hc.core.hyp7 hc.core.rk_gt hc.core.hyp
      hc.core.A_mem_nineOmegaIn (Subgroup.mem_sup_right hx) hcommA
  have hxbot : x ∈ X ⊓ pCoreOf 2 K := ⟨hx, hxR⟩
  rw [TwoPTwo.sylowP_inf_pCoreOf hc.core.hyp.base.toTwoPTwo] at hxbot
  exact hx1 (Subgroup.mem_bot.mp hxbot)

theorem nine3_exists_order_p (hc : Nine3Choice V T A K S X p g x)
    {c : G} (hcK : c ∈ K) (hnot : ∀ n : ℕ, c ^ 2 ^ n ≠ 1) :
    ∃ y : G, y ∈ Subgroup.zpowers c ∧ orderOf y = p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime p) := ⟨hc.core.hyp.base.prime⟩
  obtain ⟨n, hnS⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp
    hc.core.hyp.base.sylowTwo.isPGroup
  have hKcard : Nat.card K = Nat.card S * p := nine3_card_K hc
  have hordK : orderOf c ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hcK
  have hordS : ¬ orderOf c ∣ Nat.card S := by
    intro hdvd
    have hc2 : c ^ 2 ^ n = 1 := by
      rw [hnS] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact hnot n hc2
  have hdiv : orderOf c ∣ Nat.card S * p := by rwa [hKcard] at hordK
  have hpord : p ∣ orderOf c := by
    by_contra hp
    have hcop : Nat.Coprime (orderOf c) p := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hc.core.hyp.base.prime).mpr hp
    exact hordS (hcop.dvd_of_dvd_mul_right hdiv)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p (G := ↥(Subgroup.zpowers c))
    (by rwa [Nat.card_zpowers])
  refine ⟨(y : G), y.2, ?_⟩
  rw [← Subgroup.orderOf_mk (y : G) y.2]
  exact hy

end CFSG.LocalAnalysis.WeakClosure81
