module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourCentralizer
public import CFSG.Quasithin.SteinbergCBAlternatingFive

public section

namespace CFSG.Quasithin.Vol2.Ch11.O5

open CFSG.GorensteinWalter

theorem not_le_reflected_join_of_alt5 {G : Type*} [Group G] {U : Subgroup G} {w : G}
    (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    {B : Subgroup G} (eB : ↥B ≃* alternatingGroup (Fin 5)) (hB : B ≤ U ⊔ Subgroup.zpowers w) :
    False := by
  let c₁ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  let c₂ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  have hU : ∀ c : alternatingGroup (Fin 5), c ^ 3 = 1 → c ≠ 1 → ((eB.symm c : B) : G) ∈ U := by
    intro c hc3 hc1
    have hb3 : ((eB.symm c : B) : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hc3, map_one, Subgroup.coe_one]
    rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp (hB (eB.symm c).2) with
      ⟨u, hu, hbu | hbw⟩
    · rwa [hbu]
    · exfalso
      have hsq : ((eB.symm c : B) : G) * ((eB.symm c : B) : G) = 1 := by
        rw [hbw]
        calc (u * w) * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
          _ = 1 := by rw [hwinv u hu, hwsq]; group
      have h1 : ((eB.symm c : B) : G) = 1 := by
        calc ((eB.symm c : B) : G) = ((eB.symm c : B) : G) ^ 3 *
            (((eB.symm c : B) : G) * ((eB.symm c : B) : G))⁻¹ := by group
          _ = 1 := by rw [hb3, hsq]; group
      apply hc1
      apply eB.symm.injective
      rw [map_one]
      exact Subtype.ext h1
  have h₁ := hU c₁ (by decide) (by decide)
  have h₂ := hU c₂ (by decide) (by decide)
  let : CommGroup U := IsCyclic.commGroup
  have hcomm : ((eB.symm c₁ : B) : G) * ((eB.symm c₂ : B) : G) =
      ((eB.symm c₂ : B) : G) * ((eB.symm c₁ : B) : G) :=
    congrArg Subtype.val (mul_comm (⟨_, h₁⟩ : U) ⟨_, h₂⟩)
  have hc : c₁ * c₂ = c₂ * c₁ := by
    apply eB.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext hcomm
  exact absurd hc (by decide)

theorem isKleinFour_sylow_two_alt5 (P : Sylow 2 (alternatingGroup (Fin 5))) :
    IsKleinFour (P : Subgroup (alternatingGroup (Fin 5))) := by
  have hcard := SteinbergCB.nat_card_sylow_two_alternating_five P
  have : Nontrivial (P : Subgroup (alternatingGroup (Fin 5))) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  have h4 : (g : alternatingGroup (Fin 5)) ^ 4 = 1 := by
    have h := pow_card_eq_one' (G := (P : Subgroup (alternatingGroup (Fin 5)))) (x := g)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  have h2 : g ^ 2 = 1 :=
    Subtype.ext (by simpa using SteinbergCB.sq_eq_one_of_pow_four_alternating_five _ h4)
  have hg1 : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact absurd h hg1
  · exact h

theorem exists_kleinFour_le_of_alt5 {G : Type*} [Group G] {B : Subgroup G}
    (eB : ↥B ≃* alternatingGroup (Fin 5)) : ∃ V : Subgroup G, IsKleinFour V ∧ V ≤ B := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (alternatingGroup (Fin 5))))
  have hP := isKleinFour_sylow_two_alt5 P
  let f : alternatingGroup (Fin 5) →* G := B.subtype.comp eB.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp eB.symm.injective
  let eV := Subgroup.equivMapOfInjective (P : Subgroup (alternatingGroup (Fin 5))) f hf
  refine ⟨(P : Subgroup (alternatingGroup (Fin 5))).map f,
    ⟨(Nat.card_congr eV.toEquiv).symm.trans hP.card_four,
      (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hP.exponent_two⟩, ?_⟩
  rintro _ ⟨x, -, rfl⟩
  exact (eB.symm x).2

variable {K : Type} [Field K] [Finite K]

theorem exists_conj_reflected_centralizer (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {t : PGL2 K} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ (U : Subgroup (PGL2 K)) (w h : PGL2 K), IsCyclic U ∧ w ∉ U ∧ w * w = 1 ∧
      (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({h * t * h⁻¹} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w := by
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hqOdd : Odd (Nat.card K) := by
    obtain ⟨q, n, -, hq, -, hn⟩ := hK
    rw [hn]
    exact hq.pow
  set J : Subgroup (PGL2 K) := commutator (PGL2 K) with hJdef
  have hJ : J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  have hJindex : J.index = 2 := by rw [hJ]; exact pgl2_psl2Range_index_eq_two K hK
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨ht1, by rw [pow_two]; exact ht2⟩
  obtain ⟨Ulow, sout, -, wlow, hUlowcyc, hUlowhalf, hUlowcard, -, hsoutJ, hsoutne, hsoutsq, -,
    -, -, -, -, hwlowU, hwlowsq, hwlowInv, hcentlow⟩ :=
    pgl2_low_two_part_torus_reflection_data K hK hcard
  by_cases htJ : t ∈ J
  ·
    obtain ⟨U0, s0, w0, hU0cyc, hs0U, hs0sq, hs0ne, hw0U, hw0sq, hw0inv, hcent0, hU0J, m, hU0two,
        hmeven⟩ : ∃ (U0 : Subgroup (PGL2 K)) (s0 w0 : PGL2 K), IsCyclic U0 ∧ s0 ∈ U0 ∧
        s0 * s0 = 1 ∧ s0 ≠ 1 ∧ w0 ∉ U0 ∧ w0 * w0 = 1 ∧ (∀ x ∈ U0, w0 * x * w0⁻¹ = x⁻¹) ∧
        Subgroup.centralizer ({s0} : Set (PGL2 K)) = U0 ⊔ Subgroup.zpowers w0 ∧ ¬ U0 ≤ J ∧
        ∃ m : ℕ, Nat.card U0 = 2 * m ∧ Even m := by
      rcases hUlowcard with hminus | hplus
      · obtain ⟨U0, s0, w0, hU0cyc, hU0card, hs0U, hs0sq, hs0ne, hw0U, hw0sq, hw0inv, hcent0,
          hU0cross⟩ := pgl2_nonsplit_torus_centralizer_data K hqOdd
        refine ⟨U0, s0, w0, hU0cyc, hs0U, hs0sq, hs0ne, hw0U, hw0sq, hw0inv, hcent0,
          fun hle => hU0cross hqOdd (hJ ▸ hle), (Nat.card K + 1) / 2, ?_, ?_⟩
        · rw [hU0card]
          obtain ⟨a, ha⟩ := hqOdd
          omega
        · have h1 : Odd ((Nat.card K - 1) / 2) := by rwa [hminus] at hUlowhalf
          obtain ⟨a, ha⟩ := h1
          obtain ⟨b, hb⟩ := hqOdd
          exact ⟨a + 1, by omega⟩
      · obtain ⟨U0, s0, w0, hU0cyc, hU0card, hs0U, hs0sq, hs0ne, hw0U, hw0sq, hw0inv, hcent0,
          hU0cross⟩ := pgl2_split_torus_centralizer_data K hqOdd
        refine ⟨U0, s0, w0, hU0cyc, hs0U, hs0sq, hs0ne, hw0U, hw0sq, hw0inv, hcent0,
          fun hle => hU0cross hqOdd (hJ ▸ hle), (Nat.card K - 1) / 2, ?_, ?_⟩
        · rw [hU0card]
          obtain ⟨a, ha⟩ := hqOdd
          omega
        · have h1 : Odd ((Nat.card K + 1) / 2) := by rwa [hplus] at hUlowhalf
          obtain ⟨a, ha⟩ := h1
          obtain ⟨b, hb⟩ := hqOdd
          exact ⟨a, by omega⟩
    have hs0J : s0 ∈ J :=
      pgl2_torus_involution_mem_commutator hJindex U0 hU0cyc hs0U hs0sq hs0ne hU0two hmeven hU0J
    obtain ⟨h, -, hh⟩ := pgl2_inner_involutions_conjugate hK hcard htJ htI hs0J
      ⟨hs0ne, by rw [pow_two]; exact hs0sq⟩
    exact ⟨U0, w0, h, hU0cyc, hw0U, hw0sq, hw0inv, by rw [hh, hcent0]⟩
  · obtain ⟨h, hh⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate K hK hcard htI
      ⟨hsoutne, by rw [pow_two]; exact hsoutsq⟩ htJ hsoutJ)
    exact ⟨Ulow, wlow, h, hUlowcyc, hwlowU, hwlowsq, hwlowInv, by rw [hh, hcentlow]⟩

theorem eq_one_of_commute_alt5 (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {B : Subgroup (PGL2 K)} (eB : ↥B ≃* alternatingGroup (Fin 5)) {g : PGL2 K}
    (hg : ∀ b ∈ B, g * b = b * g) : g = 1 := by
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  by_contra hg1
  have ho : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd ho
  set g' := g ^ (orderOf g / r) with hg'
  have hg'r : orderOf g' = r := orderOf_pow_orderOf_div (orderOf_pos g).ne' hrd
  have hg'1 : g' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hg'r
    exact hr.one_lt.ne hg'r
  have hg'B : ∀ b ∈ B, g' * b = b * g' := fun b hb => ((Commute.pow_left (hg b hb)) _).eq
  rcases hr.eq_two_or_odd' with rfl | hrodd
  ·
    have hg'2 : g' * g' = 1 := by
      have h := pow_orderOf_eq_one g'
      rw [hg'r, pow_two] at h
      exact h
    obtain ⟨U, w, h, hUcyc, hwU, hwsq, hwinv, hcent⟩ :=
      exists_conj_reflected_centralizer hK hcard hg'1 hg'2
    let c : PGL2 K ≃* PGL2 K := MulAut.conj h
    refine not_le_reflected_join_of_alt5 hUcyc hwU hwsq hwinv
      ((B.equivMapOfInjective c.toMonoidHom c.injective).symm.trans eB) ?_
    rintro _ ⟨b, hb, rfl⟩
    rw [← hcent, Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, c, MulAut.conj_apply]
    calc h * b * h⁻¹ * (h * g' * h⁻¹) = h * (b * g') * h⁻¹ := by group
      _ = h * (g' * b) * h⁻¹ := by rw [hg'B b hb]
      _ = h * g' * h⁻¹ * (h * b * h⁻¹) := by group
  ·
    obtain ⟨V, hVK, hVB⟩ := exists_kleinFour_le_of_alt5 eB
    refine pgl2_no_kleinFour_centralizes_odd_cyclic K hK (Subgroup.zpowers g') V
      inferInstance ?_ ?_ hVK ?_
    · exact (Subgroup.zpowers_ne_bot).mpr hg'1
    · rw [Nat.card_zpowers, hg'r]
      exact hrodd
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_left (hg'B v (hVB hv)) k)).eq

end CFSG.Quasithin.Vol2.Ch11.O5
