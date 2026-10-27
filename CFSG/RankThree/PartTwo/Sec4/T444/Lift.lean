module

public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

section General

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem le_normalizer_of_subgroupOf_normal {H K : Subgroup X} (hHK : H ≤ K)
    (hN : (H.subgroupOf K).Normal) : K ≤ Subgroup.normalizer (H : Set X) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := hN.conj_mem ⟨h, hHK hh⟩ (Subgroup.mem_subgroupOf.mpr hh) ⟨k, hk⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hh
    have := hN.conj_mem ⟨k * h * k⁻¹, hHK hh⟩ (Subgroup.mem_subgroupOf.mpr hh) ⟨k⁻¹, inv_mem hk⟩
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this

theorem inSubgroup_pPrimeCore_le_of_isSubnormal {H : Subgroup X} (hH : H.IsSubnormal) :
    inSubgroup (CFSG.pPrimeCore 3) H ≤ CFSG.pPrimeCore 3 X := by
  induction hH with
  | top => exact (CFSG.pPrimeCore_map_iso 3 (Subgroup.topEquiv (G := X))).le
  | step H K hHK _ hN ih =>
    refine le_trans ?_ ih
    refine le_inSubgroup_pPrimeCore ((Subgroup.map_subtype_le _).trans hHK) ?_
      (not_three_dvd_card_inSubgroup_pPrimeCore H)
    exact (le_normalizer_of_subgroupOf_normal hHK hN).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pPrimeCore 3 H))

theorem le_pPrimeCore_of_isSubnormal {H : Subgroup X} (hH : H.IsSubnormal)
    (h3 : ¬ 3 ∣ Nat.card H) : H ≤ CFSG.pPrimeCore 3 X := by
  have htop : CFSG.pPrimeCore 3 H = ⊤ := eq_top_iff.mpr (le_sSup ⟨inferInstance, by
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩)
  have hH' : inSubgroup (CFSG.pPrimeCore 3) H = H := by
    rw [inSubgroup, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hH']
  exact inSubgroup_pPrimeCore_le_of_isSubnormal hH

theorem le_aschbacherSolvableCore_of_isSubnormal {T : Subgroup X} (hT : T.IsSubnormal)
    (hs : Group.IsSolvable T) (h3 : ¬ 3 ∣ Nat.card T) : T ≤ aschbacherSolvableCore 3 X := by
  have h := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hT
  have htop : aschbacherSolvableCore 3 T = ⊤ := by
    refine eq_top_iff.mpr ((solvable_prime_complement_core_characterization
      Nat.prime_three).2.2.2.1 ⊤ inferInstance ?_ ?_)
    · exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    · rwa [Subgroup.card_top]
  have hT' : inSubgroup (aschbacherSolvableCore 3) T = T := by
    rw [inSubgroup, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hT'] at h
  rw [h]
  exact inf_le_right

theorem three_dvd_card_of_isComponent (hX : CFSG.pPrimeCore 3 X = ⊥) {J : Subgroup X}
    (hJ : IsComponent J) : 3 ∣ Nat.card J := by
  by_contra h3
  have hle := le_pPrimeCore_of_isSubnormal hJ.2 h3
  rw [hX, le_bot_iff] at hle
  subst hle
  have := isQuasisimple_nontrivial hJ.1
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl

end General

section Star

variable {G : Type} [Group G] [Finite G]

theorem aschbacherSolvableCore_le_pPrimeCore :
    aschbacherSolvableCore 3 G ≤ CFSG.pPrimeCore 3 G :=
  le_pPrimeCore_of_normal inferInstance
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1

theorem inf_pPrimeCore_eq_of_mem_thetaComponents {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L) :
    L ⊓ CFSG.pPrimeCore 3 G = inSubgroup (aschbacherSolvableCore 3) L := by
  have hθL := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL.2.1
  apply le_antisymm
  · set θL := aschbacherSolvableCore 3 L with hθLdef
    set N : Subgroup L := (CFSG.pPrimeCore 3 G).subgroupOf L with hN
    have hNn : N.Normal := Subgroup.normal_subgroupOf
    have hN3 : ¬ 3 ∣ Nat.card N := by
      intro h
      apply not_three_dvd_card_pPrimeCore (G := G)
      have hle : N.map L.subtype ≤ CFSG.pPrimeCore 3 G := by
        rintro _ ⟨x, hx, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hx
      rw [← Subgroup.card_map_of_injective L.subtype_injective] at h
      exact h.trans (Subgroup.card_dvd_of_le hle)
    set π := QuotientGroup.mk' θL
    have hNmap : (N.map π).Normal := hNn.map π (QuotientGroup.mk'_surjective θL)
    have hθ3 : ¬ 3 ∣ Nat.card θL :=
      (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
    have hle : N ≤ θL := by
      rcases quasisimple_normal_subgroups hL.2.2 hNmap with htop | hcen
      · exfalso
        apply hN3
        have hq : 3 ∣ Nat.card (L ⧸ θL) := by
          have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup θL
          rw [hmul] at h3
          exact (Nat.Prime.dvd_mul Nat.prime_three).mp h3 |>.resolve_right hθ3
        rw [← Subgroup.card_top (G := L ⧸ θL), ← htop] at hq
        exact hq.trans (Subgroup.card_map_dvd N π)
      · have hsolv : Group.IsSolvable (N.map π) := by
          refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
          change (a : L ⧸ θL) * b = b * a
          exact Subgroup.mem_center_iff.mp (hcen b.2) a
        have hcop : ¬ 3 ∣ Nat.card (N.map π) := fun h => hN3 (h.trans (Subgroup.card_map_dvd N π))
        have hθ := (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.1
          (N.map π) hNmap hsolv hcop
        rw [(theta_quotient_core_and_ranks (G := L)).1, le_bot_iff, Subgroup.map_eq_bot_iff,
          QuotientGroup.ker_mk'] at hθ
        exact hθ
    intro x hx
    exact ⟨⟨x, hx.1⟩, hle (Subgroup.mem_subgroupOf.mpr hx.2), rfl⟩
  · rw [hθL]
    exact inf_le_inf_left _ aschbacherSolvableCore_le_pPrimeCore

theorem exists_thetaQuot_equiv_map_starQuot {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (h3 : 3 ∣ Nat.card L) :
    ∃ η : L ⧸ aschbacherSolvableCore 3 L ≃* L.map (starQuot G),
      ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ CFSG.pPrimeCore 3 G) =
        starQuot G l := by
  have heq := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3
  refine exists_quotient_mulEquiv_map (starQuot G) L _ fun l => ?_
  rw [starQuot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hl
    have hmem : (l : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨l, hl, rfl⟩
    rw [← heq] at hmem
    exact hmem.2
  · intro hl
    have hmem : (l : G) ∈ L ⊓ CFSG.pPrimeCore 3 G := ⟨l.2, hl⟩
    rw [heq] at hmem
    obtain ⟨l', hl', he⟩ := hmem
    rwa [← Subtype.ext he]

theorem isComponent_map_starQuot {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (h3 : 3 ∣ Nat.card L) : IsComponent (L.map (starQuot G)) := by
  obtain ⟨η, -⟩ := exists_thetaQuot_equiv_map_starQuot hL h3
  exact ⟨isQuasisimple_of_mulEquiv η hL.2.2, hL.2.1.map (QuotientGroup.mk'_surjective _)⟩

omit [Finite G] in
theorem map_derivedSeries_eq_of_isPerfect {Z : Type*} [Group Z] (f : G →* Z) {C : Subgroup G}
    {J : Subgroup Z} [hJ : Group.IsPerfect J] (hCJ : C.map f = J) (n : ℕ) :
    ((derivedSeries C n).map C.subtype).map f = J := by
  induction n with
  | zero => rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hCJ]
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator, Subgroup.map_commutator, ih,
      Subgroup.commutator_eq_self]

theorem exists_perfect_isSubnormal_map_eq {J : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)}
    (hJ : IsComponent J) :
    ∃ L : Subgroup G, Group.IsPerfect L ∧ L.IsSubnormal ∧ L.map (starQuot G) = J := by
  set C := J.comap (starQuot G) with hC
  have hCJ : C.map (starQuot G) = J :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J
  obtain ⟨⟨n, hn, -⟩, hchar, hperf, -⟩ := perfect_residual_characterization (G := C)
  have : Group.IsPerfect J := hJ.1.1
  refine ⟨(perfectResidual C).map C.subtype, isPerfect_map_subtype hperf, ?_, ?_⟩
  · refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) ?_ (hJ.2.comap _)
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact (Subgroup.normal_of_characteristic _).isSubnormal
  · rw [hn]
    exact map_derivedSeries_eq_of_isPerfect (starQuot G) hCJ n

end Star

end CFSG.RankThree.PartTwo.Sec4
