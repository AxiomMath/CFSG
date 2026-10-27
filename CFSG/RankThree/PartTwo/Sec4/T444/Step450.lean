module

public import CFSG.RankThree.PartTwo.Sec4.T444.LiftMin
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)

section General

variable {X : Type*} [Group X] [Finite X]

theorem fittingSubgroup_le_pCore_three_of_pPrimeCore_eq_bot (hX : CFSG.pPrimeCore 3 X = ⊥) :
    fittingSubgroup X ≤ CFSG.pCore 3 X := by
  rw [fitting_eq_sup_pCore X]
  refine iSup_le fun p => ?_
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  by_cases hp3 : p.1.1 = 3
  · rw [hp3]
  · have : Fact p.1.1.Prime := ⟨hp⟩
    have hle : CFSG.pCore p.1.1 X ≤ CFSG.pPrimeCore 3 X := by
      refine le_pPrimeCore_of_normal CFSG.pCore_normal fun h3 => hp3 ?_
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p.1.1) (G := X))
      rw [hk] at h3
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    rw [hX, le_bot_iff] at hle
    rw [hle]
    exact bot_le

theorem eq_bot_of_le_centralizer_of_pPrimeCore_eq_bot (hX : CFSG.pPrimeCore 3 X = ⊥)
    {Q : Subgroup X} (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hO : Q ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X))
    (hE : ∀ J : Subgroup X, IsComponent J → Q ≤ Subgroup.centralizer (J : Set X)) : Q = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := fittingSubgroup_le_pCore_three_of_pPrimeCore_eq_bot hX
  have hQF : Q ≤ Subgroup.centralizer (generalizedFitting X : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ((hF.trans ?_)) (sSup_le fun J hJ => ?_)
    · exact Subgroup.le_centralizer_iff.mp hO
    · exact Subgroup.le_centralizer_iff.mp (hE J hJ)
  set Zs := generalizedFitting X ⊓ Subgroup.centralizer (generalizedFitting X : Set X) with hZs
  have hQZ : Q ≤ Zs := le_inf (hQF.trans (centralizer_generalizedFitting_le X)) hQF
  have hFn : (generalizedFitting X).Normal := generalized_fitting_characteristic.2
  have hZn : Zs.Normal := by
    have : (Subgroup.centralizer (generalizedFitting X : Set X)).Normal :=
      Subgroup.normal_centralizer (H := generalizedFitting X)
    exact Subgroup.normal_inf_normal _ _
  have hZc : IsMulCommutative Zs := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp b.2.2 _ a.2.1)⟩⟩
  have hZF : Zs ≤ fittingSubgroup X := le_sSup ⟨hZn, inferInstance⟩
  have hQp : IsPGroup 3 Q :=
    (CFSG.pCore_isPGroup (p := 3) (G := X)).to_le (hQZ.trans (hZF.trans hF))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exact absurd (by rw [hk]; exact dvd_pow_self 3 (Nat.succ_ne_zero k)) hQ3

end General

section Star

variable {G : Type} [Group G] [Finite G]

theorem localRank_theta_quotient_le (h : SectionFourHyp G) :
    ∀ s : ℕ, s.Prime → 3 < s → localRank s (G ⧸ aschbacherSolvableCore 3 G) ≤ 3 := by
  have he : CFSG.twoLocalOddRank G ≤ 3 := by
    rw [← OddKernel.evenRank_eq_twoLocalOddRank]
    exact h.evenRank_le
  have hr : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2 := fun r hr h3 =>
    Nat.lt_succ_iff.mp (h.localRank_lt r hr h3)
  obtain ⟨-, -, -, -, -, -, hbound⟩ :=
    OddKernel.rank_three_three_complement_quotient_sharp_local_bounds_theta he hr
  exact fun s hs hs3 => (hbound s hs hs3).2

theorem commutator_eq_self_of_not_le_centralizer {L Q : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hne : ¬ Q.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    ⁅L, Q⁆ = L := by
  set π := starQuot G with hπ
  set J := L.map π with hJdef
  set Qs := Q.map π with hQsdef
  have hJ := isComponent_map_starQuot hL h3
  have : Group.IsPerfect J := hJ.1.1
  have hQJ : Qs ≤ Subgroup.normalizer (J : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    (Subgroup.map_mono hQL).trans (Subgroup.le_normalizer_map π)
  have hDJ : ⁅J, Qs⁆ ≤ J := Subgroup.le_normalizer_iff_commutator_le_left.mp hQJ
  have hJD : J ≤ Subgroup.normalizer
      ((⁅J, Qs⁆ : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    Subgroup.normalizer_commutator_ge_left J Qs
  have hDn : ((⁅J, Qs⁆ : Subgroup _).subgroupOf J).Normal :=
    ⟨fun x hx j => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hJD j.2) _).mp hx⟩
  have hDeq : ⁅J, Qs⁆ = J := by
    rcases quasisimple_normal_subgroups hJ.1 hDn with htop | hcen
    · refine le_antisymm hDJ fun j hj => ?_
      have : (⟨j, hj⟩ : J) ∈ (⁅J, Qs⁆ : Subgroup _).subgroupOf J := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    · exfalso
      apply hne
      have hDC : ⁅J, Qs⁆ ≤ Subgroup.centralizer (J : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hxc := Subgroup.mem_center_iff.mp
          (hcen (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hDJ hx⟩ : J) ∈ _)) ⟨j, hj⟩
        exact congrArg Subtype.val hxc
      have h1 : ⁅⁅J, Qs⁆, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDC
      have h2 : ⁅⁅Qs, J⁆, J⁆ = ⊥ := by rw [Subgroup.commutator_comm Qs J]; exact h1
      have h := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
      rw [Subgroup.commutator_eq_self] at h
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h
  set D := ⁅L, Q⁆ with hD
  have hDL : D ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hQL
  have hLND : L ≤ Subgroup.normalizer (D : Set G) := Subgroup.normalizer_commutator_ge_left L Q
  have hθ := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3
  have hLDθ : ∀ l ∈ L, ∃ d ∈ D, d⁻¹ * l ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro l hl
    have hlJ : π l ∈ D.map π := by
      rw [hD, Subgroup.map_commutator, hDeq]
      exact Subgroup.mem_map_of_mem π hl
    obtain ⟨d, hd, hdl⟩ := hlJ
    refine ⟨d, hd, ?_⟩
    rw [← hθ]
    refine ⟨L.mul_mem (L.inv_mem (hDL hd)) hl, ?_⟩
    have : π (d⁻¹ * l) = 1 := by rw [map_mul, map_inv, hdl, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  set D' : Subgroup L := D.subgroupOf L with hD'
  have hD'n : D'.Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hLND l.2) _).mp hx⟩
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' D').comp (aschbacherSolvableCore 3 L).subtype) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨d, hd, ht⟩ := hLDθ x x.2
      obtain ⟨t, htθ, hte⟩ := ht
      refine ⟨⟨t, htθ⟩, ?_⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      have htx : (t : G) = d⁻¹ * x := hte
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, htx, mul_inv_rev, inv_inv]
      have h := (Subgroup.mem_normalizer_iff.mp (hLND (L.inv_mem x.2)) d).mp hd
      rw [inv_inv] at h
      simpa [mul_assoc] using h
  have hsolvθ : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have hsolv : Group.IsSolvable (L ⧸ D') := Group.isSolvable_of_surjective hsurj
  have : Group.IsPerfect L := hL.1
  have hsub : Subsingleton (L ⧸ D') := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable (L ⧸ D') hsolv
  have hD'top : D' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : (x : L ⧸ D') = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp this
  refine le_antisymm hDL fun l hl => ?_
  have : (⟨l, hl⟩ : L) ∈ D' := hD'top ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem rank3II_4_50_of (hSz : KFacts.KPSz) (h447 : Item4_47) : Item4_50 := by
  intro G _ _ A M h hor
  set π := starQuot G with hπ
  set Q := inSubgroup (CFSG.pPrimeCore 3) M with hQ
  set Qs := Q.map π with hQs
  have hQsne : Qs ≠ ⊥ := map_starQuot_ne_bot_iff.mpr (h.not_le_pPrimeCore hor)
  have hX : CFSG.pPrimeCore 3 (G ⧸ CFSG.pPrimeCore 3 G) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hQs3 : ¬ 3 ∣ Nat.card Qs := fun h3 =>
    not_three_dvd_card_inSubgroup_pPrimeCore M (h3.trans (Subgroup.card_map_dvd _ _))
  have h48 := rank3II_4_48 G A M h
  obtain ⟨J, hJ, hJQ⟩ : ∃ J : Subgroup (G ⧸ CFSG.pPrimeCore 3 G), IsComponent J ∧
      ¬ Qs ≤ Subgroup.centralizer (J : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    by_contra hno
    push Not at hno
    exact hQsne (eq_bot_of_le_centralizer_of_pPrimeCore_eq_bot hX hQs3 h48 hno)
  obtain ⟨L, hL, hLJ⟩ := exists_mem_thetaComponents_map_eq hSz h.sectionFourHyp.kGroup
    (localRank_theta_quotient_le h.sectionFourHyp) hJ
  have h3J := three_dvd_card_of_isComponent hX hJ
  have h3L : 3 ∣ Nat.card L := h3J.trans (hLJ ▸ Subgroup.card_map_dvd L π)
  have hLM : ¬ L ≤ M := by
    intro hLM
    set Ms := M.map π with hMs
    have hJM : J ≤ Ms := hLJ ▸ Subgroup.map_mono hLM
    have hQM : Qs ≤ Ms := Subgroup.map_mono (Subgroup.map_subtype_le _)
    have hcomp := component_overgroup hJ hJM
    have hQn : (Qs.subgroupOf Ms).Normal := by
      refine ⟨fun x hx m => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨m', hm', hm'e⟩ := m.2
      have hmn : (m : G ⧸ CFSG.pPrimeCore 3 G) ∈
          Subgroup.normalizer (Qs : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
        rw [← hm'e]
        exact Subgroup.le_normalizer_map π
          (Subgroup.mem_map_of_mem π (le_normalizer_inSubgroup_pPrimeCore M hm'))
      exact (Subgroup.mem_normalizer_iff.mp hmn _).mp hx
    rcases component_normal_subgroup hcomp hQn with hle | hcomm
    · apply hQs3
      have hJQs : J ≤ Qs := fun j hj => Subgroup.mem_subgroupOf.mp
        (hle (Subgroup.mem_subgroupOf.mpr hj : (⟨j, hJM hj⟩ : Ms) ∈ J.subgroupOf Ms))
      exact h3J.trans (Subgroup.card_dvd_of_le hJQs)
    · apply hJQ
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
        (Subgroup.mem_subgroupOf.mpr hj : (⟨j, hJM hj⟩ : Ms) ∈ J.subgroupOf Ms)
      have := Subgroup.mem_centralizer_iff.mp hc ⟨q, hQM hq⟩ (Subgroup.mem_subgroupOf.mpr hq)
      exact (congrArg Subtype.val this).symm
  have hQL := h447 G A M h L hL hLM
  exact ⟨L, hL, hQL, commutator_eq_self_of_not_le_centralizer hL h3L hQL (hLJ ▸ hJQ), hLM⟩

end Star

end CFSG.RankThree.PartTwo.Sec4
