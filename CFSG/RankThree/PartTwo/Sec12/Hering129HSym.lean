module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HDefs
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartTwo.Sec12.Item127
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofHJL0

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Sym

variable {G : Type} [Group G] [Finite G]

theorem not_mem_thetaQuotCentralizer_of_comm_eq {x c : G} {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 x) (hYc : ⁅Y, Subgroup.zpowers c⁆ = Y) :
    c ∉ Sec4.thetaQuotCentralizer Y := by
  intro hcR
  have hzY : Subgroup.zpowers c ≤ Sec4.thetaQuotCentralizer Y := Subgroup.zpowers_le.mpr hcR
  have hle : ⁅Y, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
    refine Subgroup.commutator_le.mpr fun l hl g hg => ?_
    have := (Sec6.mem_thetaQuotCentralizer_iff.mp (hzY hg)).2 l⁻¹ (Y.inv_mem hl)
    simpa [commutatorElement_def, mul_assoc] using this
  rw [hYc] at hle
  exact Sec6.theta_ne_of_mem_thetaComponentsAt hY (le_antisymm (Sec6.theta_le Y) hle)

theorem resCent_le_of_core (h48 : Sec4.Item4_8) {A L K S : Subgroup G} {c b a : G}
    (cfg : Cfg129 G A c L b a K S) {x : G} (hxD : x ∈ D129 a b)
    (hxb : x ∉ Subgroup.zpowers b) (hcX : c ∈ resCent K x)
    (hq : IsQuasisimple (↥(resCent K x) ⧸ aschbacherSolvableCore 3 ↥(resCent K x)))
    {Y : Subgroup G} (hY : Core129 A c x Y) : resCent K x ≤ Y := by
  have hstd := cfg.std
  have hAF : A ∈ partTwoF G := hstd.partTwoF_eq ▸ cfg.mem_E
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hG4x : SectionFourHyp (Subgroup.centralizer ({x} : Set G)) :=
    (Proof128.centralizer_setup hstd.toPartTwoStanding hAF hstd.isE27.2 hxA hx1).1
  obtain ⟨Yx, hYx, hXYx⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4x hstd.isE27
    hbA hxA hb1 cfg.hK hq
  by_cases hYY : Yx = Y
  · exact hYY ▸ hXYx
  · exfalso
    have hcYx : c ∈ Yx := hXYx hcX
    have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hY.2.1 hstd.mem_A
    exact not_mem_thetaQuotCentralizer_of_comm_eq hY.1 hY.2.2.2
      (mem_thetaQuotCentralizer_of_ne hYx hY.1 hYY hcYx hcN)

theorem sym_core (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A L K S : Subgroup G} {c b a : G}
    (cfg : Cfg129 G A c L b a K S) {x : G} (hxD : x ∈ D129 a b)
    (hxb : x ∉ Subgroup.zpowers b) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 x)
    (hD : SymData129 A c x Y) :
    ∃ J : Subgroup G, J ∈ thetaComponentsAt 3 c ∧ resCent Y c ≤ J ∧ J ≠ L ∧
      J = resCent Y c ⊔ inSubgroup (aschbacherSolvableCore 3) J ∧
      A ⊓ Sec4.thetaQuotCentralizer J = A ⊓ L ∧ x ∈ L ∧ b ∈ J ∧
      A ≤ Subgroup.normalizer (J : Set G) ∧
      inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({x} : Set G)) = resCent Y c ∧
      ∃ j ∈ A ⊓ J, j ∉ A ⊓ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hAF : A ∈ partTwoF G := hstd.partTwoF_eq ▸ cfg.mem_E
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hcA := hstd.mem_A
  have hc1 := hstd.ne_one
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hxB := cfg.not_mem_B_of_mem_D hxD hxb
  have hL := hstd.mem_thetaComponentsAt
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcB : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hstd.mem_L hLc
  have hxc : x ∉ Subgroup.zpowers c := fun h =>
    hxB ((Subgroup.zpowers_le.mpr hcB) h)
  set I := resCent Y c with hI
  have hIY : I ≤ Y := (resCent_le Y c).trans inf_le_left
  have hIC : I ≤ Subgroup.centralizer ({c} : Set G) := (resCent_le Y c).trans inf_le_right
  have hYx : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  have hxI : ∀ i ∈ I, x * i = i * x := fun i hi =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hYx (hIY hi))).symm
  have hcI' : ∀ i ∈ I, c * i = i * c := fun i hi =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hIC hi)).symm
  have hIp := isPerfect_resCent Y c
  have hI1 : I ≠ ⊥ := fun h0 =>
    hc1 (Subgroup.mem_bot.mp ((h0 ▸ hD.mem : c ∈ (⊥ : Subgroup G))))
  obtain ⟨j, hjAI, hjU⟩ := hD.exists_j
  have hjA : j ∈ A := hjAI.1
  have hjI : j ∈ I := hjAI.2
  have hj1 : j ≠ 1 := fun h => hjU (h ▸ Subgroup.one_mem _)
  set U := Subgroup.zpowers x ⊔ Subgroup.zpowers c with hU
  have hU9 : Nat.card U = 9 := Proof128.card_zpowers_sup_eq_nine hAe hcA hxA hc1 hx1 hxc
  have hUA : U ≤ A := sup_le (Subgroup.zpowers_le.mpr hxA) (Subgroup.zpowers_le.mpr hcA)
  have hxU : x ∈ U := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hAL9 := card_inf_eq_nine_of_list hstd cfg.list
  have hG4c : SectionFourHyp (Subgroup.centralizer ({c} : Set G)) :=
    (Proof128.centralizer_setup hstd.toPartTwoStanding hAF hA27 hcA hc1).1
  have hG4x : SectionFourHyp (Subgroup.centralizer ({x} : Set G)) :=
    (Proof128.centralizer_setup hstd.toPartTwoStanding hAF hA27 hxA hx1).1
  obtain ⟨J, hJ, hIJ⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4c hstd.isE27 hxA
    hcA hx1 hY hD.quasi
  have hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun y hy =>
    mem_normalizer_zpowers_of_commute (hAc y hy c hcA)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hstd.toTheoremFourHyp
      (orderOf_eq_prime hc3 hc1) hJ hA3 hAH
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hstd.toTheoremFourHyp
      (orderOf_eq_prime hc3 hc1) hL hA3 hAH
  have hker : ∀ g ∈ A, g ∈ Sec4.thetaQuotCentralizer J → g ∈ U := fun g hg hgJ =>
    mem_sup_of_mem_thetaQuotCentralizer hAe hA27 hxA hcA hjA hx1 hc1 hxc hjU hIJ hjI hD.mem
      hxI hcI' hD.card_center hg hgJ
  have hJL : J ≠ L := by
    rintro rfl
    have hBU : A ⊓ Sec4.thetaQuotCentralizer J ≤ U := fun g hg => hker g hg.1 hg.2
    have hBeq : A ⊓ Sec4.thetaQuotCentralizer J = U :=
      Subgroup.eq_of_le_of_card_ge hBU (by rw [hstd.card_B, hU9])
    exact hxB (hBeq ▸ hxU).2
  have hALJ : A ⊓ L ≤ A ⊓ Sec4.thetaQuotCentralizer J := fun g hg =>
    ⟨hg.1, mem_thetaQuotCentralizer_of_ne hL hJ (Ne.symm hJL) hg.2 (hAJ hg.1)⟩
  have hALU : A ⊓ L ≤ U := fun g hg => hker g hg.1 (hALJ hg).2
  have hALeq : A ⊓ L = U := Subgroup.eq_of_le_of_card_ge hALU (by rw [hAL9, hU9])
  have hxL : x ∈ L := (hALeq ▸ hxU : x ∈ A ⊓ L).2
  have hCeq : A ⊓ Sec4.thetaQuotCentralizer J = A ⊓ L :=
    le_antisymm (fun g hg => hALeq ▸ hker g hg.1 hg.2) hALJ
  have hxJ : x ∈ Sec4.thetaQuotCentralizer J := (hALJ ⟨hxA, hxL⟩).2
  have hJc : J ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hJq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hJ
  have hJ' := Proof128.eq_residual_sup_theta hJq.1 (k := 1) (by simpa using hx3) hxJ
  set J' := inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({x} : Set G)) with hJ'def
  have hJ'J : J' ≤ J := (Subgroup.map_subtype_le _).trans inf_le_left
  obtain ⟨eJ⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hJ'J hJ'
  have hJ'q : IsQuasisimple (↥J' ⧸ aschbacherSolvableCore 3 ↥J') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm hJq
  obtain ⟨Y', hY', hJ'Y'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4x hstd.isE27
    hcA hxA hc1 hJ hJ'q
  have hIJ' : I ≤ J' :=
    le_inSubgroup_perfectResidual_of_isPerfect (le_inf hIJ (hIY.trans hYx)) hIp
  have hYY' : Y' = Y :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt
      Nat.prime_three hY' hY hI1 hIp (hIJ'.trans hJ'Y') hIY
  have hJ'I : J' ≤ I := by
    have hp : Group.IsPerfect J' := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact le_inSubgroup_perfectResidual_of_isPerfect
      (le_inf (hYY' ▸ hJ'Y') (hJ'J.trans hJc)) hp
  have hJeq : J = I ⊔ inSubgroup (aschbacherSolvableCore 3) J := by
    apply le_antisymm
    · calc J = J' ⊔ inSubgroup (aschbacherSolvableCore 3) J := hJ'
        _ ≤ I ⊔ inSubgroup (aschbacherSolvableCore 3) J := sup_le_sup_right hJ'I _
    · exact sup_le hIJ (Subgroup.map_subtype_le _)
  have hjJ : j ∈ J := hIJ hjI
  have hcJ : c ∈ J := hIJ hD.mem
  have hjL : j ∈ Sec4.thetaQuotCentralizer L :=
    mem_thetaQuotCentralizer_of_ne hJ hL hJL hjJ (hAL hjA)
  have hjc : j ∉ Subgroup.zpowers c := fun h => hjU (Subgroup.mem_sup_right h)
  have hjc9 : Nat.card (Subgroup.zpowers j ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
    Proof128.card_zpowers_sup_eq_nine hAe hcA hjA hc1 hj1 hjc
  have hjcB : Subgroup.zpowers j ⊔ Subgroup.zpowers c ≤ A ⊓ Sec4.thetaQuotCentralizer L :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hjA, hjL⟩) (Subgroup.zpowers_le.mpr ⟨hcA, hcB⟩)
  have hjcBeq : Subgroup.zpowers j ⊔ Subgroup.zpowers c = A ⊓ Sec4.thetaQuotCentralizer L :=
    Subgroup.eq_of_le_of_card_ge hjcB (by rw [hstd.card_B, hjc9])
  have hbJ : b ∈ J := by
    have hbB : b ∈ A ⊓ Sec4.thetaQuotCentralizer L := cfg.hb
    rw [← hjcBeq] at hbB
    exact (sup_le (Subgroup.zpowers_le.mpr hjJ) (Subgroup.zpowers_le.mpr hcJ)) hbB
  exact ⟨J, hJ, hIJ, hJL, hJeq, hCeq, hxL, hbJ, hAJ, le_antisymm hJ'I hIJ',
    ⟨j, ⟨hjA, hjJ⟩, fun h => hjU (hALeq ▸ h)⟩⟩

end Sym

end CFSG.RankThree.PartTwo.Sec12
