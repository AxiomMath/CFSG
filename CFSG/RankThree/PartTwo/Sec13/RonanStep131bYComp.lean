module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan
public import CFSG.RankThree.PartTwo.Sec4.Item463Proof
import CFSG.RankThree.PartTwo.Sec4.Item422Proof

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Main


theorem exists_component_list (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (hKF : KFacts.OutFixCentralThreeAbelian46Rank) (h49 : Sec4.Item4_9) (h47 : Sec4.Item4_7W)
    (h423 : Sec4.Item4_23) (hAlt : Sec4.Step463Alt)
    {G : Type} [Group G] [Finite G] (hS4 : SectionFourHyp G) {A : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) {z a : G} (hzA : z ∈ A) (hzZ : z ∈ Subgroup.center G) (hz1 : z ≠ 1)
    (haA : a ∈ A) (haz : a ∉ Subgroup.zpowers z)
    (hodd : Odd (Nat.card (aschbacherSolvableCore 3 G)))
    (hev : 2 ∣ Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)), A⁆ : Subgroup G)) :
    ∃ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G) ∧
      Nat.card (Sec4.autThetaQuot A L) = 9 ∧
      thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf (Sec4.autThetaQuot ⊤ L)) ≠ ⊥ ∧
      List463 L := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hz3 : orderOf z = 3 := orderOf_eq_prime (hAe.2 z hzA) hz1
  have ha1 : a ≠ 1 := fun h => haz (h ▸ Subgroup.one_mem _)
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hza : z ∉ Subgroup.zpowers a := by
    intro hza
    have hle : Subgroup.zpowers z ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hza
    have heq : Subgroup.zpowers z = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hz3])
    exact haz (heq ▸ Subgroup.mem_zpowers a)
  set B := Subgroup.zpowers a ⊔ Subgroup.zpowers z with hBdef
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hzA)
  have hzB : z ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have haB : a ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hB9 : Nat.card B = 9 := by
    rw [hBdef, Sec4.Item462Proof.card_sup_zpowers_of_not_mem hzZ hz3 hza, Nat.card_zpowers, ha3]
  have hCB : Subgroup.centralizer (B : Set G) = Subgroup.centralizer ({a} : Set G) := by
    refine le_antisymm (Subgroup.centralizer_le (by simpa using haB)) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ?_ ((Subgroup.zpowers_le.mpr hzZ).trans (Subgroup.center_le_centralizer _))
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_singleton_iff).mp hx).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hBx hy)
  set H := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) with hHdef
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := hAa.trans (Sec6.le_normalizer_theta _)
  obtain ⟨hHs, hH3⟩ := Sec4.Item422Proof.inSubgroup_theta_solvable_coprime
    (Subgroup.centralizer ({a} : Set G))
  obtain ⟨U, hUle, hU2, hU1, hAU, hUA⟩ :=
    Sec4.Item463Proof.exists_isPGroup_two_le_commutator hAp hH3 hHs hAH hev
  have hUθ : ¬ U ≤ aschbacherSolvableCore 3 G := by
    intro hle
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hU1 (Subgroup.eq_bot_of_card_eq U hk)
    have hdvd : 2 ∣ Nat.card (aschbacherSolvableCore 3 G) :=
      (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hle)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hUleB : U ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer (B : Set G)), A⁆ := by
    rw [hCB]
    exact hUle
  obtain ⟨L, hL, hAL, hUN, hUC, h9, hα, -⟩ :=
    Sec4.Item462Proof.exists_thetaComponent_of_le_commutator
    h45 h41 hKF hS4 hmax h27 hzA hzZ hz1 haA haz hUle hUθ
  have hLU : ⁅L, U⁆ = L := Sec6.commutator_eq_of_not_le_theta hL.1 hL.2.2 hUN
    (fun h => hUC ((Sec6.commutator_le_theta_iff hUN).mp h))
  have h3Z : 3 ∣ Nat.card (Subgroup.center G) := by
    have h : orderOf (⟨z, hzZ⟩ : Subgroup.center G) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hz3
    rw [← h]
    exact orderOf_dvd_natCard _
  have hfix : ∀ K ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (K : Set G) := fun K hK =>
    h45 G hS4 A hAp (Or.inr ⟨hAe, 3, le_rfl, by rw [h27]; norm_num⟩) K hK
  have hUinv : U ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hU2, hAU⟩
  have hUcomm : ⁅A, U⁆ = U := by
    rw [Subgroup.commutator_comm]
    exact hUA
  have hUs : U ≤ L ⊔ Sec4.thetaQuotCentralizer L :=
    h49 G hS4 h3Z L hL A hAp hfix U hUinv hUcomm
  have hAlt423 := Sec4.Item462Proof.alt423_of h423 hS4 hmax h27 hzA hzZ hz1 hL h9 hα
  have hlist := (Sec4.Item463Proof.list_or_alt423T_of_alt423 hL hAL hAlt423).elim id fun hT =>
    hAlt G hS4 A hmax h27 z hzA hzZ hz1 hodd B hzB hBA hB9 U hU2 hU1 hAU hUA hUleB
      L hL hAL hUN hLU hUs h9 hT
      (fun e _ he3 hout => h47 G hS4 h3Z L hL e he3 hout)
  exact ⟨L, hL, hAL, h9, hα, hlist⟩

end Main

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
