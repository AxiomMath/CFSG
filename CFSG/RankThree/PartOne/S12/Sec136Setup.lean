module

public import CFSG.RankThree.PartOne.S12.RowFacts
public import CFSG.RankThree.PartOne.S12.Sec138Trans
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartOne.KF.Reduction123

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem not_psp_three_and_psu_five {Q : Type} [Group Q] {a g : ℕ}
    (h1 : StatedClassicalModel Q .PSp 3 2 a) (ha : 1 ≤ a) (h2 : StatedClassicalModel Q .PSU 5 2 g)
    (hg : 1 ≤ g) : False := by
  have c1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h1).2.2.1 rfl
  have c2 := (CFSG.Timmesfeld.card_statedClassicalModel_two h2).2.1 rfl
  exact CFSG.Timmesfeld.Orders.ordBC_ne_ordTwistedA (n := 3) (u := 5 - 1) (by norm_num) ha
    (by norm_num) hg (c1.symm.trans c2)

theorem rowTen_data (hRow10 : KF123Row 10) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) {p : ℕ} {B : Subgroup G} {c : G} {X E : Subgroup G}
    (h : Sec12Hyp G p B c X E) (hm : RowModel p X 10) :
    Sec12TwoGeneric p c X E ∧ RowWeylIso E (torusImage E X) 10 ∧ Nat.card E = p ^ 4 := by
  rcases Sec12Hyp.table123_hyp h107 h109 h122 h with ⟨hG, hT⟩ | ⟨hS, hT⟩
  · obtain ⟨-, hcard, hweyl, -, -, -⟩ := hRow10 G p X (B ⊓ X) (E ⊓ X) hT hm
    have R := h.restr_of_generic hG
    have hcL := h.c_not_mem_of_generic hG
    have hEcard := R.card_E h.prime (Sec12Three.orderOf_c h) hcL
    refine ⟨hG, R.rowWeylIso hweyl, ?_⟩
    rw [hEcard, hcard, Sec12Three.rowRank_eq_three (by norm_num) (by norm_num) (by norm_num)]
    ring
  · exfalso
    obtain ⟨f', hf', hmod5⟩ := hS.model
    obtain ⟨f, hf, -, hmod10⟩ := hm
    exact not_psp_three_and_psu_five hmod10 hf hmod5 hf'

theorem central_involution_data {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hG : Sec12TwoGeneric p c L E)
    (hweyl : RowWeylIso E (torusImage E L) 10) :
    ∃ u : MulAut E, u ∈ torusImage E L ∧ u ≠ 1 ∧ u * u = 1 ∧
      (∀ g ∈ torusImage E L, g * u = u * g) ∧ autFixedInG E u = Subgroup.zpowers c ∧
      ∀ b : E, (b : G) ∈ L → u b = b⁻¹ := by
  classical
  obtain ⟨u, huΓ, hu1, hu2, hucomm⟩ := rowWeylIso_central_involution_of_ten hweyl
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have R := h.restr_of_generic hG
  have hcL := h.c_not_mem_of_generic hG
  have hEc : ∀ a b : E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.1 huΓ
  have hnL : (n : G) ∈ L := Subgroup.mem_subgroupOf.mp hn
  have hu_app : ∀ e : E, ((u e : E) : G) = (n : G) * e * (n : G)⁻¹ := fun e => by
    rw [← hnu]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe E n e
  have hu_c : u ⟨c, hcE⟩ = ⟨c, hcE⟩ := by
    apply Subtype.ext
    rw [hu_app]
    show (n : G) * c * (n : G)⁻¹ = c
    rw [← R.comm (n : G) hnL, mul_assoc, mul_inv_cancel, mul_one]
  have hcB : c ∈ autFixedInG E u := ⟨⟨c, hcE⟩, hu_c, rfl⟩
  have hinv : torusInvariant E L (autFixedInG E u) := by
    intro w hw b hb
    obtain ⟨hwL, hwN⟩ := Subgroup.mem_inf.1 hw
    have hwN' : w ∈ Subgroup.normalizer (E : Set G) := hwN
    have hg := Sec138Trans.conjAut_mem_torusImage hwN' hwL
    have hgu := hucomm _ hg
    obtain ⟨e, he, rfl⟩ := hb
    refine ⟨conjAut E w hwN' e, ?_, ?_⟩
    · have h1 : (conjAut E w hwN' * u) e = (u * conjAut E w hwN') e := by rw [hgu]
      have h2 : u e = e := he
      show u (conjAut E w hwN' e) = conjAut E w hwN' e
      have h3 : conjAut E w hwN' (u e) = u (conjAut E w hwN' e) := h1
      rw [← h3, h2]
    · exact Equivariance.coe_conjAut hwN' e
  have hfix : autFixedInG E u = Subgroup.zpowers c := by
    have hle : autFixedInG E u ≤ E := Subgroup.map_subtype_le _
    have hne_top : autFixedInG E u ≠ E := by
      intro heq
      apply hu1
      refine MulEquiv.ext fun x => ?_
      have hx : (x : G) ∈ autFixedInG E u := by rw [heq]; exact x.2
      obtain ⟨e, he, hex⟩ := hx
      have hex' : e = x := Subtype.ext hex
      subst hex'
      exact he
    have hne_bot : autFixedInG E u ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hcB
      exact h.c_ne_one hcB
    rcases hF.four.1 _ hle hinv hne_bot hne_top with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hcB
      exact hcL (R.F_le_L (R.commutator_le_F hcB))
  refine ⟨u, huΓ, hu1, hu2, hucomm, hfix, ?_⟩
  intro b hb
  have hbb : u (u b) = b := by simpa using congrArg (fun m : MulAut E => m b) hu2
  have hw : b * u b ∈ autFixed E u := by
    show u (b * u b) = b * u b
    rw [map_mul, hbb, hEc]
  have hw' : ((b * u b : E) : G) ∈ Subgroup.zpowers c := by
    rw [← hfix]
    exact ⟨b * u b, hw, rfl⟩
  have hwL : ((b * u b : E) : G) ∈ L := by
    rw [Subgroup.coe_mul, hu_app]
    exact L.mul_mem hb (L.mul_mem (L.mul_mem hnL hb) (L.inv_mem hnL))
  have h1 : ((b * u b : E) : G) ∈ Subgroup.zpowers c ⊓ L := ⟨hw', hwL⟩
  rw [Sec12Three.zpowers_inf_eq_bot h.prime (Sec12Three.orderOf_c h) hcL, Subgroup.mem_bot] at h1
  have h2 : b * u b = 1 := Subtype.ext h1
  exact eq_inv_of_mul_eq_one_right h2

end CFSG.RankThree.PartOne
