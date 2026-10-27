module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.RankThree.PartTwo.Sec11.TwoStarProofComponent
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddGroup
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoLThree
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoUThree
import CFSG.Quasithin.EmptyFaithful.T1521SU3Out
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGJ1
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitaryPSU unitaryProj unitaryProj_surjective
  unitaryPSUEquiv)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

private theorem r1f2_ne_one {G : Type*} [Group G] {x : G} (hx : orderOf x = 3) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  norm_num at hx

private theorem r1f2_pow_three {G : Type*} [Group G] {x : G} (hx : orderOf x = 3) :
    x ^ 3 = 1 := by
  rw [← hx]
  exact pow_orderOf_eq_one x

private theorem r1f2_isCyclic_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 2) : IsCyclic G := by
  have h0 : 0 < Nat.card G := Nat.card_pos
  refine isCyclic_of_card_dvd_prime (p := 2) ?_
  obtain h1 | h1 : Nat.card G = 1 ∨ Nat.card G = 2 := by omega
  · rw [h1]
    exact one_dvd 2
  · rw [h1]

private theorem r1f2_odd_card_of_forall {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ∀ c ∈ H, c ^ 2 = 1 → c = 1) : Odd (Nat.card H) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (even_iff_two_dvd.mp hodd)
  have hc2 : (c : G) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
  have h1 : c = 1 := Subtype.ext (h c c.2 hc2)
  rw [h1, orderOf_one] at hc
  norm_num at hc

private theorem r1f2_isCyclic_of_outer {K : Type} [Group K]
    (hcyc : ∀ B : Subgroup (MulAut K), IsPGroup 2 B → IsCyclic (B.map
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K))))
    {W : Subgroup (MulAut K)} (hW : IsPGroup 2 W)
    (hWi : W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) : IsCyclic W := by
  have := hcyc W hW
  refine isCyclic_of_injective ((QuotientGroup.mk'
    (CFSG.ComponentClassification.OuterAutomorphisms.inner K)).subgroupMap W)
    ((injective_iff_map_eq_one _).mpr fun w hw => ?_)
  have hw' : (w : MulAut K) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K :=
    (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner K)
      (w : MulAut K)).mp (congrArg Subtype.val hw)
  have hmem : (w : MulAut K) ∈ W ⊓ (MulAut.conj : K →* MulAut K).range := mem_inf.mpr ⟨w.2, hw'⟩
  rw [hWi, mem_bot] at hmem
  exact Subtype.ext hmem

theorem odd_card_centralizer_of_psl_two_two {K : Type} [Group K] [Finite K] {f : ℕ}
    (hK : LieModel K .PSL 2 2 f) {x : K} (hx : orderOf x = 3) :
    Odd (Nat.card (centralizer ({x} : Set K))) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel
    (hK.statedClassicalModel (by decide))
  have hf2 : 2 ≤ f := (UC22.P22fin.isL2Ev_of_isL2 hK).2
  have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  rcases (CFSG.RankThree.PartTwo.Sec11.TwoStarProof.centralizer_isCyclic_card hf2 e
    (r1f2_ne_one hx) (r1f2_pow_three hx)).2 with h | h <;> rw [h]
  · exact Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one
  · exact hev.add_one

theorem isCyclic_of_inf_inner_eq_bot_of_psl_two_two {K : Type} [Group K] [Finite K] {f : ℕ}
    (hK : LieModel K .PSL 2 2 f) (W : Subgroup (MulAut K)) (hW : IsPGroup 2 W)
    (hWi : W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) : IsCyclic W := by
  have := UC22.P22y.isCyclic_outer_of_isL2Ev (UC22.P22fin.isL2Ev_of_isL2 hK).1
  exact r1f2_isCyclic_of_outer (fun _ _ => inferInstance) hW hWi

theorem odd_card_centralizer_of_psl_three_two {K : Type} [Group K] [Finite K] {f : ℕ}
    (hq : 2 ^ f % 3 = 2) (hK : LieModel K .PSL 3 2 f) {x : K} (hx : orderOf x = 3) :
    Odd (Nat.card (centralizer ({x} : Set K))) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel
    (hK.statedClassicalModel (by decide))
  have hF : Nat.card (GaloisField 2 f) % 3 = 2 := by
    rw [GaloisField.card 2 f (by rintro rfl; norm_num at hq)]
    exact hq
  obtain ⟨σ⟩ := CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.nonempty_sl_three_mulEquiv_projSL hF
  set e' := e.trans σ.symm
  refine r1f2_odd_card_of_forall _ fun c hc hc2 => e'.injective ?_
  rw [map_one]
  exact CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.sl_three_eq_one_of_commute hF
    (x := e' x) (c := e' c) (by rw [← map_pow, r1f2_pow_three hx, map_one])
    (by rw [Ne, map_eq_one_iff e' e'.injective]; exact r1f2_ne_one hx)
    (by rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc])
    (by rw [← map_pow, hc2, map_one])

theorem isCyclic_of_inf_inner_eq_bot_of_psl_three_two {K : Type} [Group K] [Finite K] {f : ℕ}
    (hq : 2 ^ f % 3 = 2) (hK : LieModel K .PSL 3 2 f) (W : Subgroup (MulAut K))
    (hW : IsPGroup 2 W) (hWi : W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) : IsCyclic W := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel
    (hK.statedClassicalModel (by decide))
  have : Finite (MulAut K) := MulEquiv.finite_left
  exact r1f2_isCyclic_of_card_le_two
    (CFSG.RankThree.PartTwo.Sec20.L3OddGroup.card_le_two_of_inf_inn_eq_bot_L3 hq e hW hWi)

private theorem r1f2_exists_unitarySU {K : Type} [Group K] {f : ℕ} (hq : 2 ^ f % 3 = 1)
    (hK : LieModel K .PSU 3 2 f) :
    ∃ (F : Type) (_ : Field F), UnitaryFieldData 2 f F ∧ Nonempty (K ≃* unitarySU 2 f F 3) := by
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := hK.statedClassicalModel (by decide)
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hadm.2.1, by rw [hF, ← pow_mul, mul_comm]⟩
  let ψ : unitarySU 2 f F 3 ≃* unitaryPSU h 3 :=
    MulEquiv.ofBijective (unitaryProj h 3)
      ⟨CFSG.RankThree.PartTwo.KFacts.unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩
  exact ⟨F, inferInstance, h, ⟨(e.trans (unitaryPSUEquiv h (by norm_num)).symm).trans ψ.symm⟩⟩

theorem odd_card_centralizer_of_psu_three_two {K : Type} [Group K] [Finite K] {f : ℕ}
    (hq : 2 ^ f % 3 = 1) (hK : LieModel K .PSU 3 2 f) {x : K} (hx : orderOf x = 3) :
    Odd (Nat.card (centralizer ({x} : Set K))) := by
  obtain ⟨F, _, h, ⟨e⟩⟩ := r1f2_exists_unitarySU hq hK
  refine r1f2_odd_card_of_forall _ fun c hc hc2 => e.injective ?_
  rw [map_one]
  exact CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.su_three_eq_one_of_commute h hq
    (x := e x) (c := e c) (by rw [← map_pow, r1f2_pow_three hx, map_one])
    (by rw [Ne, map_eq_one_iff e e.injective]; exact r1f2_ne_one hx)
    (by rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc])
    (by rw [← map_pow, hc2, map_one])

theorem isCyclic_of_inf_inner_eq_bot_of_psu_three_two {K : Type} [Group K] [Finite K] {f : ℕ}
    (hq : 2 ^ f % 3 = 1) (hK : LieModel K .PSU 3 2 f) (W : Subgroup (MulAut K))
    (hW : IsPGroup 2 W) (hWi : W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) : IsCyclic W := by
  have hf2 : 2 ≤ f := by
    have hf1 : 1 ≤ f := hK.admissible.2.1
    by_contra hlt
    obtain rfl : f = 1 := by omega
    norm_num at hq
  exact r1f2_isCyclic_of_outer (fun _ hB => CFSG.Quasithin.U31521.cyclic_map_outer_of_isPGroup hf2
    (hK.statedClassicalModel (by decide)) hB) hW hWi

theorem mem_range_conj_of_isSpor_J1 {K : Type} [Group K] [Finite K] (hK : IsSpor K .J1)
    (α : MulAut K) : α ∈ (MulAut.conj : K →* MulAut K).range :=
  Small.s1667_kg_j1_aut_mem_range hK α

theorem isCyclic_of_le_centralizer_of_isSpor_J1 {K : Type} [Group K] [Finite K]
    (hK : IsSpor K .J1) {x : K} (hx : orderOf x = 3) (P : Subgroup K)
    (hP : P ≤ centralizer ({x} : Set K)) (h2 : IsPGroup 2 P) : IsCyclic P := by
  obtain ⟨e⟩ := Small.s1667_kg_j1_equiv hK
  have hy : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hPC : P.map e.toMonoidHom ≤ centralizer ({e x} : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change e a * e x = e x * e a
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hP ha)]
  have hdvd : Nat.card P ∣ Nat.card (centralizer ({e x} : Set _)) := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact card_dvd_of_le hPC
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  apply r1f2_isCyclic_of_card_le_two
  rw [hk]
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra h'
    interval_cases k <;> norm_num at hlt
  apply Small.s1667_kg_j1_not_four_dvd_card_centralizer hy
  calc 4 = 2 ^ 2 := by norm_num
    _ ∣ 2 ^ k := pow_dvd_pow 2 hk2
    _ = Nat.card P := hk.symm
    _ ∣ _ := hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
