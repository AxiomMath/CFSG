module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQuot
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Ord3
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem genByOrderThree_opp (S : Slice D L D₃ Y H q) {E : Subgroup G} (hEX : E ≤ Opp 3 Y)
    (hE3 : Nat.card E = 3) : Opp 3 Y ≤ closure {x : G | x ∈ Opp 3 Y ∧ orderOf x = 3} := by
  haveI : IsSimpleGroup (Bar2 (Opp 3 Y)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide)
      S.shape_opp
  have h3 : 3 ∣ Nat.card ↥(Opp 3 Y) := (dvd_of_eq hE3.symm).trans (Subgroup.card_dvd_of_le hEX)
  refine CFSG.Quasithin.S15223.genByOrderThree_of_epi_simple ?_
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(Opp 3 Y))) (QuotientGroup.ker_mk' _) h3
  intro N _ hN2
  rw [eq_top_iff, ← F09.closure_threeElements_opp Y, Subgroup.closure_le]
  rintro x ⟨k, hk⟩
  obtain ⟨m, hm⟩ := hN2 (x : ↥(Opp 3 Y) ⧸ N)
  have h1 : orderOf (x : ↥(Opp 3 Y) ⧸ N) ∣ 3 ^ k := by
    rw [← hk]
    exact orderOf_map_dvd (QuotientGroup.mk' N) x
  have h2 : orderOf (x : ↥(Opp 3 Y) ⧸ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow k m (by norm_num)))
      (orderOf_dvd_of_pow_eq_one hm)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h2
  exact h2

theorem isSimpleGroup_Lbar9 (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) : IsSimpleGroup (F09.Lbar9 Y H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXH : Opp 3 Y ≤ H := (F09.opp_le_self 3 Y).trans hyp.2.1.1
  have hLH : F09.L9 Y H ≤ H := iSup_le fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem h.2 (hXH hx)) (H.inv_mem h.2)
  let π : ↥H →* F09.Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let φ : ↥(F09.L9 Y H) →* F09.Lbar9 Y H := (π.subgroupMap ((F09.L9 Y H).subgroupOf H)).comp
    (Subgroup.subgroupOfEquivOfLe hLH).symm.toMonoidHom
  have hφ : Function.Surjective φ :=
    (π.subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hLH).symm.surjective
  have hX := S.genByOrderThree_opp hyp.2.2.1 hyp.2.2.2
  have hL : F09.L9 Y H ≤
      (closure {x : ↥(F09.L9 Y H) | orderOf x = 3}).map (F09.L9 Y H).subtype := by
    refine iSup_le fun h => ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_ (CFSG.Quasithin.S15223.GenByOrderThree.conj_mem
      (Y' := F09.L9 Y H) (g := (h : G)) (fun y hy => (le_iSup (fun k : ↥H =>
        (Opp 3 Y).map (MulAut.conj (k : G)).toMonoidHom) h) ⟨y, hy, rfl⟩) hX hx)
    rintro z ⟨hzL, hz3⟩
    exact ⟨⟨z, hzL⟩, (Subgroup.orderOf_mk z hzL).trans hz3, rfl⟩
  have hC : closure {x : ↥(F09.L9 Y H) | orderOf x = 3} = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨c, hc, hcx⟩ := hL hx
    rwa [show c = ⟨x, hx⟩ from Subtype.ext hcx] at hc
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 3 (by rw [hyp.2.2.2])
  have heL : (e : G) ∈ F09.L9 Y H := F09.opp_le_L9 Y H (hyp.2.2.1 e.2)
  have hφe : φ ⟨e, heL⟩ ≠ 1 := by
    intro h1
    have h2 : π ⟨e, hLH heL⟩ = 1 := congrArg Subtype.val h1
    have h3 := (QuotientGroup.eq_one_iff _).mp h2
    have h4 := orderOf_dvd_natCard (⟨⟨e, hLH heL⟩, h3⟩ : ↥(CFSG.pPrimeCore 3 ↥H))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe, he] at h4
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card h4
  haveI : Nontrivial (F09.Lbar9 Y H) := ⟨⟨_, _, hφe⟩⟩
  refine CFSG.GroupTheory.ThreeTranspositions.isSimpleGroup_of_generated_by_order_three
    (F09.not_hasE9_Lbar9 hyp) (F09.pPrimeCore_Lbar9 hyp.2.1.1)
    (S := φ '' {x | orderOf x = 3}) ?_ ?_
  · rw [← MonoidHom.map_closure, hC, Subgroup.map_top_of_surjective φ hφ]
  · rintro _ ⟨x, hx, rfl⟩
    have h := orderOf_map_dvd φ x
    rw [hx] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
    · exact Or.inl (orderOf_eq_one_iff.mp h1)
    · exact Or.inr h1

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
