module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h
import CFSG.Quasithin.H13.GoldschmidtG52Sec
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup
open scoped MatrixGroups
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09
open CFSG.Theory.Representation (kerRepresentation kerRepresentation_faithful
  kerRepresentation_irreducible_iff)

private theorem card_map_ker_mk'_eq_three {Q : Type} [Group Q] [Finite Q] {r : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Nontrivial V]
    (ρ : Representation (ZMod r) Q V) {D : Subgroup Q} (hD3 : Nat.card D = 3)
    (hfix : fixV ρ D = ⊥) :
    Nat.card (D.map (QuotientGroup.mk' ρ.ker)) = 3 := by
  obtain ⟨d₀, hd₀⟩ := exists_prime_orderOf_dvd_card' 3 (hD3 ▸ dvd_rfl : 3 ∣ Nat.card D)
  have hd₀1 : (d₀ : Q) ≠ 1 := fun h => by
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hd₀
    omega
  have hdvd : Nat.card (D.map (QuotientGroup.mk' ρ.ker)) ∣ 3 :=
    hD3 ▸ Subgroup.card_map_dvd D (QuotientGroup.mk' ρ.ker)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    have hmem : QuotientGroup.mk' ρ.ker d₀ ∈ D.map (QuotientGroup.mk' ρ.ker) :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' ρ.ker) d₀.2
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hmem
    exact hd₀1 (eq_one_of_mem_ker_of_fixV_eq_bot ρ hD3 hfix d₀.2
      ((QuotientGroup.eq_one_iff _).mp hmem))
  · exact h3

private theorem normalClosure_map_ker_mk'_eq_top {Q : Type} [Group Q] {r : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod r) V]
    (ρ : Representation (ZMod r) Q V) {D : Subgroup Q}
    (hDgen : normalClosure (D : Set Q) = ⊤) :
    normalClosure ((D.map (QuotientGroup.mk' ρ.ker) : Subgroup (Q ⧸ ρ.ker)) :
      Set (Q ⧸ ρ.ker)) = ⊤ := by
  rw [Subgroup.coe_map,
    ← Subgroup.map_normalClosure _ (QuotientGroup.mk' ρ.ker)
      (QuotientGroup.mk'_surjective _), hDgen,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem fixV_kerRepresentation_map_ker_mk'_eq_bot {Q : Type} [Group Q] {r : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod r) V]
    (ρ : Representation (ZMod r) Q V) {D : Subgroup Q} (hfix : fixV ρ D = ⊥) :
    fixV (kerRepresentation ρ) (D.map (QuotientGroup.mk' ρ.ker)) = ⊥ := by
  rw [eq_bot_iff, ← hfix]
  intro v hv
  have hv' : ∀ b ∈ D.map (QuotientGroup.mk' ρ.ker), kerRepresentation ρ b v = v := hv
  show ∀ a ∈ D, ρ a v = v
  intro a ha
  exact hv' (QuotientGroup.mk' ρ.ker a) (Subgroup.mem_map_of_mem (QuotientGroup.mk' ρ.ker) ha)

private theorem pRank_three_quot_ker_eq_one {Q : Type} [Group Q] [Finite Q] {r : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Nontrivial V]
    (ρ : Representation (ZMod r) Q V) (hE9 : ¬ HasE9 Q) {D : Subgroup Q}
    (hD3 : Nat.card D = 3) (hfix : fixV ρ D = ⊥) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Q ⧸ ρ.ker)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 := not_three_dvd_card_ker ρ hE9 hD3 hfix
  have hDb3 := card_map_ker_mk'_eq_three ρ hD3 hfix
  refine le_antisymm (pRank_three_le_one_of_not_hasE9 fun h =>
    hE9 (CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient ρ.ker hN3 h)) ?_
  exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤)
    (E := D.map (QuotientGroup.mk' ρ.ker)) (by norm_num) le_top
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hDb3) (k := 1)
    (by rw [hDb3, pow_one])

theorem quot_ker_K462 {Q : Type} [Group Q] [Finite Q] (hK462 : UCK.K462) {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) (hQK : CFSG.Open.IsKGroup Q) (hE9 : ¬ HasE9 Q)
    (hQperf : commutator Q = ⊤) {D : Subgroup Q} (hD3 : Nat.card D = 3)
    (hDgen : normalClosure (D : Set Q) = ⊤)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod r) Q V)
    (hirr : ∀ U : Submodule (ZMod r) V, (∀ g : Q, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV ρ D = ⊥) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
        Nonempty ((Q ⧸ ρ.ker) ≃* SL(2, F))) ∨
      (∃ m : ℕ, Odd m ∧ LieModel (Q ⧸ ρ.ker) .PSL 2 2 m) ∨
      CFSG.Quasithin.IsExt (Q ⧸ ρ.ker)
        (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y) := by
  classical
  have hinj : Function.Injective (kerRepresentation ρ) := kerRepresentation_faithful ρ
  have hirrb : Representation.IsIrreducible (kerRepresentation ρ) :=
    (kerRepresentation_irreducible_iff ρ).mpr
      (CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule ρ hirr)
  have hperfb : commutator (Q ⧸ ρ.ker) = ⊤ := by
    haveI : Group.IsPerfect Q := ⟨hQperf⟩
    exact Group.IsPerfect.commutator_eq_top
  have hKb : CFSG.Open.IsKGroup (Q ⧸ ρ.ker) := hQK.quotient ρ.ker
  have h2r : 2 < r := lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr2)
  obtain hSL | hL2 | hExt := hK462 r h2r (Q ⧸ ρ.ker) hKb V (kerRepresentation ρ) hinj hirrb
    (D.map (QuotientGroup.mk' ρ.ker)) (card_map_ker_mk'_eq_three ρ hD3 hfix)
    (normalClosure_map_ker_mk'_eq_top ρ hDgen)
    (fixV_kerRepresentation_map_ker_mk'_eq_bot ρ hfix)
    (pRank_three_quot_ker_eq_one ρ hE9 hD3 hfix) hperfb
  · obtain ⟨F, hF, hFin, hodd, φ⟩ := hSL
    exact Or.inl ⟨F, hF, hFin, hodd, φ⟩
  · obtain ⟨m, hodd, hm⟩ := hL2
    exact Or.inr (Or.inl ⟨m, hodd, hm⟩)
  · exact Or.inr (Or.inr hExt)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
