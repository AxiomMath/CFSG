module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h
import CFSG.Quasithin.H13.GoldschmidtG52Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped MatrixGroups
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09
open CFSG.Theory.Representation (kerRepresentation kerRepresentation_faithful
  kerRepresentation_irreducible_iff)

variable {Q : Type} [Group Q] [Finite Q]

theorem quot_ker_semireg (hK46 : UCK.K46Semireg) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hQK : CFSG.Open.IsKGroup Q) (hE9 : ¬ HasE9 Q) (hQperf : commutator Q = ⊤)
    {D : Subgroup Q} (hD3 : Nat.card D = 3) (hDgen : normalClosure (D : Set Q) = ⊤)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod r) Q V)
    (hirr : ∀ U : Submodule (ZMod r) V, (∀ g : Q, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV ρ D = ⊥)
    (hfixA : ∀ (p : ℕ) (A : Subgroup Q), p.Prime → p ≠ 2 → Nat.card A = p → fixV ρ A = ⊥) :
    Nonempty ((Q ⧸ ρ.ker) ≃* SL(2, ZMod 5)) ∨
      CFSG.Quasithin.IsExt (Q ⧸ ρ.ker)
        (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 := not_three_dvd_card_ker ρ hE9 hD3 hfix
  obtain ⟨d₀, hd₀⟩ := exists_prime_orderOf_dvd_card' 3 (hD3 ▸ dvd_rfl : 3 ∣ Nat.card D)
  have hd₀1 : (d₀ : Q) ≠ 1 := fun h => by
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hd₀
    omega
  let π : Q →* Q ⧸ ρ.ker := QuotientGroup.mk' ρ.ker
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hinj : Function.Injective (kerRepresentation ρ) := kerRepresentation_faithful ρ
  have hirrb : Representation.IsIrreducible (kerRepresentation ρ) :=
    (kerRepresentation_irreducible_iff ρ).mpr
      (CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule ρ hirr)
  have hDb3 : Nat.card (D.map π) = 3 := by
    have hdvd : Nat.card (D.map π) ∣ 3 := hD3 ▸ Subgroup.card_map_dvd D π
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hmem : π d₀ ∈ D.map π := Subgroup.mem_map_of_mem π d₀.2
      rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hmem
      exact hd₀1 (eq_one_of_mem_ker_of_fixV_eq_bot ρ hD3 hfix d₀.2
        ((QuotientGroup.eq_one_iff _).mp hmem))
    · exact h3
  have hDbgen : normalClosure ((D.map π : Subgroup (Q ⧸ ρ.ker)) : Set (Q ⧸ ρ.ker)) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ π hπ, hDgen,
      Subgroup.map_top_of_surjective π hπ]
  have hfixb : fixV (kerRepresentation ρ) (D.map π) = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    intro v hv
    have hv' : ∀ b ∈ D.map π, kerRepresentation ρ b v = v := hv
    show ∀ a ∈ D, ρ a v = v
    intro a ha
    exact hv' (π a) (Subgroup.mem_map_of_mem π ha)
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (Q ⧸ ρ.ker)) = 1 := by
    refine le_antisymm (pRank_three_le_one_of_not_hasE9 fun h =>
      hE9 (CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient ρ.ker hN3 h)) ?_
    exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := D.map π) (by norm_num) le_top
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hDb3) (k := 1) (by rw [hDb3, pow_one])
  have hperfb : commutator (Q ⧸ ρ.ker) = ⊤ := by
    haveI : Group.IsPerfect Q := ⟨hQperf⟩
    exact Group.IsPerfect.commutator_eq_top
  have hKb : CFSG.Open.IsKGroup (Q ⧸ ρ.ker) := hQK.quotient ρ.ker
  have hfixAb : ∀ (p : ℕ) (Ā : Subgroup (Q ⧸ ρ.ker)), p.Prime → p ≠ 2 →
      Nat.card Ā = p → fixV (kerRepresentation ρ) Ā = ⊥ := by
    intro p Ā hp hp2 hcard
    haveI : Fact p.Prime := ⟨hp⟩
    let B : Subgroup Q := Ā.comap π
    have hBcard : p ∣ Nat.card B := by
      have hmap : B.map π = Ā := Subgroup.map_comap_eq_self_of_surjective hπ Ā
      have hdvd : Nat.card (B.map π) ∣ Nat.card B := Subgroup.card_map_dvd B π
      rwa [hmap, hcard] at hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hBcard
    have hgQ : orderOf ((g : Q)) = p := by rw [Subgroup.orderOf_coe, hg]
    let A₁ : Subgroup Q := Subgroup.zpowers (g : Q)
    have hA₁card : Nat.card A₁ = p := by
      show Nat.card (Subgroup.zpowers (g : Q)) = p
      rw [Nat.card_zpowers, hgQ]
    have hA₁fix : fixV ρ A₁ = ⊥ := hfixA p A₁ hp hp2 hA₁card
    have hA₁B : A₁ ≤ B := Subgroup.zpowers_le.mpr g.2
    refine eq_bot_iff.mpr fun v hv => ?_
    have hvB : v ∈ fixV ρ B := by
      intro a ha
      have hva := hv (π a) (ha : π a ∈ Ā)
      rwa [show kerRepresentation ρ (π a) = ρ a from rfl] at hva
    have hvA₁ : v ∈ fixV ρ A₁ := fun a ha => hvB a (hA₁B ha)
    have hmem : v ∈ (⊥ : Submodule (ZMod r) V) := hA₁fix ▸ hvA₁
    simpa using hmem
  have h2r : 2 < r := lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr2)
  exact hK46 r h2r (Q ⧸ ρ.ker) hKb V (kerRepresentation ρ) hinj hirrb
    (D.map π) hDb3 hDbgen hfixb hrank hperfb hfixAb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
