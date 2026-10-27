module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.GroupTheory.ThreeTranspositions.CyclicSylow
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93d
import CFSG.Quasithin.H13.GoldschmidtG52Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped MatrixGroups
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open CFSG.Theory.Representation (kerRepresentation kerRepresentation_faithful
  kerRepresentation_irreducible_iff)

variable {Q : Type} [Group Q] [Finite Q]

theorem pRank_three_le_one_of_not_hasE9 (hE9 : ¬ HasE9 Q) :
    CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup Q)
  by_contra h
  push Not at h
  have h9 : 9 ≤ Nat.card E := by
    rw [hEcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    rcases E.bot_or_exists_ne_one with hbot | hex
    · rw [hbot, Subgroup.card_bot] at h9
      omega
    · exact hex
  have hxo : orderOf x = 3 := orderOf_eq_prime (hE.2 x hxE) hx1
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (fun y hy => hcon y hy :
      E ≤ zpowers x))
    rw [Nat.card_zpowers, hxo] at hle
    omega
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy : Commute x y :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hxE⟩ : ↥E) ⟨y, hyE⟩)
  exact hE9 ⟨x, y, hxo, orderOf_eq_prime (hE.2 y hyE) hy1, hxy, hyx⟩

theorem eq_one_of_mem_ker_of_fixV_eq_bot {r : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod r) V] [Nontrivial V] (ρ : Representation (ZMod r) Q V) {D : Subgroup Q}
    (hD3 : Nat.card D = 3) (hfix : fixV ρ D = ⊥) {d : Q} (hd : d ∈ D) (hdk : d ∈ ρ.ker) :
    d = 1 := by
  by_contra hd1
  have hDle : D ≤ ρ.ker := by
    rw [(eq_zpowers_of_card_eq_three hD3 hd hd1).1]
    exact Subgroup.zpowers_le.mpr hdk
  have htop : fixV ρ D = ⊤ := by
    rw [eq_top_iff]
    intro v _
    show ∀ a ∈ D, ρ a v = v
    intro a ha
    rw [MonoidHom.mem_ker.mp (hDle ha)]
    rfl
  exact bot_ne_top (hfix.symm.trans htop)

theorem not_three_dvd_card_ker {r : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod r) V]
    [Nontrivial V] (ρ : Representation (ZMod r) Q V) (hE9 : ¬ HasE9 Q) {D : Subgroup Q}
    (hD3 : Nat.card D = 3) (hfix : fixV ρ D = ⊥) : ¬ 3 ∣ Nat.card ρ.ker := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 (hD3 ▸ dvd_rfl : 3 ∣ Nat.card D)
  have hdo : orderOf (d : Q) = 3 := by rw [Subgroup.orderOf_coe, hd]
  intro h3
  have hd1 := eq_one_of_mem_ker_of_fixV_eq_bot ρ hD3 hfix d.2
    (CFSG.GroupTheory.ThreeTranspositions.mem_of_normal_of_three_dvd_card hE9 h3 hdo)
  rw [hd1, orderOf_one] at hdo
  omega

theorem quot_ker_cases (hK461 : UCK.K461) (hK462 : UCK.K462) {r : ℕ} [Fact r.Prime]
    (hQK : CFSG.Open.IsKGroup Q) (hE9 : ¬ HasE9 Q) (hQperf : commutator Q = ⊤)
    {D : Subgroup Q} (hD3 : Nat.card D = 3) (hDgen : normalClosure (D : Set Q) = ⊤)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod r) Q V)
    (hirr : ∀ U : Submodule (ZMod r) V, (∀ g : Q, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hfix : fixV ρ D = ⊥) :
    ¬ 3 ∣ Nat.card ρ.ker ∧
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (Q ⧸ ρ.ker ≃* SL(2, F))) ∨
        (∃ n : ℕ, CFSG.Blueprint.LieModel (Q ⧸ ρ.ker) .PSL 2 2 n) ∨
        CFSG.Quasithin.IsExt (Q ⧸ ρ.ker)
          (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
          (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 := not_three_dvd_card_ker ρ hE9 hD3 hfix
  refine ⟨hN3, ?_⟩
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
  rcases eq_or_ne r 2 with rfl | hr2
  · have hfixs : CFSG.RankThree.FFModules.fixSub (kerRepresentation ρ) (D.map π) = ⊥ := hfixb
    obtain ⟨n, F, hF, hFin, φ, -, -, -⟩ := hK461 (Q ⧸ ρ.ker) hKb V (kerRepresentation ρ) hinj
      hirrb (D.map π) hDb3 hDbgen hfixs hrank hperfb
    exact Or.inl ⟨F, hF, hFin, ⟨φ⟩⟩
  · have h2r : 2 < r := lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr2)
    obtain hSL | hL2 | hExt := hK462 r h2r (Q ⧸ ρ.ker) hKb V (kerRepresentation ρ) hinj hirrb
      (D.map π) hDb3 hDbgen hfixb hrank hperfb
    · obtain ⟨F, hF, hFin, -, φ⟩ := hSL
      exact Or.inl ⟨F, hF, hFin, φ⟩
    · obtain ⟨n, -, hn⟩ := hL2
      exact Or.inr (Or.inl ⟨n, hn⟩)
    · exact Or.inr (Or.inr hExt)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
