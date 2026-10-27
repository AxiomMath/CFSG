module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Proof
public import CFSG.RankThree.PartTwo.Sec17.Item1730Chosen
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511 CFSG.RankThree.PartTwo.Sec15.Proof1513

namespace Proof1513Steps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem three_dvd_card_of_quot_j2 {L : Subgroup G} {N : Subgroup ↥L} [N.Normal]
    (hJ : Nonempty (↥L ⧸ N ≃* CFSG.Blueprint.NativeSporadic.J2)) : 3 ∣ Nat.card L := by
  obtain ⟨φ⟩ := hJ
  have hq : 3 ∣ Nat.card (↥L ⧸ N) := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  exact hq.mul_right _

theorem j2_of_point (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {b : G} {Lb : Subgroup G}
    (hb : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b)
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h9 : Nat.card (A ⊓ Lb : Subgroup G) = 9) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have hD := h.toSec13Data
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  obtain ⟨d, hdAL, hd1, hdc⟩ := Sec17.exists_threeCentral_of_card_nine h415 hθ3 hJ inf_le_right
    (fun x hx => hD.isElemAbelian.2 x hx.1) h9
  obtain ⟨L', hL', hJ'⟩ := Sec17.exists_hj_at_point h134 h48 h415 hD hb hLb hJ hdAL.1 hd1 hdc
    h.zpowers_mem_omegaA
  have hL'L : L' = L :=
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 L' hL'.1 (three_dvd_card_of_quot_j2 hJ')
  subst hL'L
  exact hJ'

omit [Finite G] in
theorem false_of_j2_of_types {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (htypes : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    False := by
  obtain ⟨ψ⟩ := hJ
  obtain ⟨hJL, hJA, hJM⟩ := KFacts.KS14.ks17J2NotList
  rcases htypes with ⟨p, e, hp, -, hL3⟩ | ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
  · exact hJL p e (isoLThreePi_of_mulEquiv ψ hL3)
  · exact hJA.false (ψ.symm.trans χ)
  · exact hJM.false (ψ.symm.trans χ)


theorem not_j2_of_irreducible (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {b : G} (hb : Subgroup.zpowers b ∈ omegaA A)
    {Lb : Subgroup G} (hLb : Lb ∈ lA A b) :
    IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  refine ⟨fun ψ => ?_⟩
  have hDb := (sec15R_point h hb hLb).toSec13Data
  obtain ⟨-, htypes⟩ := cases_of_irreducible h131 h h9 hirr
  have hbL : b ∉ Lb := h.hypS.2.2 b hb Lb hLb
  have h9b : Nat.card (A ⊓ Lb : Subgroup G) = 9 := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hDb with ⟨-, h9', -⟩ | ⟨-, h9', -⟩ |
        ⟨-, hPGL, -⟩ | ⟨hbL', -⟩
    · exact h9'
    · exact h9'
    · obtain ⟨hL3, -⟩ := facts_of_isZ3PGLThreePi hDb hPGL
      obtain ⟨p, e, hp, -, hiso⟩ := hL3
      exact (KFacts.KS14.ks17J2NotList.1 p e (isoLThreePi_of_mulEquiv ψ hiso)).elim
    · exact (hbL hbL').elim
  exact false_of_j2_of_types (j2_of_point h134 h48 h415 h hb hLb ⟨ψ⟩ h9b) htypes

end Proof1513Steps

open Proof1513Steps

theorem step1513HJ_of
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) : Step1513HJ := by
  intro G _ _ A c L a K h _ hirr h9 _ ha _ hK
  refine ⟨fun φ => ?_⟩
  have hDa := (sec15R_point h ha hK).toSec13Data
  obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  obtain ⟨-, h9K, -, ⟨ψ⟩⟩ := facts_of_prod hDa hJ2p hJ2z φ
  obtain ⟨-, htypes⟩ := cases_of_irreducible h131 h h9 hirr
  exact false_of_j2_of_types (j2_of_point h134 h48 h415 h ha hK ⟨ψ⟩ h9K) htypes

end CFSG.RankThree.PartTwo.Sec15
