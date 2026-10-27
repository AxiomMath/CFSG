module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340S
import CFSG.Quasithin.EmptyFaithful.S1422LocTitsAct
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentE9

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.RankThree.LocalRank

open scoped commutatorElement

theorem res1340_commutator_le {G : Type} [Group G] [Finite G]
    {L Q P : Subgroup G} [Group.IsPerfect ↥L]
    (hsimple : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hE9 : ∃ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (_hPQ : P ≤ Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (_hQP : Q ≤ Subgroup.normalizer (P : Set G))
    [(P.subgroupOf Q).Normal] (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hS2 : CFSG.pCore 2 (↥Q ⧸ P.subgroupOf Q) = ⊥)
    (hSz : CFSG.RankThree.S4Free.SzSections (↥Q ⧸ P.subgroupOf Q))
    (hrank : ∀ p : ℕ, p.Prime → 5 ≤ p →
      CFSG.Open.pRank p (⊤ : Subgroup (↥Q ⧸ P.subgroupOf Q)) ≤ 2) :
    ⁅L, Q⁆ ≤ P := by
  obtain ⟨hNsol, -, hN3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨E, hE, hE9'⟩ := res1Cent_exists_e9_lift (aschbacherSolvableCore 3 ↥L) hN3 hE9
  have hS3 : ¬ 3 ∣ Nat.card (↥Q ⧸ P.subgroupOf Q) := fun h =>
    hQ3 (h.trans (Subgroup.card_quotient_dvd_card _))
  have hφ := res1340_mulAut_eq_one hNsol hN3 hsimple hE hE9' hS3 hS2 hSz hrank
    (CFSG.Quasithin.S1422Loc.quotAction hLQ hLP)
  rw [Subgroup.commutator_le]
  intro l hl q hq
  have h := congrArg
    (fun f : ↥L →* MulAut (↥Q ⧸ P.subgroupOf Q) => f ⟨l, hl⟩ (QuotientGroup.mk ⟨q, hq⟩)) hφ
  simp only [CFSG.Quasithin.S1422Loc.quotAction_mk, MonoidHom.one_apply, MulAut.one_apply] at h
  have h2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq_iff_div_mem.mp h)
  simpa [commutatorElement_def, div_eq_mul_inv] using h2

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
