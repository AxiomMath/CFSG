module

public import CFSG.Timmesfeld.Orders.BangField
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_U3CartanRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n p : ℕ), IsSU3 X n →
    p.Prime → p ∣ 2 ^ n + 1 → (3 < p ∨ n = 3) →
      ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
        1 ≤ CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S))

theorem uc2_17_36a_exists_prime_gt_three {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n + 1 := by
  have h2n : 2 ≤ 2 * n := by omega
  have h6 : 2 * n ≠ 6 := by omega
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * n) h2n h6
  have hp3 : 3 < p := hp.three_lt_of_two_lt (by omega)
  have hnotdvd : ¬ 2 * n ∣ n := by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hdvd : p ∣ 2 ^ n + 1 :=
    (hp.dvd_add_one_iff (k := 2 * n) (by omega) n).2 ⟨dvd_rfl, hnotdvd⟩
  exact ⟨p, hp.prime, hp3, hdvd⟩

theorem exists_elemAbelian_sq_lift_of_isSU3 {L : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (Bar2 L))) :
    ∃ E : Subgroup G, E ≤ L ∧ CFSG.Open.IsElemAbelian q E ∧
      ∃ a : ℕ, 2 ≤ a ∧ Nat.card E = q ^ a := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set m := CFSG.Open.pRank q (⊤ : Subgroup (Bar2 L)) with hm
  obtain ⟨Eb, -, hEbel, hEbcard⟩ :=
    CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup (Bar2 L))
  have hEbcard' : Nat.card Eb = q ^ m := hEbcard
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 Eb hEbel.isPGroup
  refine ⟨Q.map L.subtype, Subgroup.map_subtype_le Q, ?_, m, by rw [hm]; exact h, ?_⟩
  · exact (isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hEbel)).map _
  · rw [Subgroup.card_map_of_injective L.subtype_injective,
      ← card_map_of_disjoint_ker π Q hQdisj, hQmap, hEbcard']

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
