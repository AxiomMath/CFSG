module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27J
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27C

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.SBc17

variable {G : Type} [Group G] [Finite G]

theorem false_of_c27_normal_nonsolvable (hC27 : ASC27Statement G) {H R M K J : Subgroup G}
    (hyp : HypC23 H R M) (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hc : CharTwo K) (hKM : ¬ K ≤ M) (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hJ : J ≤ M ⊓ K) (hJN : M ⊓ K ≤ Subgroup.normalizer (J : Set G))
    (hJs : ¬ Group.IsSolvable J)
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card J → CFSG.Open.pRank p K ≤ 1) : False := by
  have c : Ctx H R M K J := ⟨⟨hyp, hK, hq, hc, hKM, hR⟩, hJ, hJN, hJs, hrank⟩
  rcases c.cases hC27 with h | h | h | h | h | h | h | h | h | h | h
  · exact c.false_of_borel hC27 h.2.2.2
  · exact c.false_of_borel hC27 h.2.2.2.2
  · obtain ⟨-, -, -, e, P, hP, hmap⟩ := h
    exact c.false_of_partition hC27 (by decide) (by decide) hP e hmap
  · obtain ⟨-, -, -, e, P, hP, hmap⟩ := h
    exact c.false_of_partition hC27 (by decide) (by decide) hP e hmap
  · exact c.false_of_alt hC27 h
  · exact c.false_of_hatA6 h.1 h.2.1
  · exact c.false_of_excA7 h.1 h.2
  · rcases h.1 with h6 | hsp
    · exact c.false_of_a6 h6
    · exact c.false_of_sp4 hsp
  · exact c.false_of_g2 hC27 h.1 h.2.1
  · obtain ⟨⟨n, F, _, _, hn1, hF, ⟨e₀⟩⟩, hmax, -⟩ := h
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      exact c.false_of_sl32 hC27 (hF.trans (pow_one 2)) e₀ hmax
    · exact c.false_of_sl3q hC27 hn2 hF e₀ hmax
  · exact c.false_of_l45 hC27 h

end CFSG.Quasithin.H13.Ch4.T425C27
