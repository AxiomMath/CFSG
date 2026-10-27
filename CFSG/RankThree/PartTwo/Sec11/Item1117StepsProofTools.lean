module

public import CFSG.RankThree.PartTwo.Sec11.Item1116Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
public import CFSG.RankThree.PartTwo.Sec11.RFactsK

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1117StepsProof

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem false_of_commutator_le_closure_c_d (h45 : Sec4.Item4_5) (h113 : Item113)
    (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hPP : ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {c, d})
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)) : False := by
  have h' := h.of_closure_eq hrs
  have hNd := h'.normalizer_sec11P_le_normalizer_zpowers_d h113 h117 hcdN
  have htrans := h'.htrans hcdN hNd
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have haR : a ∈ R := le_R_of_hyp91 h.toHyp91 h.a_mem
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have hVP : Subgroup.closure ({s, x} : Set G) ≤ sec11P R g := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact le_sup_left (a := R) hsR
    · exact le_sup_left (a := R) hxR
  have hcdV : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.closure {s, x} := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h.c_mem_zpowers_s
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
        (Item1117Proof.d_mem_zpowers_x h)
  have hgV : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, x} : Set G) : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have e : g * v * g⁻¹ = ⁅g, v⁆ * v := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hcdV (hPP (Subgroup.commutator_mem_commutator hgP (hVP hv)))) hv
  have hag : a * g = g * a := (Item1117Proof.commute_g_a h).symm
  exact rank3II_11_15_of h' hag h'.commute_s_x (h'.R_le_normalizer_V h45) hgV
    (h'.normalizer_P_le_normalizer_V h45 h113) (h'.commutator_mem_V h45 h113 outAbelian1016 haR)
    h'.r_not_mem_V hcdN hNd htrans

end Data

end Item1117StepsProof

end CFSG.RankThree.PartTwo.Sec11
