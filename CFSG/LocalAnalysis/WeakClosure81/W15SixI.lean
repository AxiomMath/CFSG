module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixG
public import CFSG.LocalAnalysis.WeakClosure81.W15SixH
public import CFSG.Quasithin.EmptyFaithful.S1565L4
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped CFSG.Goldschmidt.G2

variable {G : Type} [Group G] [Finite G]

namespace Cex156

variable {M V₀ V U S A X T : Subgroup G}

theorem contradiction (hB : Asc80ThmB) (hMult : SchurMultiplierInput)
    (h122 : W3Lem122Two) (h : Cex156 M V₀ V U S A X T) : False := by
  haveI : Fact (IsElemAbelian 2 (eSub V₀ X T)) := ⟨h.isElemAbelian_eSub⟩
  obtain ⟨⟨n, hn⟩, hBorel⟩ := five_nine_borel hB h.min.toPairAt h.isElemAbelian_A
    (h.cex.isKGroup_of_le h.std h.X_le_H) h.two_lt_relIndex
  have hK := h.ker_le_centralizer hMult hn
  have hn2 : 2 ≤ n := one_lt_of_isPSL_or_isSz hn
  obtain ⟨r, hr, hr2, q, hq, hqo⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      ∃ q ∈ kerQuotImg M X M, orderOf q = r := by
    rcases hn with hn' | hn'
    · exact exists_odd_order_mem_borel_psl2 hn2 (isPSL_congr Subgroup.topEquiv.symm hn') hBorel
    · exact exists_odd_order_mem_borel_sz (isSz_congr Subgroup.topEquiv.symm hn') hBorel
  obtain ⟨x, rfl⟩ := kerQuotMk_surjective M X q
  have hxM : (x : G) ∈ M := (kerQuotMk_mem_kerQuotImg_iff x).1 hq
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk, hP, hqk⟩ := exists_pow_isPGroup_orderOf_map_eq (kerQuotMk M X) x.2 hr hqo
  have hodd : Odd (orderOf (kerQuotMk M X ⟨(x : G) ^ k, hk⟩)) := by
    rw [hqk]
    exact hr.odd_of_ne_two hr2
  have hne : kerQuotMk M X ⟨(x : G) ^ k, hk⟩ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hqk
    exact hr.ne_one hqk.symm
  have hxkM : (x : G) ^ k ∈ M := M.pow_mem hxM k
  exact h.cex.false_of_fixedPointFree hr2 (h.X_le_H hk) hxkM hP
    (h.fixedPointFree h122 hn hBorel hK hk hxkM hodd hne)

end Cex156

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem not_le_pCoreOf_centralizer (hB : Asc80ThmB)
    (hMult : SchurMultiplierInput) (h122 : W3Lem122Two) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) : ¬ V₀ ≤ pCoreOf 2 (centralizer (U : Set G)) := by
  intro hCH
  obtain ⟨A, X, hmin⟩ := h.exists_isMinPair156
  have hA2 : IsPGroup 2 A := by
    obtain ⟨g, rfl⟩ := hmin.pair.conj
    exact (isElemAbelian_conjSubgroup' h.hyp.elemAbelian₀ g).isPGroup
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hmin.pair.A_le hA2
  exact Cex156.contradiction hB hMult h122 ⟨hS, h, hCH, hmin, hT, hAT⟩

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
