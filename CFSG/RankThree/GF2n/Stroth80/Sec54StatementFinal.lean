module

public import CFSG.RankThree.GF2n.Stroth80.Sec54Fix
public import CFSG.RankThree.GF2n.Stroth80.Sec54FixD

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth54Statement_of_hcomm (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement)
    (hcomm : ∀ (_G : Type) [Group _G] [Finite _G] (_M _Q _Z _B : Subgroup _G) (hc : Ctx _M _Q _Z _B)
      (_n : ℕ) (_t : _G) (_m : ℕ), Sec5Hyp hc _n _t → 2 ≤ _m → SpMNat hc _t _m →
      Nat.card ↥(hc.CN _t) = Nat.card _Q * Nat.card _Z →
      ∀ s ∈ Rt _M (LB _M _Q _B) _t,
        ∀ x ∈ Wt _Q (Vt _M (LB _M _Q _B) _B _Z _t), ⁅s, x⁆ ∈ Vt _M (LB _M _Q _B) _B _Z _t) :
    Stroth54Statement :=
  stroth54Statement_of_contra h34 hRoot h51 hcomm
    (fun _G _ _ _M _Q _Z _B hc _n _t _m hs hm hV hN =>
      stroth54FC_hNW_of h34 hRoot h51 hc hs hm hV hN)


theorem stroth54Statement_holds : Stroth54Statement :=
  stroth54Statement_of_hcomm stroth34Statement_unconditional stroth310RootStatement_unconditional
    stroth51Statement_unconditional
    (fun G _ _ M Q Z B hc n t m hs hm hV hN => by
      have hsp : SpNat hc t := by
        obtain ⟨K, hK, hKf, hKc, hrep⟩ := hV
        exact ⟨K, hK, hKf, hKc, m, hm, hrep⟩
      obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_sp stroth34Statement_unconditional
        stroth310RootStatement_unconditional hs hsp
      exact sec54FC_hcomm_of stroth34Statement_unconditional stroth310RootStatement_unconditional
        stroth51Statement_unconditional hc hs hm hV hN hr hplane)
end CFSG.RankThree.GF2n.Stroth80
