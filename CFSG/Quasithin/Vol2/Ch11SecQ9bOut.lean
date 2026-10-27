module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bRed
public import CFSG.Quasithin.Vol2.Ch11SecA12Out
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

namespace C11P9B

theorem false_of_outerList (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hF11 : Facts11)
    (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K)
    (hS : IsPSL 2 5 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSLEps3 true 5 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsPSLEps3 true 5 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSLEps3 false 5 1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    False := by
  obtain ⟨t, ht, hout⟩ := exists_outer hFb hN h1102 h hV₁ hK hNK hLK hS
  exact false_of_outer hFb hC hF hN h1102 h hV₁ hV₂ hX
    (le_centralizer_of_cComp hF11 hN h1102 h hV₁ hK hLK)
    ((xOne_le_normalizer_V1 hN h1102 h hV₁ hX).trans hNK) ht hout

theorem false_of_rank3 (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hF11 : Facts11)
    (hN : NatFacts) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₁ < K)
    (hS : IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 7)) ∨
      IsSporadic .M22 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSporadic .J2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsSporadic .J4 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSporadic .HS (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsSporadic .Ru (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSLEps3 false 5 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsPSLEps3 false 5 1 (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  obtain ⟨hQ, hZ, hrk, hL3⟩ := hFb.list3.1 _ hS
  obtain ⟨s, p, e, hp, he, hP⟩ := isPSLEps3_of_a318 hC hF hF11 hN h318 h36 h38 h1102 h hV₁ hV₂
    hX hK hNK hlt hQ hZ hrk
  obtain ⟨rfl, rfl, rfl⟩ := hL3 s p e hp he hP
  exact false_of_outerList hFb hC hF hF11 hN h1102 h hV₁ hV₂ hX hK hNK hlt.le
    (Or.inr (Or.inr (Or.inr hP)))

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
