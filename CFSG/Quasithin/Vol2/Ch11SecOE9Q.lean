module

public import CFSG.Quasithin.Vol2.Ch11SecOE9P
public import CFSG.Quasithin.Vol2.Ch11SecOE7A
public import CFSG.Quasithin.Vol2.Ch11SecOE9N

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCRootAxis


namespace Sp4

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} [L.Normal] (ψ : antiSp K ≃* ↥L)

theorem exists_member (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hAS : AlmostSimple L) (hT : IsSylowIn 2 T ⊤)
    (hψ : (antiUnipotent K).map ψ.toMonoidHom = (T ⊓ L).subgroupOf L) {A : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hcA : 2 ^ n < Nat.card A) :
    ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ X : Subgroup G,
      E1.IsE n ⊤ T (A1b.conjSub g A) X ∧ ¬ Group.IsSolvable ↥X := by
  have hone : ∀ X : Subgroup G, E1.IsE n ⊤ T A X → ¬ Group.IsSolvable ↥X →
      ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ X : Subgroup G,
        E1.IsE n ⊤ T (A1b.conjSub g A) X ∧ ¬ Group.IsSolvable ↥X := fun X hX hXs =>
    ⟨1, by rwa [A1b.conjSub_one], X, by rwa [A1b.conjSub_one], hXs⟩
  by_cases hZ : A.comap (emb ψ) ≤ antiUnipotentCenter K
  · by_cases hAL : A ≤ L
    · exact exists_member_of_le_center ψ hK hn hAS hT hψ hA hcA hAL hZ
    · rcases Nat.even_or_odd n with hev | ⟨m, rfl⟩
      · obtain ⟨X, hX, hXs⟩ := exists_member_of_not_le_even ψ hK hn hev hAS hT hψ hAT hA hcA
          hAL hZ
        exact hone X hX hXs
      · exact exists_member_of_not_le_odd hAS hT (by omega) hK ψ hA hcA hAL
  · obtain ⟨i, hi⟩ := exists_rootA_of_comap ψ hψ hAT hA
    have hij : ∃ j : Axis, (i = .one ∧ j = .two) ∨ (i = .two ∧ j = .one) := by
      cases i
      · exact ⟨.two, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨.one, Or.inr ⟨rfl, rfl⟩⟩
    obtain ⟨j, hij⟩ := hij
    obtain ⟨X, hX, hXs⟩ := exists_member_of_not_le_center ψ hK hn hAS hT hψ hAT hA hij hi hZ
    exact hone X hX hXs

end Sp4

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_isPSp4_of_twisted {T : Subgroup G} {n : ℕ}
    (hS : IsPSp4 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (htw : E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
      (T ⊓ CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hn1, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hS
  have hn : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact hne (by simp)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  set L := CFSG.generalizedFitting G with hLdef
  set e' : antiSp K ≃* ↥L := (e.trans (antiProjEquiv K).symm).symm with he'
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    apply Sp4.not_isSolvable_parC hK hn .one
    exact Group.isSolvable_of_comm fun x y => Subtype.ext (e'.injective (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hc]))
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT.1 hFT
  have hLn := hAS.normal
  have hTsyl : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  obtain ⟨ψ, hψ⟩ := Sp4.exists_equiv_antiUnipotent e' hTsyl
  set D := Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) with hD
  have hTD : T ≤ D := SecE3.le_normalizer_inf
  have hDc := Sp4.isCoatom_normalizer ψ hK hn hψ hFT (Sp4.exists_swap ψ hK hn hψ hTsyl htw)
  have hDs := Sp4.isSolvable_normalizer ψ hK hn hψ hAS.two
  have hDE : E1.InEFor n D T := by
    have h1 : E1.InE 1 D :=
      (E1.nParam_le_iff Nat.one_pos).mp (by exact_mod_cast E1.solvable_nParam_le_one hDs)
    exact (h1 T (B6.isSylowTwoOf_mono hTsyl hTD le_top)).mono (by omega)
  have hInE := inEFor_top_of_coatom_conj hTsyl hTD hDE hDc
    (fun A _ hA1 hc => SecE3.isE_top_of_card_le hAS hTsyl hA1 hc)
    (fun A hAT hA hc => by
      obtain ⟨g, hg, X, hX, hXs⟩ := Sp4.exists_member ψ hK hn hAS hTsyl hψ hAT hA hc
      exact ⟨g, hg, X, hX, fun hle => hXs
        (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))⟩)
  exact (E1.nParam_le_iff (by omega)).mpr ((E1.inE_iff_inEFor hTsyl).mpr hInE)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
