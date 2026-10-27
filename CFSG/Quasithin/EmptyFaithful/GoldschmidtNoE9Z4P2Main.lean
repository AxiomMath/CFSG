module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2E2b
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2E3b
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ExAut
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ExL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2SolE9
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2E3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem stage14614E9_of_inputs (h35 : Lemma1435)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (iL : Input14614ListsE9) : Stage14614E9 := by
  intro G _ _ T M S H PQ p hred hmax hshape
  by_cases hKz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H
  · exact Or.inl (stage14614C1_of_eq_E9 h35 h36 h37 hlist S hred hmax hshape hKz)
  · obtain ⟨K₁, hK₁, ⟨s, hsT, hsN, hKz', hcase⟩ | ⟨hKz', hcase⟩⟩ :=
      iL G T M S H PQ p hred hmax hshape hKz
    · rcases hcase with ⟨m, hm, hpm, e⟩ | e
      · exact Or.inr (Or.inr
          (e9_caseE3 h36 hlist iS S hred hmax hshape hK₁ hsT hsN hKz' hm hpm e))
      · exact (e9_not_caseL3 h35 h36 hlist iS S hred hmax hshape hK₁ hsT hsN hKz' e).elim
    · rcases hcase with ⟨n, hn, hne, e⟩ | ⟨n, hn, e⟩
      · exact Or.inr (Or.inl (e9_caseE2 h35 h36 hlist iS S hred hmax hshape hK₁ hKz' hn hne e))
      · exact (e9_not_caseAutLn h35 S hred hshape hK₁ hKz' hn e).elim

theorem e9z4_normalizer_le (h35 : Lemma1435) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p)
    (hC : Stage14614E9C2 T H ∨ Stage14614E9C3 T H) {R₁ R₂ : Subgroup G} {s : G}
    (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) ⊓
      mcOf T ≤ H := by
  have h1 : pCoreOf 2 H ≤ T ⊓ Subgroup.normalizer (R₁ : Set G) :=
    le_inf (S.pCoreOf_le_T hred.isHTM) (hdat.plane₁.1.trans Subgroup.le_normalizer)
  have h2 : T ⊓ Subgroup.normalizer (R₁ : Set G) ≤ T := inf_le_left
  rcases hC with hC | hC
  · exact e9_normalizer_le_of_E2 h35 h36 hlist iS S hred hmax hshape hC h1 h2
  · exact e9_normalizer_le_of_E3 h35 h36 hlist iS S hred hmax hshape hC h1 h2

theorem e9z4_oTwoUpper_le_fstar (h14 : Stage14614E9) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p) :
    oTwoUpper H ≤ oTwoFstarIn (mcOf T) := by
  rcases h14 G T M S H PQ p hred hmax hshape with hC | hC | hC
  · exact e9z4_fstar_of_C1 S hred hC
  · exact e9_fstar_of_E2 S hred hC
  · exact e9_fstar_of_E3 S hred hC

end Main

end CFSG.Quasithin
