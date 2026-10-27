module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3Nrm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3E1c

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9z4_lemma_14_6_16 (h35 : Lemma1435) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (iS : Input14614NoSz) (h14 : Stage14614E9) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p)
    {R₁ R₂ : Subgroup G} {s : G} (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) ⊓
      mcOf T = T := by
  have hP3a := e9z4_normalizer_inf_eq h35 S hred hshape hdat
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  rcases h14 G T M S H PQ p hred hmax hshape with hC | hC | hC
  · exact e9z4_normalizer_eq_of_C1 h35 S hred hshape hdat hC
  · have hle := e9z4_normalizer_le h35 h36 hlist iS S hred hmax hshape (Or.inl hC) hdat
    exact le_antisymm ((le_inf inf_le_left hle).trans hP3a.le)
      (le_inf (hP3a.ge.trans inf_le_left) hTG)
  · have hle := e9z4_normalizer_le h35 h36 hlist iS S hred hmax hshape (Or.inr hC) hdat
    exact le_antisymm ((le_inf inf_le_left hle).trans hP3a.le)
      (le_inf (hP3a.ge.trans inf_le_left) hTG)

end Main

end CFSG.Quasithin
