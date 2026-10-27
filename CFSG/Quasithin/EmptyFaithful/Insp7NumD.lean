module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumC
public import CFSG.Quasithin.EmptyFaithful.Insp7NumA

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

theorem listCases_cases
    {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (h : ListCases L) :
    BigDvd L ∨ SmallLie L ∨ LargeReeTits L ∨ OddFam L ∨ SporSmall L := by
  rcases h with ⟨hs, hA⟩ | ⟨hne, hc, hB⟩ | hE | ⟨s, hs, ⟨e⟩⟩
  · rcases lieCharTwo_cases hq hs hA with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases hB with hL34 | hG24
    · exact Or.inr (Or.inl (by unfold SmallLie; tauto))
    · refine Or.inl (bigDvd_of_cover hq ?_)
      rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG24]
      exact (pow_dvd_pow 2 (by norm_num : 9 ≤ 6 * 2)).trans two_pow_dvd_ordG2
  · exact Or.inr (Or.inr (Or.inr (Or.inl hE)))
  · have hcard : Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card (NativeSporadic.Carrier s) :=
      Nat.card_congr e.toEquiv
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Or.inl rfl, ⟨e⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Or.inr (Or.inl rfl), ⟨e⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Or.inr (Or.inr (Or.inl rfl)), ⟨e⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), ⟨e⟩⟩)))
    · exact Or.inl (bigDvd_of_cover hq (by rw [hcard]; exact hbig _ (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Or.inr (Or.inr (Or.inr (Or.inr rfl))), ⟨e⟩⟩)))
    · exact Or.inl (bigDvd_of_cover hq (by rw [hcard]; exact hbig _ (Or.inr (Or.inl rfl))))
    · exact Or.inl (bigDvd_of_cover hq
        (by rw [hcard]; exact hbig _ (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inl (bigDvd_of_cover hq
        (by rw [hcard]; exact hbig _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact Or.inl (bigDvd_of_cover hq
        (by rw [hcard]; exact hbig _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem numFactAt_listCases
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallLie) (hT : NumFactAt LargeReeTits)
    (hO : NumFactAt OddFam) (hP : NumFactAt SporSmall) : NumFactAt ListCases := by
  intro L _ _ hq hlist z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  rcases listCases_cases hq hbig hlist with hb | hs | ht | ho | hp
  · exact numFactAt_of_big (F := fun L _ => BigDvd L) (fun L _ _ _ h => h) L hq hb z hz2 hzc Gc ρ
      hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hS L hq hs z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hT L hq ht z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hO L hq ho z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hP L hq hp z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard

theorem inspNum_of_residuals
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallLie) (hT : NumFactAt LargeReeTits)
    (hO : NumFactAt OddFam) (hP : NumFactAt SporSmall) : InspNum :=
  inspNum_iff.mpr (inspAt_of_numFactAt (numFactAt_listCases hbig hS hT hO hP))

theorem lemma14320Inspect_of_residuals
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallLie) (hT : NumFactAt LargeReeTits)
    (hO : NumFactAt OddFam) (hP : NumFactAt SporSmall) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_num (inspNum_of_residuals hbig hS hT hO hP)

end Insp7

end CFSG.Quasithin
