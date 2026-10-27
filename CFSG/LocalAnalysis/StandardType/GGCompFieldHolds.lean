module

public import CFSG.LocalAnalysis.StandardType.GGCompFieldCatalogue

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.TwistedE6
open CFSG.Assembly (isComponentOf_iff_open)

theorem ggCompFieldDataQ_dvd
    {G : Type} [Group G] {q : ℕ} {X : Subgroup G}
    (h : GGCompFieldDataQ q X) {p : ℕ} (hp : p.Prime) (hpq : p ∣ q ^ 2 - 1) :
    p ∣ Nat.card ↥X := by
  rcases h with ⟨m, hm, hQ⟩ | ⟨rfl, hX⟩
  · exact hpq.trans ((sq_sub_one_dvd_pow_sq_sub_one q m).trans
      (ggCompFieldAt_dvd hQ))
  · have h3 : p ∣ 3 := by simpa using hpq
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    refine Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (Subgroup.center ↥X))
    rcases hX with h | h <;> rw [h] <;> norm_num

theorem ggCompFieldDataQ_notExcThree
    {G : Type} [Group G] {q : ℕ} {X : Subgroup G}
    (h : GGCompFieldDataQ q X) (hq : 4 ≤ q) : GGNotExcThreeOrder (ggCQ X) := by
  rcases h with ⟨m, hm, hQ⟩ | ⟨rfl, -⟩
  · exact ggCompFieldAt_notExcThree hQ (hq.trans (Nat.le_self_pow (by omega) q))
  · omega

theorem ggLayerPDivExcRestNs_holds
    : GGLayerPDivExcRestNs := by
  have hc : ∀ f : ℕ, 1 ≤ f → Nat.card (GaloisField 2 f) = 2 ^ f := fun f hf =>
    GaloisField.card 2 f (by omega)
  have hsq : ∀ f p : ℕ, (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) → p ∣ (2 ^ f) ^ 2 - 1 := by
    intro f p h
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ h1
    have e : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      zify [h1, h2]
      ring
    rw [e]
    exact h.elim (fun h => h.mul_right _) (fun h => h.mul_left _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf p hp hp2 hpq a ha _ _ X hX
    exact ggCompFieldDataQ_dvd (ggExcCompFieldInputQ (Or.inl rfl) (GaloisField 2 f) p hp hp2 a ha
      X (isComponentOf_iff_open.1 hX)) hp (by rw [hc f hf]; exact hsq f p (Or.inr hpq))
  · intro f hf p hp hp2 hpq α hα hαp _ _ X hX
    exact ggCompFieldDataQ_dvd (ggE6CompFieldInputQ (GaloisField 2 f) p hp hp2 α hα hαp X
      (isComponentOf_iff_open.1 hX)) hp
      (by rw [hc f hf]; exact hsq f p (hpq.elim (fun h => Or.inl h.1) Or.inr))
  · intro f hf p hp hp2 hpq a ha _ _ X hX
    exact ggCompFieldDataQ_dvd (ggExcCompFieldInputQ (Or.inr (Or.inl rfl)) (GaloisField 2 f) p hp
      hp2 a ha X (isComponentOf_iff_open.1 hX)) hp
      (by rw [hc f hf]; exact hsq f p (Or.inr hpq))
  · intro f hf p hp hp2 hpq a ha _ _ X hX
    exact ggCompFieldDataQ_dvd (ggExcCompFieldInputQ (Or.inr (Or.inr rfl)) (GaloisField 2 f) p hp
      hp2 a ha X (isComponentOf_iff_open.1 hX)) hp
      (by rw [hc f hf]; exact hsq f p (Or.inr hpq))
  · intro f hf p hp hp2 hpq α hα hαp X hX
    exact ggCompFieldDataQ_dvd (ggTwE6CompFieldInputQ f hf p hp hp2 α hα hαp X
      (isComponentOf_iff_open.1 hX)) hp (hsq f p hpq)

theorem ggLayerNotExcThreeRestNsNonToral_holds
    : GGLayerNotExcThreeRestNsNonToral := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K _ _ _ hK p hp hp2 _ s hs _ C hC
    exact ggCompFieldDataQ_notExcThree
      (ggExcCompFieldInputQ (Or.inl rfl) K p hp hp2 s hs C (isComponentOf_iff_open.1 hC)) hK
  · intro K _ _ _ hK p hp hp2 _ s hs _ C hC
    exact ggCompFieldDataQ_notExcThree
      (ggExcCompFieldInputQ (Or.inr (Or.inl rfl)) K p hp hp2 s hs C
        (isComponentOf_iff_open.1 hC)) hK
  · intro K _ _ _ hK p hp hp2 _ s hs _ C hC
    exact ggCompFieldDataQ_notExcThree
      (ggExcCompFieldInputQ (Or.inr (Or.inr rfl)) K p hp hp2 s hs C
        (isComponentOf_iff_open.1 hC)) hK
  · intro K _ _ _ hK p hp hp2 _ α hα hαp _ X hX
    exact ggCompFieldDataQ_notExcThree
      (ggE6CompFieldInputQ K p hp hp2 α hα hαp X (isComponentOf_iff_open.1 hX)) hK
  · intro f hf p hp hp2 α hα hαp X hX
    exact ggCompFieldDataQ_notExcThree
      (ggTwE6CompFieldInputQ f (by omega) p hp hp2 α hα hαp X (isComponentOf_iff_open.1 hX))
      (calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end CFSG.StandardType
