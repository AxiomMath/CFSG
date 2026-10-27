module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsD
public import CFSG.Quasithin.Background.HF166B
public import CFSG.Quasithin.Background.HF1607M22B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

@[expose] def HTab82Nine : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
    ∀ n : ℕ, 1 ≤ n → BinaryNineTensor L ⊤ ⊥ n →
      CFSG.Open.pRank 2 M ≤ 4 * n ∧ ((4 * n : ℕ) : ℕ∞) ≤ betaH M ∧
        (n = 1 → (5 : ℕ∞) ≤ alphaE M) ∧ (1 < n → alphaE M = ⊤)

@[expose] def HOffNormal82L3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
    ∀ S A : Subgroup (MulAut V), S ≤ M → IsPGroup 2 ↥S → ¬ 2 ∣ S.relIndex M → A ≤ S →
      IsElemAbelian2 A → BinaryNineTensor L ⊤ ⊥ 1 → rk ↥A = 4 → rk ↥(fixV A) = 4 →
      S ≤ Subgroup.normalizer (A : Set (MulAut V))

theorem le_alphaE_of {V : Type} [CommGroup V] [Finite V] {M : Subgroup (MulAut V)} {b : ℕ}
    (h : ∀ k ∈ alphaSet M, b ≤ k) : (b : ℕ∞) ≤ alphaE M :=
  le_iInf₂ fun k hk => by exact_mod_cast h k hk

theorem hCode82_holds :
    HCode82 := by
  intro V _ _ L M hLM
  refine ⟨fun h => ⟨fun x hxM hx1 hxo hx6 => code24_odd_fact hLM h hxM hx1 hxo hx6,
    fun Y hYM hY3 hY6 => code24_h1606 hLM h hYM hY3 hY6⟩, ?_⟩
  rintro (h | h) s hs A Y hAM hYM hAe hAc hYc hAY
  · exact code22_h1607 hLM h hs hAM hYM hAe hAc hYc
  · exact code24_h1607 hLM h hs hAM hAe hAc hYc hAY

theorem hTab82_of
    (h9 : HTab82Nine) : HTab82 := by
  intro V _ _ L M hLM
  refine ⟨h9 V L M hLM, fun h => ⟨?_, code22_betaH hLM h, le_alphaE_of (code22_alphaSet hLM h)⟩,
    fun h => ⟨?_, code24_betaH hLM h, le_alphaE_of (code24_alphaSet hLM h)⟩⟩
  · exact pRank_le_of_card_le fun A hAM hAe k hk => code22_card_le hLM h hAM hAe hk
  · exact pRank_le_of_card_le fun A hAM hAe k hk => code24_card_le hLM h hAM hAe hk

theorem card_eq_two_pow_rk_of {V : Type} [CommGroup V] [Finite V] {A : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) : Nat.card A = 2 ^ rk ↥A := by
  have : Finite (MulAut V) := finite_mulAut V
  exact card_eq_two_pow_of_isPGroup
    (isPGroup_two_of_sq_eq_one fun a => Subtype.ext (hA.2 a a.2))

theorem hOffNormal82_of
    (hL : HOffNormal82L3) : HOffNormal82 := by
  intro V _ _ L M hLM S A hSM hS hodd hAS hAe hcase
  rcases hcase with ⟨h, hA4, hfix⟩ | ⟨h, hA5, -⟩ | ⟨h, hA6, -⟩ | ⟨h, hA6, -⟩
  · exact hL V L M hLM S A hSM hS hodd hAS hAe h hA4 hfix
  · exact code22_le_normalizer hLM h hSM hS hAS hAe (by rw [card_eq_two_pow_rk_of hAe, hA5])
  · exact code24_le_normalizer hLM h hSM hS hAS hAe (by rw [card_eq_two_pow_rk_of hAe, hA6])
  · exact cocode24_le_normalizer hLM h hSM hS hAS hAe (by rw [card_eq_two_pow_rk_of hAe, hA6])

end CFSG.Quasithin.H13
