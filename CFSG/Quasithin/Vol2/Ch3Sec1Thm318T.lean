module

public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.EmptyFaithful.S151Statements

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L₀ V : Subgroup G}

theorem theorem318_one_of_316 (h316 : Theorem316Statement) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (h : Hyp318 T M L₀ V) : qhatInt (L₀ ⊔ T) V h.reduced.2.2.1 ≤ 2 := by
  obtain ⟨H, hH⟩ := h.nonempty
  rcases h316 G T hs hnab hK hT M (L₀ ⊔ T) H V h.inM (h.hyp315 hT hH) with
    h1 | ⟨-, h2, -⟩ | h3
  · exact absurd h1 (h.not_exists_normal hH)
  · exact h2
  · exact (qhatInt_le_qInt _ _ _).trans h3

theorem theorem318_two_of_316 (h316 : Theorem316Statement) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (h : Hyp318 T M L₀ V) :
    qInt (L₀ ⊔ T) V h.reduced.2.2.1 ≤ 2 ∨
      ((∀ H : Subgroup G, IsHStar T M H → ¬ V ≤ pCoreOf 2 H) ∧
        (IsTISetIn V M → qhatInt (L₀ ⊔ T) V h.reduced.2.2.1 < 2)) := by
  by_cases hq : qInt (L₀ ⊔ T) V h.reduced.2.2.1 ≤ 2
  · exact Or.inl hq
  right
  have key : ∀ H : Subgroup G, IsHStar T M H →
      ¬ V ≤ pCoreOf 2 H ∧ (IsTISetIn V M → qhatInt (L₀ ⊔ T) V h.reduced.2.2.1 < 2) := by
    intro H hH
    rcases h316 G T hs hnab hK hT M (L₀ ⊔ T) H V h.inM (h.hyp315 hT hH) with
      h1 | ⟨h2, -, h3⟩ | h3
    · exact absurd h1 (h.not_exists_normal hH)
    · exact ⟨h2, h3⟩
    · exact absurd h3 hq
  obtain ⟨H₀, hH₀⟩ := h.nonempty
  exact ⟨fun H hH => (key H hH).1, (key H₀ hH₀).2⟩

end CFSG.Quasithin

end
