module

public import CFSG.Quasithin.Vol2.Ch3Sec1Lem317
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm316

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

structure Hyp318 (T M L₀ V : Subgroup G) : Prop where
  inM : InM T M
  nonempty : ∃ H : Subgroup G, IsHStar T M H
  perfect : L₀ = oTwoUpper L₀
  le_M : L₀ ≤ M
  normal : M ≤ Subgroup.normalizer (L₀ : Set G)
  unique : IsUniqueM (L₀ ⊔ T) M
  reduced : IsTwoReducedIn (L₀ ⊔ T) V
  centralizer : pCoreOf 2 (L₀ ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G)

section Prelim

variable {T M L₀ V : Subgroup G}

theorem oTwoUpper_sup_eq_of_normal {L₀ T : Subgroup G} (hL : L₀ = oTwoUpper L₀)
    (hT2 : IsPGroup 2 T) (hTn : T ≤ Subgroup.normalizer (L₀ : Set G)) :
    oTwoUpper (L₀ ⊔ T) = L₀ := by
  apply le_antisymm
  · exact oTwoUpper_le_of_pow_mem
      (B6.isTwoQuotient_of_sup_eq hT2 (sup_le Subgroup.le_normalizer hTn) (sup_comm _ _))
  · calc L₀ = oTwoUpper L₀ := hL
      _ ≤ oTwoUpper (L₀ ⊔ T) := oTwoUpper_mono le_sup_left

theorem pCoreOf_sup_eq_bot_of_isUniqueM {M₀ H M : Subgroup G} (hMu : IsUniqueM M₀ M)
    (hH : ¬ H ≤ M) : pCoreOf 2 (M₀ ⊔ H) = ⊥ := by
  by_contra hne
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (M₀ ⊔ H) : Set G)) :=
    ⟨pCoreOf 2 (M₀ ⊔ H), hne, pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨M', hM'max, hle⟩ := exists_maxTwoLocal_ge hloc
  have hsupN : M₀ ⊔ H ≤ M' := (le_normalizer_pCoreOf 2 (M₀ ⊔ H)).trans hle
  have hM'eq : M' = M := hMu.2 M' ⟨hM'max, le_sup_left.trans hsupN⟩
  exact hH (hM'eq ▸ (le_sup_right.trans hsupN))

theorem Hyp318.hyp315 (hT : quasithinIsSylowTwo T) (h : Hyp318 T M L₀ V) {H : Subgroup G}
    (hH : IsHStar T M H) : Hyp315 T M (L₀ ⊔ T) H V := by
  have hTM : T ≤ M := le_sup_right.trans h.unique.1.2
  have hTn : T ≤ Subgroup.normalizer (L₀ : Set G) := hTM.trans h.normal
  refine ⟨⟨le_sup_right, h.unique.1.2, hH, h.reduced, h.centralizer⟩, Or.inl ?_⟩
  show H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (L₀ ⊔ T) : Set G)
  rw [oTwoUpper_sup_eq_of_normal h.perfect hT.1 hTn]
  exact inf_le_right.trans h.normal

theorem Hyp318.not_exists_normal (h : Hyp318 T M L₀ V) {H : Subgroup G} (hH : IsHStar T M H) :
    ¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 (L₀ ⊔ T) ∧
      (L₀ ⊔ T) ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  rintro ⟨R₀, hR₀, hle, hnorm⟩
  have hR₀sup : R₀ ≤ (L₀ ⊔ T) ⊔ H := (hle.trans (pCoreOf_le 2 _)).trans le_sup_left
  have h1 : R₀ ≤ pCoreOf 2 ((L₀ ⊔ T) ⊔ H) :=
    le_pCoreOf_of_le_normalizer 2 hR₀sup hnorm ((pCoreOf_isPGroup 2 _).to_le hle)
  rw [pCoreOf_sup_eq_bot_of_isUniqueM h.unique hH.2.1, le_bot_iff] at h1
  exact hR₀ h1

end Prelim

section Main

variable {T M L₀ V : Subgroup G}

theorem theorem318_one (hC58 : TheoremC58) (hD15 : D15Used) (hB : B513) (hE213 : E213Three)
    (hE215 : E215) (h316 : AS316Sylow) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T) (h : Hyp318 T M L₀ V) :
    qhatInt (L₀ ⊔ T) V h.reduced.2.2.1 ≤ 2 := by
  obtain ⟨H, hH⟩ := h.nonempty
  rcases theorem316 hC58 hD15 hB hE213 hE215 h316 hs hnab hK hT h.inM (h.hyp315 hT hH) with
    h1 | ⟨-, h2, -⟩ | h3
  · exact absurd h1 (h.not_exists_normal hH)
  · exact h2
  · exact (qhatInt_le_qInt _ _ _).trans h3

theorem theorem318_two (hC58 : TheoremC58) (hD15 : D15Used) (hB : B513) (hE213 : E213Three)
    (hE215 : E215) (h316 : AS316Sylow) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T) (h : Hyp318 T M L₀ V) :
    qInt (L₀ ⊔ T) V h.reduced.2.2.1 ≤ 2 ∨
      ((∀ H : Subgroup G, IsHStar T M H → ¬ V ≤ pCoreOf 2 H) ∧
        (IsTISetIn V M → qhatInt (L₀ ⊔ T) V h.reduced.2.2.1 < 2)) := by
  by_cases hq : qInt (L₀ ⊔ T) V h.reduced.2.2.1 ≤ 2
  · exact Or.inl hq
  right
  have key : ∀ H : Subgroup G, IsHStar T M H →
      ¬ V ≤ pCoreOf 2 H ∧ (IsTISetIn V M → qhatInt (L₀ ⊔ T) V h.reduced.2.2.1 < 2) := by
    intro H hH
    rcases theorem316 hC58 hD15 hB hE213 hE215 h316 hs hnab hK hT h.inM (h.hyp315 hT hH) with
      h1 | ⟨h2, -, h3⟩ | h3
    · exact absurd h1 (h.not_exists_normal hH)
    · exact ⟨h2, h3⟩
    · exact absurd h3 hq
  obtain ⟨H₀, hH₀⟩ := h.nonempty
  exact ⟨fun H hH => (key H hH).1, (key H₀ hH₀).2⟩

theorem theorem318_three (hC58 : TheoremC58) (h317 : AS317Sylow) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (h : Hyp318 T M L₀ V) :
    (¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) ∧
        IsFFInt (L₀ ⊔ T) V h.reduced.2.2.1) ∨
      (thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) ∧
        (∀ H : Subgroup G, IsHStar T M H → quasithinOmegaOneCenter T ≤ centerOf H) ∧
        centerOf (L₀ ⊔ T) = ⊥) := by
  by_cases hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)
  · right
    have key : ∀ H : Subgroup G, IsHStar T M H →
        quasithinOmegaOneCenter T ≤ centerOf H ∧ centerOf (L₀ ⊔ T) = ⊥ := by
      intro H hH
      rcases lemma317 hC58 h317 hs hnab hK hT h.inM (h.hyp315 hT hH) (h.centralizer ▸ hJ) with
        h1 | ⟨R₀, h1, h2, h3⟩
      · exact h1
      · exact absurd ⟨R₀, h1, h2, h3⟩ (h.not_exists_normal hH)
    obtain ⟨H₀, hH₀⟩ := h.nonempty
    exact ⟨hJ, fun H hH => (key H hH).1, (key H₀ hH₀).2⟩
  · left
    refine ⟨hJ, ?_⟩
    have hV := h.reduced.2.2.1
    have hVT : V ≤ T :=
      (A4.le_pCoreOf_of_isTwoReducedIn h.reduced).trans (h.centralizer ▸ inf_le_left)
    obtain ⟨A, hA, hAC⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
        ¬ A ≤ Subgroup.centralizer (V : Set G) := by
      by_contra hall
      push Not at hall
      exact hJ (iSup₂_le fun A hA => le_inf hA.1 (hall A hA))
    exact isFFModule_autOn hV hVT h.reduced.2.1 (hA.1.trans le_sup_right) hA hAC

end Main

end CFSG.Quasithin
