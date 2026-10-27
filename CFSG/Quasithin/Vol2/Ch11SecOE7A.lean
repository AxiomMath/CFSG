module

public import CFSG.Quasithin.Vol2.Ch11SecU1Crit

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1

variable {G : Type} [Group G] [Finite G]

theorem inEFor_top_of_conj_sup {n : ℕ} {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hTD : T ≤ D) (hD : InEFor n D T)
    (hsmall : ∀ A : Subgroup G, A ≤ T → A ≠ ⊥ → Nat.card A ≤ 2 ^ n → IsE n ⊤ T A ⊤)
    (hK : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → 2 ^ n < Nat.card A →
      ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ K : Subgroup G, IsE n ⊤ T (A1b.conjSub g A) K ∧
        D ⊔ K = ⊤) :
    InEFor n ⊤ T := by
  intro Ω hΩ
  refine eq_top_iff.mpr ?_
  by_cases hbig : ∃ A ∈ Ω, A ≤ T ∧ A ≠ ⊥
  · obtain ⟨A, hA, hAT, hA1⟩ := hbig
    by_cases hc : Nat.card A ≤ 2 ^ n
    · exact (le_eGen hA hAT (hsmall A hAT hA1 hc)).trans le_sup_left
    · obtain ⟨g, hgT, K, hK1, hK2⟩ := hK A hAT (hΩ.isElemAbelian A hA) (not_le.mp hc)
      have hA' : A1b.conjSub g A ∈ Ω := hΩ.conj A hA g (Subgroup.mem_top g)
      have hDX := le_eGen_sup_normalizer_of_inEFor hT hTD hD hΩ
      have hKX := (le_eGen hA' hgT hK1).trans (le_sup_left :
        eGen n ⊤ T Ω ≤ eGen n ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)))
      exact hK2.symm.le.trans (sup_le hDX hKX)
  · push Not at hbig
    have hW : weakClosure T Ω = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => (hbig A hA hAT).le)
    rw [hW, Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq]
    exact le_sup_right

theorem inEFor_top_of_coatom_conj {n : ℕ} {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hTD : T ≤ D) (hD : InEFor n D T) (hDc : IsCoatom D)
    (hsmall : ∀ A : Subgroup G, A ≤ T → A ≠ ⊥ → Nat.card A ≤ 2 ^ n → IsE n ⊤ T A ⊤)
    (hK : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → 2 ^ n < Nat.card A →
      ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ K : Subgroup G, IsE n ⊤ T (A1b.conjSub g A) K ∧
        ¬ K ≤ D) :
    InEFor n ⊤ T := by
  refine inEFor_top_of_conj_sup hT hTD hD hsmall fun A hAT hA hc => ?_
  obtain ⟨g, hgT, K, hK1, hK2⟩ := hK A hAT hA hc
  exact ⟨g, hgT, K, hK1, hDc.2 _ (lt_of_le_of_ne le_sup_left fun h => hK2 (h ▸ le_sup_right))⟩

omit [Finite G] in
theorem weakClosure_le (T : Subgroup G) (Ω : Set (Subgroup G)) : weakClosure T Ω ≤ T :=
  iSup₂_le fun _ _ => iSup_le fun h => h

omit [Finite G] in
theorem isInvColl_conj {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsInvColl ⊤ {B | ∃ g : G, B = A1b.conjSub g A} := by
  refine ⟨fun _ _ => le_top, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact SecU1.isElemAbelian_conjSub hA g
  · rintro _ ⟨g, rfl⟩ h -
    exact ⟨h * g, by rw [A1b.conjSub_mul]⟩

theorem le_nParam_of_forall_not_isE {n : ℕ} {T A : Subgroup G} (hn : 2 ≤ n)
    (hT : IsSylowIn 2 T ⊤) (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hno : ∀ g : G, A1b.conjSub g A ≤ T → ∀ K : Subgroup G,
      ¬ IsE (n - 1) ⊤ T (A1b.conjSub g A) K) :
    (n : ℕ∞) ≤ nParam (⊤ : Subgroup G) := by
  set Ω : Set (Subgroup G) := {B | ∃ g : G, B = A1b.conjSub g A} with hΩdef
  have hΩ : IsInvColl ⊤ Ω := isInvColl_conj hA
  have hAΩ : A ∈ Ω := ⟨1, (A1b.conjSub_one A).symm⟩
  have hE : eGen (n - 1) ⊤ T Ω = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun K hK => ?_)
    obtain ⟨g, rfl⟩ := hB
    exact absurd hK (hno g hBT K)
  have hnot : ¬ InEFor (n - 1) ⊤ T := by
    intro h
    have h1 := h Ω hΩ
    rw [hE, bot_sup_eq, top_inf_eq, Subgroup.normalizer_eq_top_iff] at h1
    have hW2 : IsPGroup 2 (weakClosure T Ω) := hT.2.1.to_le (weakClosure_le T Ω)
    have hW := hO2 _ h1 hW2
    exact hA1 (le_bot_iff.mp (hW ▸ le_weakClosure hAΩ hAT))
  by_contra hlt
  rw [not_le] at hlt
  have hn' : (n : ℕ∞) = ((n - 1 : ℕ) : ℕ∞) + 1 := by
    rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm]
    simp
  rw [hn', ENat.lt_add_one_iff (ENat.natCast_ne_top _)] at hlt
  exact hnot ((nParam_le_iff (by omega)).1 hlt T hT)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
