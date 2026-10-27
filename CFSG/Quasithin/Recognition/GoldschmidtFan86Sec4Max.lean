module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Arc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem IsTArc.pseg {a b : ℤ} (h : IsTArc T a b) : PSeg T a b :=
  ⟨h.1.le, fun hle => h.2.1 (hle.trans (T.fixer_le_subFixer _ _))⟩

theorem IsTArc.of_pseg_max (F : FanTree Γ G) (h40 : Fan40 F) {a b : ℤ} (hp : PSeg T a b)
    (hmax : ∀ a' b' : ℤ, a' ≤ a → b ≤ b' → PSeg T a' b' → a' = a ∧ b' = b) : IsTArc T a b := by
  have hab : a < b := by
    rcases lt_or_eq_of_le hp.1 with h | h
    · exact h
    · exfalso
      subst h
      have := hmax a (a + 1) le_rfl (by omega) ⟨by omega, fan42_1 T F h40 a⟩
      omega
  have hnot : ∀ a' b' : ℤ, a' ≤ a → b ≤ b' → (a' ≠ a ∨ b' ≠ b) →
      omega1 (T.subFixer a' b') ≤ T.fixer := by
    intro a' b' h1 h2 hne
    by_contra hc
    have hp' : PSeg T a' b' := ⟨by omega, hc⟩
    obtain ⟨e1, e2⟩ := hmax a' b' h1 h2 hp'
    tauto
  refine ⟨hab, fun hle => hp.2 ?_, fun hle => hp.2 ?_, hnot (a - 1) (b + 1) (by omega) (by omega)
    (Or.inl (by omega))⟩
  · refine (omega1_le_omega1_of_inv (K := T.subFixer (a - 1) b) fun x hx hx2 =>
      hle (Subgroup.subset_closure ⟨hx, hx2⟩)).trans ?_
    exact hnot (a - 1) b (by omega) le_rfl (Or.inl (by omega))
  · refine (omega1_le_omega1_of_inv (K := T.subFixer a (b + 1)) fun x hx hx2 =>
      hle (Subgroup.subset_closure ⟨hx, hx2⟩)).trans ?_
    exact hnot a (b + 1) le_rfl (by omega) (Or.inr (by omega))

theorem fan42_2a (F : FanTree Γ G) (h40 : Fan40 F) : ∃ a b : ℤ, IsTArc T a b := by
  obtain ⟨a, b, -, -, hp, hmax⟩ := T.exists_pseg_max F
    (a₀ := 0) (b₀ := 1) ⟨by omega, fan42_1 T F h40 0⟩
  exact ⟨a, b, IsTArc.of_pseg_max T F h40 hp hmax⟩

theorem fan42_2b (F : FanTree Γ G) (h40 : Fan40 F) (a b : ℤ) :
    IsMaxTArc T a b ↔ (PSeg T a b ∧ ∀ a' b' : ℤ, a' ≤ a → b ≤ b' → PSeg T a' b' →
      a' = a ∧ b' = b) := by
  constructor
  · rintro ⟨hT, hmax⟩
    refine ⟨hT.pseg T, fun a' b' h1 h2 hp' => ?_⟩
    obtain ⟨a'', b'', ha'', hb'', hp'', hm''⟩ := T.exists_pseg_max F hp'
    have hA := IsTArc.of_pseg_max T F h40 hp'' hm''
    obtain ⟨e1, e2⟩ := hmax a'' b'' (by omega) (by omega) hA
    omega
  · rintro ⟨hp, hmax⟩
    have hA := IsTArc.of_pseg_max T F h40 hp hmax
    exact ⟨hA, fun a' b' h1 h2 hA' => hmax a' b' h1 h2 (hA'.pseg T)⟩

end CFSG.Quasithin.Fan86
