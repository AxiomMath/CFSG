module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvMeet

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Λ : Type} [Group Λ]

theorem le_centralizer_biSup {ι : Type*} {p : ι → Prop} {X : ι → Subgroup Λ} {Y : Subgroup Λ}
    (h : ∀ i, p i → ⁅Y, X i⁆ = ⊥) :
    Y ≤ Subgroup.centralizer ((⨆ (i) (_ : p i), X i : Subgroup Λ) : Set Λ) := by
  rw [Subgroup.le_centralizer_iff]
  exact iSup₂_le fun i hi => Subgroup.le_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp (h i hi))

theorem commutator_biSup_eq_bot {ι : Type*} {X : ι → Subgroup Λ}
    (hX : ∀ i i', i ≠ i' → ⁅X i, X i'⁆ = ⊥) {p q : ι → Prop} (hpq : ∀ i, p i → ¬ q i) :
    ⁅⨆ (i) (_ : p i), X i, ⨆ (i) (_ : q i), X i⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine le_centralizer_biSup fun i hi => ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  exact le_centralizer_biSup fun i' hi' => hX i i' fun h => hpq i hi (h ▸ hi')

theorem opp_biSup_eq {ι : Type*} {p : ι → Prop} {X : ι → Subgroup Λ}
    (h : ∀ i, Opp 2 (X i) = X i) :
    Opp 2 (⨆ (i) (_ : p i), X i) = ⨆ (i) (_ : p i), X i :=
  le_antisymm (opp_le _) (iSup₂_le fun i hi =>
    (h i).symm.le.trans (opp_mono (le_iSup₂_of_le i hi le_rfl)))

structure TwoFamilies {r d : ℕ} (L : Fin r → Subgroup Λ) (K : Fin d → Subgroup Λ) : Prop where
  hO2 : ∀ R : Subgroup Λ, R.Normal → IsPGroup 2 R → R = ⊥
  Ln : ∀ i, (L i).Normal
  Kn : ∀ j, (K j).Normal
  L2 : ∀ i, Opp 2 (L i) = L i
  K2 : ∀ j, Opp 2 (K j) = K j
  L0 : ∀ i, L i ≠ ⊥
  K0 : ∀ j, K j ≠ ⊥
  Lc : ∀ i i', i ≠ i' → ⁅L i, L i'⁆ = ⊥
  Kc : ∀ j j', j ≠ j' → ⁅K j, K j'⁆ = ⊥
  LK : (⨆ i, L i) = ⨆ j, K j
  tits : ∀ i (N : Subgroup Λ), N.Normal → N ≤ L i → ⁅N, L i⁆ ≠ ⊥ → S17.oUpperTwo (L i) ≤ N
  ind : ∀ j (A B : Subgroup Λ), Opp 2 A = A → Opp 2 B = B → A ⊔ B = K j → ⁅A, B⁆ = ⊥ →
    A = K j ∨ B = K j

namespace TwoFamilies

variable [Finite Λ] {r d : ℕ} {L : Fin r → Subgroup Λ} {K : Fin d → Subgroup Λ}

omit [Finite Λ] in
theorem le_iSupL (h : TwoFamilies L K) (j : Fin d) : K j ≤ ⨆ i, L i :=
  (le_iSup K j).trans h.LK.ge

omit [Finite Λ] in
theorem le_iSupK (h : TwoFamilies L K) (i : Fin r) : L i ≤ ⨆ j, K j :=
  (le_iSup L i).trans h.LK.le

theorem oUpperTwo_le (h : TwoFamilies L K) {i : Fin r} {j : Fin d} (hm : ⁅K j, L i⁆ ≠ ⊥) :
    S17.oUpperTwo (L i) ≤ K j := by
  have := h.Ln i
  have := h.Kn j
  exact (h.tits i (K j ⊓ L i) (Subgroup.normal_inf_normal _ _) inf_le_right
    (commutator_inf_ne_bot h.hO2 (h.L2 i) hm)).trans inf_le_left

theorem disjoint (h : TwoFamilies L K) {i : Fin r} {j j' : Fin d} (hjj : j ≠ j')
    (hm : ⁅K j, L i⁆ ≠ ⊥) (hm' : ⁅K j', L i⁆ ≠ ⊥) : False := by
  have hO : S17.oUpperTwo (L i) ≤ Subgroup.centralizer (L i : Set Λ) := by
    intro y hy
    have hyj := h.oUpperTwo_le hm hy
    have hyj' := h.oUpperTwo_le hm' hy
    have hc : y ∈ Subgroup.centralizer ((⨆ l, K l : Subgroup Λ) : Set Λ) := by
      refine mem_centralizer_iSup fun l x hx => ?_
      by_cases hl : l = j
      · subst hl
        exact (Subgroup.mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp
          (h.Kc j' l (Ne.symm hjj)) hyj') x hx).symm
      · exact (Subgroup.mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp
          (h.Kc j l (Ne.symm hl)) hyj) x hx).symm
    exact Subgroup.centralizer_le (fun x hx => h.le_iSupK i hx) hc
  have := h.Ln i
  exact h.L0 i (h.hO2 _ inferInstance (isPGroup_of_oUpperTwo_le_centralizer (h.L2 i) hO))

theorem exists_meet (h : TwoFamilies L K) (j : Fin d) : ∃ i, ⁅K j, L i⁆ ≠ ⊥ := by
  by_contra hno
  push Not at hno
  have : ∀ i, (L i).Normal := h.Ln
  have : (⨆ i, L i).Normal := Subgroup.iSup_normal L
  exact h.K0 j (eq_bot_of_le_centralizer h.hO2 (h.K2 j) (h.le_iSupL j) (le_centralizer_iSup hno))

theorem exists_met (h : TwoFamilies L K) (i : Fin r) : ∃ j, ⁅K j, L i⁆ ≠ ⊥ := by
  by_contra hno
  push Not at hno
  have : ∀ j, (K j).Normal := h.Kn
  have : (⨆ j, K j).Normal := Subgroup.iSup_normal K
  refine h.L0 i (eq_bot_of_le_centralizer h.hO2 (h.L2 i) (h.le_iSupK i)
    (le_centralizer_iSup fun j => ?_))
  rw [Subgroup.commutator_comm]
  exact hno j

theorem le_iSup_meet (h : TwoFamilies L K) (j : Fin d) :
    K j ≤ ⨆ (i) (_ : ⁅K j, L i⁆ ≠ ⊥), L i := by
  classical
  have := h.Ln
  have hSn : (⨆ (i) (_ : ⁅K j, L i⁆ ≠ ⊥), L i).Normal :=
    Subgroup.biSup_normal {i | ⁅K j, L i⁆ ≠ ⊥} L fun i _ => h.Ln i
  have hTn : (⨆ (i) (_ : ¬ ⁅K j, L i⁆ ≠ ⊥), L i).Normal :=
    Subgroup.biSup_normal {i | ¬ ⁅K j, L i⁆ ≠ ⊥} L fun i _ => h.Ln i
  refine le_of_le_sup_of_commute h.hO2 (commutator_biSup_eq_bot h.Lc fun i h1 h2 => h2 h1)
    (h.K2 j) ((h.le_iSupL j).trans (iSup_split L _).le) ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact le_centralizer_biSup fun i hi => not_not.mp hi

theorem le_of_meet (h : TwoFamilies L K) {i : Fin r} {j : Fin d} (hm : ⁅K j, L i⁆ ≠ ⊥) :
    L i ≤ K j := by
  classical
  have := h.Kn
  have hTn : (⨆ (j') (_ : ¬ j' = j), K j').Normal :=
    Subgroup.biSup_normal {j' | ¬ j' = j} K fun j' _ => h.Kn j'
  have hsplit : (⨆ j', K j') = K j ⊔ ⨆ (j') (_ : ¬ j' = j), K j' := by
    rw [iSup_split K (· = j), iSup_iSup_eq_left]
  have hST : ⁅K j, ⨆ (j') (_ : ¬ j' = j), K j'⁆ = ⊥ := by
    have h1 := commutator_biSup_eq_bot h.Kc (p := (· = j)) (q := fun j' => ¬ j' = j)
      fun _ h1 h2 => h2 h1
    rwa [iSup_iSup_eq_left] at h1
  refine le_of_le_sup_of_commute h.hO2 hST (h.L2 i) ((h.le_iSupK i).trans hsplit.le) ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine le_centralizer_biSup fun j' hj' => ?_
  by_contra hne
  rw [Subgroup.commutator_comm] at hne
  exact h.disjoint (Ne.symm hj') hm hne

theorem eq_iSup_meet (h : TwoFamilies L K) (j : Fin d) :
    K j = ⨆ (i) (_ : ⁅K j, L i⁆ ≠ ⊥), L i :=
  le_antisymm (h.le_iSup_meet j) (iSup₂_le fun _ hi => h.le_of_meet hi)

theorem eq_of_meet (h : TwoFamilies L K) {i₀ i₁ : Fin r} {j : Fin d}
    (h₀ : ⁅K j, L i₀⁆ ≠ ⊥) (h₁ : ⁅K j, L i₁⁆ ≠ ⊥) : i₀ = i₁ := by
  classical
  by_contra hne
  set B := ⨆ (i) (_ : ⁅K j, L i⁆ ≠ ⊥ ∧ i ≠ i₀), L i with hBdef
  have hAB : L i₀ ⊔ B = K j := by
    rw [h.eq_iSup_meet j]
    refine le_antisymm (sup_le (le_iSup₂_of_le i₀ h₀ le_rfl)
      (iSup₂_le fun i hi => le_iSup₂_of_le i hi.1 le_rfl)) (iSup₂_le fun i hi => ?_)
    by_cases hii : i = i₀
    · subst hii
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le i ⟨hi, hii⟩ le_rfl)
  have hc : ⁅L i₀, B⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact le_centralizer_biSup fun i hi => h.Lc i₀ i (Ne.symm hi.2)
  rcases h.ind j (L i₀) B (h.L2 i₀) (opp_biSup_eq h.L2) hAB hc with hA | hB
  · have hle : L i₁ ≤ L i₀ := hA ▸ h.le_of_meet h₁
    have := h.Ln i₁
    exact commutator_ne_bot_of_opp h.hO2 (h.L2 i₁) (h.L0 i₁) (le_bot_iff.mp
      ((Subgroup.commutator_mono le_rfl hle).trans (h.Lc i₁ i₀ (Ne.symm hne)).le))
  · have hle : L i₀ ≤ B := hB ▸ h.le_of_meet h₀
    have := h.Ln i₀
    exact commutator_ne_bot_of_opp h.hO2 (h.L2 i₀) (h.L0 i₀) (le_bot_iff.mp
      ((Subgroup.commutator_mono le_rfl hle).trans hc.le))

theorem exists_equiv (h : TwoFamilies L K) : ∃ σ : Fin d ≃ Fin r, ∀ j, K j = L (σ j) := by
  classical
  choose σ hσ using h.exists_meet
  have hK : ∀ j, K j = L (σ j) := by
    intro j
    rw [h.eq_iSup_meet j]
    refine le_antisymm (iSup₂_le fun i hi => ?_) (le_iSup₂_of_le (σ j) (hσ j) le_rfl)
    rw [← h.eq_of_meet (hσ j) hi]
  have hinj : Function.Injective σ := by
    intro j j' hjj
    by_contra hne
    exact h.disjoint hne (hσ j) (by rw [hjj]; exact hσ j')
  have hsurj : Function.Surjective σ := by
    intro i
    obtain ⟨j, hj⟩ := h.exists_met i
    exact ⟨j, h.eq_of_meet (hσ j) hj⟩
  exact ⟨Equiv.ofBijective σ ⟨hinj, hsurj⟩, hK⟩

end TwoFamilies

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
