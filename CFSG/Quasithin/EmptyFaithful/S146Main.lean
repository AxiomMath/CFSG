module

public import CFSG.Quasithin.EmptyFaithful.S146Six2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def FinalData146Core (T M : Subgroup G) : Prop :=
  ∃ (H : Subgroup G) (u : G) (H₂ : Subgroup G),
    IsHTM T M H ∧ IsInvU T M H u ∧ IsI T M u (Subgroup.centralizer ({u} : Set G)) ∧
    4 < (pCoreOf 2 H).relIndex T ∧
    4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
    tZero T u ≤ H₂ ∧
    H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
    Nonempty (OTwoQuot H₂ ≃* Equiv.Perm (Fin 3)) ∧ ¬ H₂ ≤ M ∧
    Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4

@[expose] def Stage146BranchACore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    (∃ H : Subgroup G, IsHTM T M H ∧ ¬ OddCoreModTwoTrivial H) → FinalData146Core T M

@[expose] def Stage146BranchBCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    (∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H) → FinalData146Core T M

theorem stepBCore (hedge : GoldschmidtEdgeBoundSubgroups.{0}) (h9 : Stage1469)
    (h105 : Stage14610Five) (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) {T M : Subgroup G} (S : Setting146 G T M)
    (hD : FinalData146Core T M) : False := by
  obtain ⟨H, u, H₂, hH, hu, hCu, h4', hm, hT0, hH₂C, hS3, hH₂M, hrk⟩ := hD
  obtain ⟨I, hI, hIc⟩ := exists_isIStar_choice hCu
  have hTH : T ≤ H := hH.1.1
  have hlIL : lI T M I ≤ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left
  have hlII : lI T M I ≤ I := (oTwoUpper_le _).trans inf_le_right
  have ha := h1 G T M S H hH u hu
  have hb := h2 G T M S H hH u hu
  have hc := h3 G T M S H hH u hu
  have hd := h4 G T M S H hH u hu
  obtain ⟨h211, hLT⟩ := h9 G T M H u S hH hu I hI h4' hm
  have hL_eq : yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) := by
    refine le_antisymm ?_ (sup_le hlIL (LieType.BorelTits.pCoreOf_le 2 _))
    refine le_sup_pCoreOf_of_S3 (X := yOfL22 T M ⊔ T) le_sup_left ?_ S.hyp1281.residual
      (oTwoUpper_oTwoUpper _) hlIL S.facts.sThree (S.hyp.sylow.1.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) hLT
    exact sup_le Subgroup.le_normalizer (S.hyp.m_max.1.2.trans S.hyp1281.normal)
  have h29 : 2 ^ 9 < Nat.card T :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h211
  obtain ⟨hI₀, hGT⟩ := six_main hedge S hH hu ha hb hc hd hI h29 hL_eq hT0 hH₂C hS3 hH₂M
  have hTI_le : T ⊓ I ≤ (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) :=
    le_sup_right.trans le_sup_left
  obtain ⟨-, hTI₀⟩ := hI.of_le_inf hI₀.1 hTI_le
  have hTIH₂ : T ⊓ I ≤ H₂ := by
    refine le_trans ?_ hT0
    rcases (isIStar_sylow_cases S hu ha.2.1 hb hd.1 hI).2 with h | h
    · rw [h]; exact tU_le_tZero T u
    · exact h.le
  have hOc : oTwoUpper H₂ ≤ Subgroup.centralizer ({u} : Set G) :=
    S.oTwoUpper_le_centralizer hH hH₂C
  have hH₂H : H₂ ≤ H := hH₂C.trans (centralizerMod_le_left _ _ _)
  have hI₂H : oTwoUpper H₂ ⊔ (T ⊓ I) ≤ H :=
    sup_le ((oTwoUpper_le H₂).trans hH₂H) (inf_le_left.trans hTH)
  have hI₀eq := eq_sup_lI_sup (T := T) (M := M) (A := lI T M I) (B := T ⊓ I)
    (C := oTwoUpper H₂) (oTwoUpper_oTwoUpper _) hlIL rfl hTI₀
  have hcent : T ⊓ ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I))) = tU T u →
      (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro h
    have hIT : T ⊓ I = tU T u := by rw [← hTI₀]; exact h
    have hIc' := hIc hIT
    exact sup_le (sup_le (hlII.trans hIc') (inf_le_right.trans hIc'))
      (sup_le hOc (inf_le_right.trans hIc'))
  have hrank := h105 G T M H u S hH hu _ hI₀ h4' hm (oTwoUpper H₂ ⊔ (T ⊓ I))
    (by rw [hTI₀]; exact le_sup_right) hI₂H hGT.2.2.1 hI₀eq hcent
  have hconj : conjClosure (VZ T M) (oTwoUpper H₂ ⊔ (T ⊓ I)) =
      conjClosure (VZ T M) (oTwoUpper H₂) :=
    conjClosure_sup_eq_of_normalizes (hTIH₂.trans (le_normalizer_oTwoUpper H₂))
      (inf_le_left.trans S.T_le_normalizer_V)
  rw [hconj, hrk] at hrank
  norm_num at hrank

theorem stageSection146_of_inputs (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hedge : GoldschmidtEdgeBoundSubgroups.{0}) (hA : Stage146BranchACore)
    (hB : Stage146BranchBCore) (h9 : Stage1469) (h105 : Stage14610Five) (h631 : Stage1463One)
    (h632 : Stage1463Two) (h633 : Stage1463Three) (h634 : Stage1463Four) : StageSection146 := by
  intro G _ _ T M hyp hnot hab
  have S : Setting146 G T M := ⟨hyp, hyp.facts1422 h11 h113, hnot, hab⟩
  by_cases h : ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H
  · exact stepBCore hedge h9 h105 h631 h632 h633 h634 S (hB G T M S h)
  · push Not at h
    exact stepBCore hedge h9 h105 h631 h632 h633 h634 S (hA G T M S h)

end CFSG.Quasithin
