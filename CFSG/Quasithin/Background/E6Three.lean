module

public import CFSG.Quasithin.Background.E6Thirteen
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open

section Three

variable {G : Type} [Group G] [Finite G] {T M V U : Subgroup G}

theorem inf_centralizer_le_normalizer (h : HypE61 T M V) (hUV : U ≤ V) (hU1 : U ≠ ⊥) :
    M ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  by_contra hgN
  have hTI := h.tiSet.2 g hg.1 hgN
  apply hU1
  rw [eq_bot_iff, ← hTI]
  intro u hu
  refine ⟨hUV hu, ?_⟩
  show u ∈ conjSubgroup V g
  rw [mem_conjSubgroup_iff]
  have hc : g * u = u * g := (Subgroup.mem_centralizer_iff.1 hg.2 u hu).symm
  have e : g * u * g⁻¹ = u := by rw [hc]; group
  rw [e]
  exact hUV hu

theorem mem_gammaE64_of_mQuot_lt (hV : IsElemAbelian 2 V) (h : HypE61 T M V) (hUV : U ≤ V)
    (hU1 : U ≠ ⊥) (hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M)
    (hlt : E3.mQuot V U < E3.mParam (autI hV M)) : U ∈ gammaE64 V M := by
  refine ⟨hUV, hU1, hCM, ?_⟩
  set H := M ⊓ Subgroup.centralizer (U : Set G) with hHdef
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := inf_centralizer_le_normalizer h hUV hU1
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two H
  have hSC : S ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hSC
    have hSN : S ≤ Subgroup.normalizer (V : Set G) := hS.1.trans hHN
    have hA1 : autI hV S ≠ ⊥ := (autI_eq_bot_iff hV hSN).not.2 hSC
    have hle := E3.mParam_le_rkIdx_fixV (autI_mono hV (hS.1.trans inf_le_left))
      (B6.isPGroup_autOn hS.2.1 V) hA1
    rw [E3.rkIdx_fixV_autI hV hSN] at hle
    have hUS : U ≤ V ⊓ Subgroup.centralizer (S : Set G) := by
      intro u hu
      refine ⟨hUV hu, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp (hS.1 hs).2 u hu).symm
    have := E3.mQuot_mono (V := V) hUS
    omega
  refine (iInf₂_le (H ⊓ Subgroup.centralizer (V : Set G))
    ⟨inf_le_left, B2F.le_normalizer_inf Subgroup.le_normalizer
      (B2F.le_normalizer_centralizer hHN), fun h2 => ?_⟩).trans (inf_le_inf_right _ inf_le_left)
  exact hS.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left H (le_inf hS.1 hSC)))

omit [Finite G] in
theorem exists_eq_rParam' (h : E3.rParam V ≠ ⊤) :
    ∃ U : Subgroup G, U ≤ V ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      (E3.mQuot V U : ℕ∞) = E3.rParam V := by
  set S := {U : Subgroup G | U ≤ V ∧
    ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)} with hSdef
  have hr : E3.rParam V = ⨅ U : S, (E3.mQuot V U : ℕ∞) := by
    rw [E3.rParam, iInf_subtype']
  have hne : Nonempty S := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    apply h
    rw [hr]
    exact iInf_of_empty _
  obtain ⟨⟨U, hUS⟩, hU⟩ := ENat.exists_eq_iInf (fun U : S => (E3.mQuot V U : ℕ∞))
  exact ⟨U, hUS.1, hUS.2, hU.trans hr.symm⟩

theorem autI_top_eq (hV : IsElemAbelian 2 V) (h : HypE61 T M V) :
    autI hV (⊤ : Subgroup G) = autI hV M := by
  refine le_antisymm (fun φ hφ => ?_) (autI_mono hV le_top)
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hφ
  exact convI_mem_autI hV (h.normalizer_le g.2) g.2

end Three

@[expose] def E623Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → 1 < E3.rParam V

@[expose] def E625Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) →
    U ∈ gammaE64 V M → (E3.mQuot V U : ℕ∞) = E3.rParam V → 1 < E3.mQuot V U →
    E3.mQuot V U < E3.mParam (autI hV M) →
    (Nat.card (autI hV M) = 21 ∧ ∃ a ∈ autI hV M, ∃ b ∈ autI hV M, a * b ≠ b * a) ∧
      (Nat.card V = 8 ∧ Nat.card U = 2) ∧ T ⊓ Subgroup.centralizer (V : Set G) = T

theorem as_E_6_3_of (h311 : Theorem311Stmt) (h623 : E623Stmt) (h625 : E625Stmt) :
    ASInputs.AS_E_6_3 := by
  intro G _ _ T M V hV h hm
  have hle : (E3.mParam (autI hV M) : ℕ∞) ≤ E3.rParam V := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨U, hUV, hCN, hUr⟩ := exists_eq_rParam' (ne_top_of_lt hlt)
    have hUlt : E3.mQuot V U < E3.mParam (autI hV M) := by
      have h1 : (E3.mQuot V U : ℕ∞) < (E3.mParam (autI hV M) : ℕ∞) := hUr ▸ hlt
      exact_mod_cast h1
    have hU1 : U ≠ ⊥ := by
      rintro rfl
      have h1 : E3.mQuot V ⊥ = rk (IntMod V hV) := by
        unfold E3.mQuot rk
        rw [Subgroup.relIndex_bot_left]
        rfl
      have h2 := E3.mParam_le_rk (autI hV M)
      omega
    have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun hCM =>
      hCN fun g hg => inf_centralizer_le_normalizer h hUV hU1 ⟨hCM hg, hg⟩
    have hUΓ : U ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hUV hU1 hCM hUlt
    have hr1 : 1 < E3.mQuot V U := by
      have h1 := h623 G T M V hV h hm
      rw [← hUr] at h1
      exact_mod_cast h1
    obtain ⟨-, -, hTQ⟩ := h625 G T M V U hV h hm hUΓ hUr hr1 hUlt
    have hTU : T ≤ Subgroup.normalizer (U : Set G) := fun t ht =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUV (inf_eq_left.1 hTQ ht))
    exact hCM (e6_13 h311 h hUV hU1 hUΓ.2.2.2 hTU)
  refine ⟨hle, ?_⟩
  unfold E3.sParam
  rw [autI_top_eq hV h, min_eq_right hle]
  rfl

end E6

end CFSG.Quasithin
