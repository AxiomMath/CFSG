module

public import CFSG.Quasithin.AppendixH.H12.ModelMain
public import CFSG.Quasithin.AppendixH.H12.TransModel
public import CFSG.Quasithin.AppendixH.H12.TransClauses
public import CFSG.Quasithin.AppendixH.H12.TransConj
public import CFSG.Quasithin.AppendixH.H12.Uniqueness
public import CFSG.Quasithin.AppendixH.H12.SmallComm
public import CFSG.Quasithin.AppendixH.H12.Parameters

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH
open CFSG.Quasithin.AppendixH.H12.Model (G0 T0 M0 N0 glHom ι0 f0 ptSub fixV_T0_le formClause_G0
  model_clauses isSylowIn_T0 M0_le_G0)
open CFSG.Quasithin.H.Mathieu.H12Cert (T0_le_G)
open CFSG.CharacterTheory.SteinbergBY

theorem main_49
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    {V : Type} [CommGroup V] {ρ : G →* MulAut V} (hρ : IsFaithIrr12 (ρ.comp L.subtype))
    (τ : Trans G0 L glHom ρ) :
    ∀ T : Subgroup G, IsSylowIn 2 T L → ∃ M N : Subgroup G, Clause4 L T M N ∧
      ∃ V₁ : Subgroup V, Clause5 ρ L T N (τ.iota ι0) (τ.form f0) V₁ ∧
        Clause6 ρ L M (τ.form f0) ∧
        ∃ V₂ : Subgroup V, Clause78 ρ L M (τ.iota ι0) (τ.form f0) V₁ V₂ ∧
          ∀ TG : Subgroup G, IsSylowIn 2 TG ⊤ → T ≤ TG →
            fixV (TG.map ρ) = V₁ ⊓ fixV (TG.map ρ) ∧ (L < ⊤ → rk ↥(fixV (TG.map ρ)) = 1) := by
  intro T hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := Trans.exists_conj_toG_eq (τ := τ) (p := 2) isSylowIn_T0 hT
  have hfc : FormClause glHom G0 ι0 f0 := formClause_G0
  have hι : (τ.conj c).iota ι0 = τ.iota ι0 :=
    Trans.iota_conj τ ι0 c (fun a v => (hfc.2.1 c c.2).1 a v)
  have hf : (τ.conj c).form f0 = τ.form f0 :=
    Trans.form_conj τ f0 c (fun u v => (hfc.2.1 c c.2).2 u v)
  obtain ⟨-, h4, h5, h6, h78⟩ := model_clauses
  refine ⟨(τ.conj c).toG M0, (τ.conj c).toG N0, ?_, (τ.conj c).toV (ptSub 5),
    ?_, ?_, (τ.conj c).toV (ptSub 1465), ?_, ?_⟩
  · rw [← hc]
    exact Trans.clause4_toG (τ.conj c) T0_le_G M0_le_G0
      (show N0 ≤ G0 from inf_le_left) h4
  · rw [← hc]
    simpa only [hι, hf] using
      Trans.clause5_toG (τ.conj c) T0_le_G (show N0 ≤ G0 from inf_le_left) h5
  · simpa only [hf] using Trans.clause6_toG (τ.conj c) M0_le_G0 h6
  · simpa only [hι, hf] using Trans.clause78_toG (τ.conj c) M0_le_G0 h78
  · intro TG hTG hTTG
    have hle : fixV (TG.map ρ) ≤ (τ.conj c).toV (ptSub 5) := by
      intro v hv
      rw [mem_fixV] at hv
      have hv' : v ∈ fixV (((τ.conj c).toG T0).map ρ) := by
        rw [mem_fixV]
        intro x hx
        have hTle : (τ.conj c).toG T0 ≤ TG := by
          rw [hc]; exact hTTG
        exact hv x (Subgroup.map_mono hTle hx)
      rw [Trans.fixV_toG (τ.conj c) T0_le_G] at hv'
      exact (Trans.toV_mono_iff (τ.conj c)).mpr fixV_T0_le hv'
    exact ⟨(inf_eq_right.mpr hle).symm, fun hlt => rk_fixV_sylow hL hF hρ hlt hTG⟩

theorem h12_main :
    H12Stmt := by
  unfold H12Stmt
  intro G _ _ L hL hF
  refine ⟨⟨exists_faithIrr12 hL, fun V₁ V₂ _ _ ρ₁ ρ₂ h₁ h₂ =>
    modIso_of_faithIrr12 hL h₁ h₂⟩, ?_⟩
  intro V _ ρ hρ
  obtain ⟨τ⟩ := exists_trans hL hρ
  have hform : FormClause ρ L (τ.iota ι0) (τ.form f0) := Trans.formClause_toG τ formClause_G0
  unfold FormClause at hform
  obtain ⟨hunit, hact, hq⟩ := hform
  refine ⟨FieldFour, inferInstance, FieldFour.natCard_eq, τ.iota ι0, τ.form f0,
    hunit, hact, hq, ?_, ?_, ?_⟩
  · intro U _ σ hU2 hinj hirr ht
    exact modIso_of_faithIrr12 hL (faithIrr12_of_small_comm hL hF σ hU2 hinj hirr ht) hρ
  · intro T hT
    obtain ⟨M, N, h4, V₁, h5, h6, V₂, h78, h9⟩ := main_49 hL hF hρ τ T hT
    unfold Clause4 at h4
    unfold Clause5 at h5
    unfold Clause6 at h6
    unfold Clause78 at h78
    obtain ⟨a, b, c, d⟩ := h5
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := h78
    exact ⟨M, N, h4, V₁, a, b, c, d, h6, V₂,
      i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, h9⟩
  · exact params_clause hL hF hρ

end CFSG.Quasithin.AppendixH.H12
