module

public import CFSG.Quasithin.EmptyFaithful.S153E56E9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace S153E

open CFSG.Quasithin.S153E56e

section Geo

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15355 cx N₁ N₂ g s) {y : G}
  (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁))
  (iJ : JStruct56 T Mc M V₁ N₁ y)
  (hrank : mIdx (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) = 2 * (s + 2))

include h113 cx c hy iJ hrank

omit h113 hy iJ hrank in
theorem geo56_Z_center : centerOf (UH153 T M V₁ Mc) = quasithinOmegaOneCenter T :=
  centerOf_U cx c.h55.1

theorem geo56_Z'_le_U :
    conjSubgroup (quasithinOmegaOneCenter T) y ≤ UH153 T M V₁ Mc :=
  Z'_le_U ⟨h113, c, hy, iJ, hrank⟩

theorem geo56_Z_le_U' :
    quasithinOmegaOneCenter T ≤ conjSubgroup (UH153 T M V₁ Mc) y :=
  Z_le_U' ⟨h113, c, hy, iJ, hrank⟩

theorem geo56_Z_inf_Z' :
    quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y = ⊥ :=
  Z_inf_Z' ⟨h113, c, hy, iJ, hrank⟩

theorem geo56_E_eq :
    Egp153 T M V₁ Mc y = UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) y :=
  E_eq ⟨h113, c, hy, iJ, hrank⟩

theorem geo56_E_sing :
    quasithinOmegaOneCenter T ≤ Egp153 T M V₁ Mc y ∧
      (∀ e ∈ Egp153 T M V₁ Mc y, e ^ 2 = 1) ∧
      mIdx (Egp153 T M V₁ Mc y) (quasithinOmegaOneCenter T) = s + 2 := by
  have H : Hyps56 cx N₁ N₂ g s y := ⟨h113, c, hy, iJ, hrank⟩
  obtain ⟨β, φ, hN, hcardE⟩ := count_main H
  refine ⟨Z_le_E H, fun e he => by rw [pow_two]; exact E_sq H he, ?_⟩
  refine mIdx_eq_of_card (Z_le_E H) (k := s + 2) ?_
  rw [hcardE, S153E57.Z_card cx]
  ring

theorem geo56_V0_le_E :
    quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤
      Egp153 T M V₁ Mc y :=
  V0_le_E ⟨h113, c, hy, iJ, hrank⟩

omit h113 c hy iJ hrank in
theorem geo56_F_eq :
    Fgp153 T M V₁ Mc y = UH153 T M V₁ Mc ⊓
      Subgroup.centralizer ((conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) :=
  F_eq cx y

theorem geo56_X_eq :
    Xgp153 T M V₁ Mc y = conjSubgroup (UH153 T M V₁ Mc) y ⊓
      Subgroup.centralizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G) :=
  X_eq ⟨h113, c, hy, iJ, hrank⟩

theorem geo56_X_le_Mc : Xgp153 T M V₁ Mc y ≤ Mc :=
  X_le_Mc ⟨h113, c, hy, iJ, hrank⟩

theorem geo56_X_inf_Q : Xgp153 T M V₁ Mc y ⊓ pCoreOf 2 Mc = Egp153 T M V₁ Mc y :=
  X_inf_Q_aux ⟨h113, c, hy, iJ, hrank⟩

theorem geo56_V_norm_E :
    VZ T M ≤ Subgroup.normalizer ((Egp153 T M V₁ Mc y : Subgroup G) : Set G) :=
  fun _ hv => iJ.normal_E (V_le_normalizer_V0 ⟨h113, c, hy, iJ, hrank⟩ hv)

theorem geo56_V_comm_E :
    ⁅Egp153 T M V₁ Mc y, VZ T M⁆ ≤
      quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y :=
  V_comm_E ⟨h113, c, hy, iJ, hrank⟩

omit [Finite G] h113 cx c hy hrank in
theorem geo56_EN :
    Subgroup.normalizer
        ((quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) :
          Set G) ≤
      Subgroup.normalizer ((Egp153 T M V₁ Mc y : Subgroup G) : Set G) := iJ.normal_E

theorem concl56_comm_XF :
    ⁅Xgp153 T M V₁ Mc y, Fgp153 T M V₁ Mc y⁆ ≤ Egp153 T M V₁ Mc y := by
  have H : Hyps56 cx N₁ N₂ g s y := ⟨h113, c, hy, iJ, hrank⟩
  obtain ⟨β, φ, hN, -⟩ := count_main H
  rw [Subgroup.commutator_le]
  intro x hx f hf
  rw [commutatorElement_def]
  exact hN.comm_mem (X_le_R H hx) (F_le_R H hf)

theorem concl56_X_norm_E :
    Xgp153 T M V₁ Mc y ≤ Subgroup.normalizer (Egp153 T M V₁ Mc y : Set G) := by
  have H : Hyps56 cx N₁ N₂ g s y := ⟨h113, c, hy, iJ, hrank⟩
  intro x hx
  have hxR := X_le_R H hx
  rw [iJ.R_cent] at hxR
  exact iJ.normal_E (Subgroup.centralizer_le_normalizer _ hxR.2)

theorem concl56_X_rank :
    IsElemAbelianOfRank 2 (s + 1) ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y)) :=
  X_rank_aux ⟨h113, c, hy, iJ, hrank⟩

end Geo

end S153E

end CFSG.Quasithin
