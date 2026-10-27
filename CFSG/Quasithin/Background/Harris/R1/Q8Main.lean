module

public import CFSG.Quasithin.Background.Harris.R1.Q8Cent
public import CFSG.Quasithin.Background.Harris.R1.Q8VbK1
public import CFSG.Quasithin.Recognition.SzR1CenterHolds

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def PermSevenStmt : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (pt : Ω), Fintype.card Ω = 9 → PermSevenAt Ω pt

@[expose] def F112R1bQbetaLocStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
    IsL2Quot 3 (OTwoQuot K1) → ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
    pCoreOf 2 K1 = vBeta K1 L2 S Zs

@[expose] def F112R1bN2LocStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
    IsL2Quot 3 (OTwoQuot K1) → ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
    pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1

theorem r1b_B2 (hP7 : PermSevenStmt)
    (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G) (hset : R1SettingLegacyBare K1 L2 S Zs)
    (hZS : ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs)
    (hL : IsL2Quot 3 (OTwoQuot K1)) (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    pCoreOf 2 K1 = vBeta K1 L2 S Zs ∧ pCoreOf 2 (K1 ⊔ S) = pCoreOf 2 K1 := by
  classical
  obtain ⟨Ω, hΩ, C, hodd, hcard, -⟩ :=
    famStmt_holds G K1 L2 S Zs hset 3 (by norm_num) (Or.inl hL) hna
  have hc9 : Fintype.card Ω = 9 := (hcard hL).trans (by norm_num)
  have hcen := centerBender_holds G K1 L2 S Zs hset ⟨3, by norm_num, Or.inl hL⟩ hna
  have hZS' : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs :=
    fun u hu hc h2 => hZS u hu h2 hc
  have hs : IsSimpleGroup (OTwoQuot K1) := by
    obtain ⟨e⟩ := hL
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [GaloisField.card 2 3 (by norm_num)]; norm_num)
    exact e.isSimpleGroup
  have hΩ4 : 4 ≤ Fintype.card Ω := by omega
  obtain ⟨i₀, j₀, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Ω)
  have hker := hker_of_simple C hodd (by omega) hs
  obtain ⟨t, htK, htB, ht7⟩ := exists_order_seven C hc9 hL
  have hD := D_le_Z_odd C hΩ4 hodd hij hcen hZS' hker hs htK htB ht7 (hP7 Ω C.D.pt hc9)
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  have hWK : vBeta K1 L2 S Zs ≤ K1 := vBeta_le_K1_gen C hodd hij hcen
  have hQ : pCoreOf 2 K1 = vBeta K1 L2 S Zs :=
    pCoreK1_eq_vBeta C hodd hij Finset.univ.toList (Finset.nodup_toList _) (by simp) hcen hWK
      (fun x hx hxC => hD ⟨⟨pCoreK1_le_kerM C hodd hx, hkS (pCoreK1_le_kerM C hodd hx)⟩, hxC⟩)
  refine ⟨hQ, le_antisymm (fun y hy => ?_) (fun y hy => ?_)⟩
  · have hyM : y ∈ C.kerM := pCore_le_kerM C hΩ4 hodd hy
    obtain ⟨w, hw, hwc⟩ := exists_inner_of_kerM C hodd hij Finset.univ.toList
      (Finset.nodup_toList _) (by simp) hcen hyM
    have hdM : w⁻¹ * y ∈ C.kerM :=
      C.kerM.mul_mem (C.kerM.inv_mem (C.vBeta_le_kerM hw)) hyM
    have hdZ : w⁻¹ * y ∈ Zs := hD ⟨⟨hdM, hkS hdM⟩, hwc⟩
    have e : y = w * (w⁻¹ * y) := by group
    rw [hQ, e]
    exact (vBeta K1 L2 S Zs).mul_mem hw (F112J2.Zs_le_vBeta K1 L2 S Zs hdZ)
  · rw [hQ] at hy
    exact F112W.conjClosure_le_pCoreOf_G₂ C.h.V_le hy

theorem qbetaLoc8_of_p7 (hP7 : PermSevenStmt) :
    F112R1bQbetaLocStatement :=
  fun G _ _ K1 L2 S Zs hset hZS hL hna => (r1b_B2 hP7 G K1 L2 S Zs hset hZS hL hna).1

theorem n2Loc8_of_p7 (hP7 : PermSevenStmt) :
    F112R1bN2LocStatement :=
  fun G _ _ K1 L2 S Zs hset hZS hL hna => (r1b_B2 hP7 G K1 L2 S Zs hset hZS hL hna).2

end CFSG.Quasithin.Background.Harris.R1
