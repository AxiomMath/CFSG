module

public import CFSG.Quasithin.Recognition.F112J2Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F112W
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace SzR1

namespace MNU

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

omit [Finite G] in
theorem mem_omegaOneCenterOf_iff {X : Subgroup G} {x : G} :
    x ∈ omegaOneCenterOf X ↔ x ∈ X ∧ (∀ y ∈ X, x * y = y * x) ∧ x * x = 1 := by
  constructor
  · intro hx
    unfold omegaOneCenterOf omegaOneOf at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxc, hx2⟩ := hx
      refine ⟨(Subgroup.mem_inf.mp hxc).1, fun y hy => ?_, by rw [← pow_two]; exact hx2⟩
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxc).2) y hy).symm
    | one => exact ⟨X.one_mem, fun y _ => by simp, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hxX, hxc, hx2⟩ := hx
      obtain ⟨hyX, hyc, hy2⟩ := hy
      refine ⟨X.mul_mem hxX hyX, fun z hz => ?_, ?_⟩
      · calc x * y * z = x * (y * z) := mul_assoc _ _ _
          _ = x * (z * y) := by rw [hyc z hz]
          _ = (x * z) * y := (mul_assoc _ _ _).symm
          _ = (z * x) * y := by rw [hxc z hz]
          _ = z * (x * y) := mul_assoc _ _ _
      · calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
          _ = x * (x * y) * y := by rw [← hxc y hyX]
          _ = (x * x) * (y * y) := by simp only [mul_assoc]
          _ = 1 := by rw [hx2, hy2, one_mul]
    | inv x _ hx =>
      obtain ⟨hxX, hxc, hx2⟩ := hx
      refine ⟨X.inv_mem hxX, fun z hz => ?_, ?_⟩
      · exact ((Commute.inv_left (hxc z hz : Commute x z))).eq
      · rw [← mul_inv_rev, hx2, inv_one]
  · rintro ⟨hxX, hxc, hx2⟩
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hxX, Subgroup.mem_centralizer_iff.mpr
      fun y hy => (hxc y hy).symm⟩, ?_⟩
    rw [pow_two]
    exact hx2

theorem amalgamHypV_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    AmalgamHypV (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) S (conjClosure Zs L2) := by
  have := F112J2.amalgamHypV_thesis hR (F112J2.zs_le_omegaOneCenter h) h.s3 h.Z_not_norm
  rwa [F112J2.conjClosure_sup_S h.hyp.h2.normalizes (F112J2.S_le_centralizer_Z h)] at this

theorem isNaturalS3_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    IsNaturalS3 (L2 ⊔ S) (conjClosure Zs L2) := by
  have hc := F112J2.conjClosure_sup_S h.hyp.h2.normalizes (F112J2.S_le_centralizer_Z h)
  have := F112J2.isNaturalS3_thesis hR (F112J2.zs_le_omegaOneCenter h) h.s3 h.Z_not_norm
    (by rw [hc]; exact h.V_card)
  rwa [hc] at this

theorem pCore_eq_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    pCoreOf 2 (L2 ⊔ S) = S ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) :=
  pCoreOf_eq_inf_centralizer (amalgamHypV_of_setting h hR)

theorem pCore_le_S_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    pCoreOf 2 (L2 ⊔ S) ≤ S :=
  isSylowTwoOf_pCoreOf_le (amalgamHypV_of_setting h hR).sylow₁

theorem V_le_pCore_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    conjClosure Zs L2 ≤ pCoreOf 2 (L2 ⊔ S) :=
  V_le_pCoreOf (amalgamHypV_of_setting h hR)

theorem V_le_S_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    conjClosure Zs L2 ≤ S :=
  h.V_le.trans (isSylowTwoOf_pCoreOf_le (amalgamHypV_of_setting h hR).sylow₂)

theorem relIndex_S_P_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    S.relIndex (L2 ⊔ S) = 3 :=
  F112J2.relIndex_L2S hR h.s3

theorem relIndex_pCore_S_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    (pCoreOf 2 (L2 ⊔ S)).relIndex S = 2 :=
  relIndex_pCoreOf_T (amalgamHypV_of_setting h hR) (isNaturalS3_of_setting h hR)

theorem V_elemAbelian_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    IsElemAbelian 2 (conjClosure Zs L2) :=
  (amalgamHypV_of_setting h hR).elemAbelian

theorem centralizer_V_le_pCore (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    (L2 ⊔ S) ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) ≤ pCoreOf 2 (L2 ⊔ S) := by
  set Q := pCoreOf 2 (L2 ⊔ S) with hQ
  have hQS : Q ≤ S := pCore_le_S_of_setting h hR
  have hSP : S ≤ L2 ⊔ S := le_sup_right
  have hQV : Q ≤ Subgroup.centralizer (conjClosure Zs L2 : Set G) := by
    rw [hQ, pCore_eq_of_setting h hR]
    exact inf_le_right
  have hQC : Q ≤ (L2 ⊔ S) ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) :=
    le_inf (hQS.trans hSP) hQV
  have h1 := Subgroup.relIndex_mul_relIndex Q ((L2 ⊔ S) ⊓ Subgroup.centralizer
    (conjClosure Zs L2 : Set G)) (L2 ⊔ S) hQC inf_le_left
  have h2 : Q.relIndex (L2 ⊔ S) = 6 := by
    rw [← Subgroup.relIndex_mul_relIndex Q S (L2 ⊔ S) hQS hSP, relIndex_pCore_S_of_setting h hR,
      relIndex_S_P_of_setting h hR]
  rw [(isNaturalS3_of_setting h hR).index_eq, h2] at h1
  have h3 : Q.relIndex ((L2 ⊔ S) ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G)) = 1 := by
    omega
  exact Subgroup.relIndex_eq_one.mp h3

theorem mem_pCore_of_central (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) {u : G}
    (huS : u ∈ S) (hc : ∀ s ∈ S, u * s = s * u) : u ∈ pCoreOf 2 (L2 ⊔ S) := by
  rw [pCore_eq_of_setting h hR]
  refine Subgroup.mem_inf.mpr ⟨huS, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact (hc v (V_le_S_of_setting h hR hv)).symm

theorem V_le_omegaOneCenter_pCore (h : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S) :
    conjClosure Zs L2 ≤ omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)) := by
  intro v hv
  rw [mem_omegaOneCenterOf_iff]
  refine ⟨V_le_pCore_of_setting h hR hv, fun q hq => ?_, ?_⟩
  · have hq' : q ∈ S ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) := by
      rw [← pCore_eq_of_setting h hR]
      exact hq
    exact Subgroup.mem_centralizer_iff.mp hq'.2 v hv
  · rw [← pow_two]
    exact (V_elemAbelian_of_setting h hR).2 v hv

end MNU

end SzR1

namespace S1421

variable {G : Type} [Group G] {T K1 : Subgroup G}

theorem hZS_of_eq (h : sOf T K1 = T) :
    ∀ u ∈ sOf T K1, u * u = 1 → (∀ s ∈ sOf T K1, u * s = s * u) →
      u ∈ quasithinOmegaOneCenter T := by
  intro u huS hu2 huc
  rw [h] at huS huc
  refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨huS, Subgroup.mem_centralizer_iff.mpr
    fun s hs => (huc s hs).symm⟩, ?_⟩
  rw [pow_two]
  exact hu2

end S1421

end CFSG.Quasithin
