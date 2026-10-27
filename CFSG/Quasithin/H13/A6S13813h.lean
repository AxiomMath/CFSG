module

public import CFSG.Quasithin.H13.A6S13813g

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_key (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h139 : Stmt13_3_9) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hsol : Group.IsSolvable ↥H)
    (hmin : ∀ K ∈ S.Hz, K ≤ H → K = H) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H)
    (hle : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    {h : G} (hhH : h ∈ H) (hβ : conjSub h (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T))
    {u₀ : G} (hu₀U : u₀ ∈ F8.Uγ S.V3 H (g : G)) (hu₀Q : u₀ ∉ pCoreOf 2 H)
    (key : ∀ v ∈ F8.Uγ V H (g : G), v ∈ pCoreOf 2 H ∨ u₀⁻¹ * v ∈ pCoreOf 2 H) : False := by
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  set φ := actH hV₁ hIH with hφ
  set Q := pCoreOf 2 H with hQ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ Q := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hQ, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hQconj : ∀ x ∈ H, ∀ q, x * q * x⁻¹ ∈ Q ↔ q ∈ Q := by
    intro x hx q
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) q)
    exact this.symm
  have hVγH : F8.Uγ V H (g : G) ≤ H := hF.Vγ_le_H s
  have hUV : F8.Uγ S.V3 H (g : G) ≤ F8.Uγ V H (g : G) := hF.Uγ_le_Vγ
  have hVab := hF.isElemAbelian_Vγ (g := g)
  have hVcomm : ∀ a ∈ F8.Uγ V H (g : G), ∀ b ∈ F8.Uγ V H (g : G), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hVab.1.is_comm.comm (⟨a, ha⟩ : ↥(F8.Uγ V H (g : G)))
      ⟨b, hb⟩)
  have hDγQ := hF.Dγ_eq_inf_pCoreOf s
  have hu₀V := hUV hu₀U
  have huH : h * u₀ * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH (hVγH hu₀V)) (H.inv_mem hhH)
  have huR : h * u₀ * h⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) := hβ (mul_mem_conjSub hu₀V)
  have huQ : h * u₀ * h⁻¹ ∉ Q := fun h1 => hu₀Q ((hQconj h hhH u₀).1 h1)
  have hVUQ : F8.Uγ V H (g : G) ≤ F8.Uγ S.V3 H (g : G) ⊔ Q := by
    intro v hv
    rcases key v hv with h1 | h1
    · exact Subgroup.mem_sup_right h1
    · rw [show v = u₀ * (u₀⁻¹ * v) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₀U) (Subgroup.mem_sup_right h1)
  have h1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by
    have hU2 : IsPGroup 2 ↥(F8.Uγ S.V3 H (g : G)) :=
      isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
    have hidx := HypF98.relIndex_eq_two_pow_mIdx
      (Y := F8.Dγ S.V3 (fsuV1 T V) H (g : G)) hU2
    have hdvd : ((F8.Dγ S.V3 (fsuV1 T V) H (g : G)).subgroupOf
        (F8.Uγ S.V3 H (g : G))).index ∣ 2 := by
      rw [Subgroup.index_dvd_two_iff]
      refine ⟨(⟨u₀, hu₀U⟩ : ↥(F8.Uγ S.V3 H (g : G)))⁻¹, fun b => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hDγQ]
      rcases key b (hUV b.2) with h2 | h2
      · exact Or.inr ⟨b.2, h2⟩
      · left
        refine ⟨(b * (⟨u₀, hu₀U⟩ : ↥(F8.Uγ S.V3 H (g : G)))⁻¹).2, ?_⟩
        have hc : (b : G) * u₀⁻¹ = u₀⁻¹ * b :=
          (hVcomm _ (hUV b.2) _ (hUV ((F8.Uγ S.V3 H (g : G)).inv_mem hu₀U))).trans rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hc]
        exact h2
    have h2 : 2 ^ mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∣ 2 ^ 1 := by
      rw [← hidx, pow_one]
      exact hdvd
    have h3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 h2
    have h4 : 0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) := by
      by_contra h0
      push Not at h0
      have h5 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 0 := by omega
      rw [h5, pow_zero, Subgroup.relIndex_eq_one] at hidx
      exact hDγ.ne (le_antisymm hDγ.le hidx)
    omega
  have hV1 := S.V1_le_Uγ_of_solvable hS hH hsol s hDγ hDH hle h1
  have hA2 : IsPGroup 2 ↥(((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ) := fun x => by
    obtain ⟨k, hk⟩ := S.pow_two_pow_eq_one_of_mem_R1 x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hA1 : ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ ≠ ⊥ := by
    intro hbot
    have hmem : φ ⟨_, huH⟩ ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map φ :=
      ⟨⟨_, huH⟩, Subgroup.mem_subgroupOf.2 huR, rfl⟩
    rw [hbot, Subgroup.mem_bot, hker] at hmem
    exact huQ hmem
  obtain ⟨p, P, hP⟩ := S.exists_P h139 hS hH hsol hmin hV₁ hIH le_rfl hA2 hA1
  have hgen := S.stab_gen hS hH (fun K hKH hKQ hc => S.gen_of_P hS hH hP hKH hKQ hc) s hDγ hDH
  exact S.lemma13_8_11_one hS.hNS h13315 h1356two hH hF h13314 s hgen (Or.inl hV1) hVUQ

end Setting4

end CFSG.Quasithin.H13.A6
