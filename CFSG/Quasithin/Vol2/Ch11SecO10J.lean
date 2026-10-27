module

public import CFSG.Quasithin.Vol2.Ch11SecEBasic
public import CFSG.Quasithin.Vol2.Ch11SecBK6F
public import CFSG.Quasithin.Vol2.Ch11SecBK7H
public import CFSG.Quasithin.Vol2.Ch11SecE41R
public import CFSG.Quasithin.Vol2.Ch11SecBK6B

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 Matrix
open CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_conjV_of_mem_rOf_two (hN : SecA.NatFacts) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) {T L I : Subgroup G} {n : ℕ} (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) {V₁ V₂ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) {r : G} (hr : r ∈ ROf T L V₂) :
    ∃ hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G),
      SecA.conjV (fsuV T I) r hrV ∈ autOn L (fsuV T I) ∧
        ∀ w : ↥(fsuV T I), (w : G) ∈ V₂ → SecA.conjV (fsuV T I) r hrV w = w := by
  have hfl := SecE.flag24_of hN h331 h1102 h hk hV₁ hV₂
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
    rw [hcV] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := hfl.two_le
  have hrV := SecB.K7.r2_le_normalizer hfl hr
  have hw₂ : ∀ w : ↥(fsuV T I), (w : G) ∈ V₂ → w ∈ V₂.subgroupOf (fsuV T I) := fun w hw =>
    Subgroup.mem_subgroupOf.mpr hw
  refine ⟨hrV, ?_⟩
  rcases hk with hk | hk
  · obtain ⟨_, K, _, _, _, hK, π, hπ⟩ := SecB.BK6.exists_real_sl3 hfl hk
    obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
    have hinj : ∀ a b : ↥(fsuV T I), f a = f b → a = b := fun a b hab => by
      have := (hf.eq_iff a b).mp hab
      rwa [hZ, Subgroup.mem_bot, mul_inv_eq_one] at this
    have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal hfl.sylow le_sup_left
        (sup_le Subgroup.le_normalizer hfl.T_le_L)
    obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
      (SecA.isSylowTwoOf_autOn hfl.le_normalizer hTL')
    have hF₂ := SecB.BK6.isFlagW_of_flag24 hfl hfl.le₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂
      hfl.index₂ hfl.T_le_V₂
    have hU₂ := eq_U2_of_isFlagW hsq hf hg (by rw [hK]; exact hF₂)
    obtain ⟨b, c, hbc⟩ := SecB.BK6.exists_rad2_of_mem_r2 hfl hK hf hU₂ hr
    refine ⟨by rw [hbc]; exact (rho3 π _).2, fun w hw => ?_⟩
    have hw' : (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) 2 =
        0 := by
      have := hw₂ w hw
      rw [hU₂] at this
      exact (mem_pre_plane_iff hf g w).mp this
    have hu : ∀ y : Fin 3 → K, y 2 = 0 → uMat 0 b c *ᵥ y = y := fun y hy => by
      rw [uMat_mulVec]
      exact vec3_eq (by simp [hy]) (by simp [hy]) (by simp)
    rw [hbc]
    apply hinj
    rw [hf.act3, gconj_mulVec, coe_uSL, hu _ hw', g_ginv_mulVec]
  · obtain ⟨_, K, _, _, _, hK, π, f, hf, g, -, -, hV₂eq⟩ := SecB.K7.exists_coord_flag24 hfl hk
    have hinj : ∀ a b : ↥(fsuV T I), f a = f b → a = b := fun a b hab => by
      have := (hf.eq_iff a b).mp hab
      rwa [hZ, Subgroup.mem_bot, mul_inv_eq_one] at this
    obtain ⟨x, y, z, hxyz⟩ := SecB.K7.exists_qSp_of_mem_r2 hfl hK hf hV₂eq hr
    refine ⟨by rw [hxyz]; exact (π _).2, fun w hw => ?_⟩
    have hw' : mat 2 K g⁻¹ *ᵥ f w ∈ spPlane K := by
      have := hw₂ w hw
      rw [hV₂eq, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gmapSp] at this
      exact this
    have hq : ∀ v : Fin 2 ⊕ Fin 2 → K, v ∈ spPlane K → mat 2 K (qSp x y z) *ᵥ v = v := by
      intro v hv
      rw [qSp_mulVec]
      refine vec4_eq ?_ ?_ ?_ ?_ <;>
        simp only [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0, vec4_apply_inr1, hv.1,
          hv.2, mul_zero, add_zero]
    rw [hxyz]
    apply hinj
    rw [hf.act4, ← mat_mulVec_inv g (mat 2 K (g * qSp x y z * g⁻¹) *ᵥ f w), conj_mulVec_sp,
      hq _ hw', mat_mulVec_inv]

theorem rOf_two_le (hN : SecA.NatFacts) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    {T L I : Subgroup G} {n : ℕ} (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) {V₁ V₂ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) :
    ROf T L V₂ ≤ TL T L ⊓ Subgroup.centralizer (V₂ : Set G) := by
  intro r hr
  obtain ⟨hrV, hmem, hfix⟩ := exists_conjV_of_mem_rOf_two hN h331 h1102 h hcV hk hV₁ hV₂ hr
  have hRT : r ∈ T := SecD.ROf_le_T h V₂ hr
  obtain ⟨l, hl, hlV, hlr⟩ := SecA.mem_autOn_iff.mp hmem
  have hC : l⁻¹ * r ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    refine SecD.mem_centralizer_of_conjV_eq_one (Subgroup.mul_mem _ (Subgroup.inv_mem _ hlV) hrV)
      ?_
    rw [SecA.conjV_mul _ (Subgroup.inv_mem _ hlV) hrV, SecA.conjV_inv _ hlV, hlr, inv_mul_cancel]
  have hlrLT : l⁻¹ * r ∈ L ⊔ T :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem hl)) (Subgroup.mem_sup_right hRT)
  have hO : l⁻¹ * r ∈ pCoreOf 2 (L ⊔ T) := SecE.inf_centralizer_le_pCoreOf h1102 h ⟨hlrLT, hC⟩
  refine ⟨⟨hRT, ?_⟩, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  · have e : r = l * (l⁻¹ * r) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hO)
  · have h2 := congrArg Subtype.val (hfix ⟨v, SecA.IsVi.le_fsuV hV₂ hv⟩ hv)
    rw [SecA.conjV_apply_coe] at h2
    calc v * r = r * v * r⁻¹ * r := by rw [h2]
      _ = r * v := by group

end CFSG.Quasithin.Vol2.Ch11.O10
