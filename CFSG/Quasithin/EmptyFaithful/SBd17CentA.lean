module

public import CFSG.Quasithin.EmptyFaithful.SBd16A6

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.pCoreOf_le_V₁ (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    {Hv : Subgroup G} (hLH : L ≤ Hv) (hOS : pCoreOf 2 Hv ≤ Sgp153 T V₁) :
    pCoreOf 2 Hv ≤ V₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxS : x ∈ Sgp153 T V₁ := hOS hx
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := r.S_le_L hxS
  have hperf : Group.IsPerfect ↥L := r.ctx.c33.quasisimple.1
  let ψ : MulAut ↥L := conjAct L ⟨x, hxN⟩
  have hψ : ∀ y : ↥L, ((ψ y : ↥L) : G) = x * (y : G) * x⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion le_rfl ⟨x, hxN⟩) y
  have hcen : ∀ y : ↥L, ψ y * y⁻¹ ∈ Subgroup.center ↥L := by
    intro y
    have hyHv : (y : G) ∈ Hv := hLH y.2
    have hz : ((ψ y * y⁻¹ : ↥L) : G) ∈ pCoreOf 2 Hv := by
      have h1 : (y : G) * x⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 Hv := by
        have hn := le_normalizer_pCoreOf 2 Hv hyHv
        have := (Subgroup.mem_normalizer_iff.mp hn x⁻¹).mp (Subgroup.inv_mem _ hx)
        exact this
      have : ((ψ y * y⁻¹ : ↥L) : G) = x * ((y : G) * x⁻¹ * (y : G)⁻¹) := by
        rw [Subgroup.coe_mul, hψ, Subgroup.coe_inv]
        group
      rw [this]
      exact Subgroup.mul_mem _ hx h1
    have hzL : ((ψ y * y⁻¹ : ↥L) : G) ∈ L := (ψ y * y⁻¹ : ↥L).2
    have hle : L ⊓ pCoreOf 2 Hv ≤ pCoreOf 2 L := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
      · intro g hg
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
          le_normalizer_pCoreOf 2 Hv (hLH hg)⟩
      · exact (pCoreOf_isPGroup 2 Hv).to_le inf_le_right
    have hzc : ((ψ y * y⁻¹ : ↥L) : G) ∈ centerOf L := by
      rw [r.ctx.c33.center_eq]
      exact hle ⟨hzL, hz⟩
    exact SBd9.mem_centerOf_iff.mp hzc
  have h1 : ψ = 1 := eq_one_of_central_perfect hperf ψ hcen
  have hxc : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨y, hy⟩ : ↥L) : G)) h1
    simp only [hψ, MulAut.one_apply] at h2
    calc y * x = (x * y * x⁻¹) * x := by rw [h2]
      _ = x * y := by group
  exact (r.CSL_eq h113).le ⟨hxS, hxc⟩

theorem RestHyp.le_normalizer_of_modO2Image_eq (r : RestHyp T Mc M V₁ V₂ Yp I L t) {Hv L' : Subgroup G}
    (hOS : pCoreOf 2 Hv ≤ Sgp153 T V₁) (hL' : L' ∈ cComp Hv) (hLL' : L ≤ L')
    (hnorm : (L'.subgroupOf Hv).Normal) (heq : modO2Image Hv L = modO2Image Hv L') :
    Hv ≤ Subgroup.normalizer (L : Set G) := by
  classical
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := r.S_le_L
  have hL'H : L' ≤ Hv := le_of_mem_cComp hL'
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    have hxI : x ∈ Hv := hL'H hx
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥Hv) ⟨x, hxI⟩ ∈ modO2Image Hv L := by
      rw [heq]
      exact ⟨⟨x, hxI⟩, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    have hv : (((y⁻¹ * ⟨x, hxI⟩ : ↥Hv)) : G) ∈ pCoreOf 2 Hv :=
      (S153D.mem_pCore_iff (y⁻¹ * ⟨x, hxI⟩ : ↥Hv)).mp hyx
    have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hxe : x = (y : G) * (((y⁻¹ * ⟨x, hxI⟩ : ↥Hv)) : G) := by
      simp
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hyL) (hSL (hOS hv))
  have hLn : (L.subgroupOf L').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLL').mpr hL'N
  have hsub : IsSubnormal L Hv :=
    A3.subnormal_trans (A3.subnormal_of_normal hLL' hLn) (A3.subnormal_of_normal hL'H hnorm)
  have hLL'eq : L = L' := by
    by_contra hne
    exact not_subnormal_of_mem_cComp hL' (lt_of_le_of_ne hLL' hne)
      (ne_bot_of_mem_cComp r.ctx.c33.mem) (perfect_of_mem_cComp r.ctx.c33.mem) hsub
  rw [hLL'eq]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hL'H).mp hnorm

end CFSG.Quasithin.SBd14
