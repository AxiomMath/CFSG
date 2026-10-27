module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2Basic
public import CFSG.LocalAnalysis.WeakClosure81.W16CBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

private theorem le_of_isSylowIn_of_le {H S T : Subgroup G} (hS : IsSylowIn 2 S H) (hST : S ≤ T)
    (hTH : T ≤ H) (hT : IsPGroup 2 T) : T ≤ S := by
  have h1 : S.relIndex T * T.relIndex H = S.relIndex H :=
    Subgroup.relIndex_mul_relIndex S T H hST hTH
  have hodd : ¬ 2 ∣ S.relIndex T := fun hd =>
    hS.not_dvd_relIndex (h1 ▸ Dvd.dvd.mul_right hd _)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT
  have hdvd : S.relIndex T ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card (H := S) (K := T)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact hodd (hk ▸ dvd_pow_self 2 hk0)
  exact Subgroup.relIndex_eq_one.1 (by rw [hk, hk0, pow_zero])

private theorem exists_mem_normalizer_of_lt {S P : Subgroup G} (hP : IsPGroup 2 P) (hSP : S < P) :
    ∃ x ∈ P, x ∉ S ∧ x ∈ normalizer (S : Set G) := by
  classical
  have hIP : S.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    exact absurd hSP (not_lt_of_ge (Subgroup.subgroupOf_eq_top.mp htop))
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  obtain ⟨x, hxN, hxS⟩ := SetLike.exists_of_lt (hnc _ hIP)
  refine ⟨x, x.2, fun hx => hxS (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (normalizer (S : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hSP.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem le_M_of_isSylowIn (h1 : W16One G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {P : Subgroup G} (hP : IsSylowIn 2 P H) (hRP : R ≤ P) :
    P ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  have hRM : R ≤ M := c.sylow.le.trans (cTilde_le_M M V₀ V)
  let D : Subgroup G := P ⊓ M
  have hDP : D ≤ P := inf_le_left
  have hDM : D ≤ M := inf_le_right
  have hRD : R ≤ D := le_inf hRP hRM
  have hDlt : D < P := lt_of_le_of_ne hDP fun heq => hnot (by
    rw [← heq]
    exact inf_le_right)
  obtain ⟨x, hxP, hxnotD, hxDnorm⟩ := exists_mem_normalizer_of_lt hP.isPGroup hDlt
  have hxnotM : x ∉ M := fun hxM => hxnotD (show x ∈ D from Subgroup.mem_inf.2 ⟨hxP, hxM⟩)
  have hxH : x ∈ H := hP.le hxP
  have hxD : conjSubgroup D x = D := conjSubgroup_eq_iff_mem_normalizer.2 hxDnorm
  have hDnormV : D ≤ normalizer (V : Set G) :=
    hDM.trans (le_of_eq c.cex.hyp.h6.normalizer_eq.symm)
  have hDnormV₀ : D ≤ normalizer (V₀ : Set G) := hDM.trans c.cex.hyp.h6.le_normalizer₀
  have hDnormCT : D ≤ normalizer (F11.CTilde M V₀ V : Set G) :=
    hDM.trans (le_normalizer_cTilde_of_hyp15 c.cex.hyp)
  have hRQ : R ≤ D ⊓ F11.CTilde M V₀ V := le_inf hRD c.sylow.le
  have hQeq : D ⊓ F11.CTilde M V₀ V = R :=
    le_antisymm (le_of_isSylowIn_of_le c.sylow hRQ inf_le_right
      (hP.isPGroup.to_le (le_trans inf_le_left hDP))) hRQ
  have hDnormR : D ≤ normalizer (R : Set G) := by
    rw [← hQeq]
    intro d hd
    rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_inf,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hd),
      conjSubgroup_eq_iff_mem_normalizer.2 (hDnormCT hd)]
  have hDnormVx : D ≤ normalizer (conjSubgroup V x : Set G) := by
    have h := E3.conjSubgroup_mono_left x hDnormV
    rwa [E3.conjSubgroup_normalizer, hxD] at h
  have hRxD : conjSubgroup R x ≤ D := by
    have h := E3.conjSubgroup_mono_left x hRD
    rwa [hxD] at h
  have hCVR : V ⊓ centralizer (R : Set G) ≤ V₀ := by
    refine fourteen_four c.cex.hyp.h6.elemAbelian (fun m hm => ?_)
      c.cex.hyp.h6.le_normalizer₀ c.cex.hyp.h6.le
      (c.cex.hyp.h6.conjGenerated c.cex.hyp.ne_bot) (fun hle => ?_) c.sylow
    · rw [c.cex.hyp.h6.normalizer_eq]
      exact hm
    · apply c.not_comm
      exact c.cex.le.trans ((Subgroup.le_centralizer_iff).mpr fun b hb =>
        hle ((c.B_le.trans c.sylow.le) hb))
  have hCVRx : conjSubgroup V x ⊓ centralizer (conjSubgroup R x : Set G) ≤
      conjSubgroup V₀ x := by
    have h := E3.conjSubgroup_mono_left x hCVR
    rwa [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer] at h
  have hV₀inf : V₀ ⊓ conjSubgroup V₀ x = ⊥ := by
    rw [inf_comm]
    exact conjSubgroup_inf_self_eq_bot c.cex.hyp.normalizer₀ c.cex.hyp.isTI hxnotM
  have hcomm_conj : ⁅conjSubgroup V x, conjSubgroup R x⁆ ≤ conjSubgroup V₀ x := by
    have h := E3.conjSubgroup_mono_left x (comm_V_R_le c)
    rwa [E3.conjSubgroup_commutator] at h
  have hcommV₀ : ⁅V₀, conjSubgroup R x⁆ ≤ V₀ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp (hRxD.trans hDnormV₀)
  have hV₀Vx : V₀ ⊓ conjSubgroup V x = ⊥ := by
    have hbot : ⁅V₀ ⊓ conjSubgroup V x, conjSubgroup R x⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf ((Subgroup.commutator_mono inf_le_left le_rfl).trans hcommV₀)
        ((Subgroup.commutator_mono inf_le_right le_rfl).trans hcomm_conj)).trans
          (le_of_eq hV₀inf))
    have hcent : V₀ ⊓ conjSubgroup V x ≤ centralizer (conjSubgroup R x : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
    exact le_bot_iff.mp ((le_inf inf_le_left ((le_inf inf_le_right hcent).trans hCVRx)).trans
      (le_of_eq hV₀inf))
  have hcommIV : ⁅conjClosure (U ⊔ V₀) H, V⁆ ≤ V₀ :=
    (Subgroup.commutator_mono (conjClosure_le_R h1 hS c) le_rfl).trans (by
      rw [Subgroup.commutator_comm]
      exact comm_V_R_le c)
  have hcommVxV : ⁅conjSubgroup V x, V⁆ ≤ conjSubgroup V x :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp ((V_le_R c).trans (hRD.trans hDnormVx))
  have hstep5 : ⁅conjSubgroup V x ⊓ conjClosure (U ⊔ V₀) H, V⁆ ≤ V₀ ⊓ conjSubgroup V x :=
    le_inf ((Subgroup.commutator_mono inf_le_right le_rfl).trans hcommIV)
      ((Subgroup.commutator_mono inf_le_left le_rfl).trans hcommVxV)
  have hstep5bot : ⁅conjSubgroup V x ⊓ conjClosure (U ⊔ V₀) H, V⁆ = ⊥ :=
    le_bot_iff.mp (hstep5.trans (le_of_eq hV₀Vx))
  have hxNI : x ∈ normalizer (conjClosure (U ⊔ V₀) H : Set G) :=
    le_normalizer_conjClosure (U ⊔ V₀) H hxH
  have hIxinv : conjSubgroup (conjClosure (U ⊔ V₀) H) x⁻¹ = conjClosure (U ⊔ V₀) H :=
    conjSubgroup_eq_iff_mem_normalizer.2 ((Subgroup.normalizer _).inv_mem hxNI)
  have hVxinvI : conjSubgroup (conjSubgroup V x ⊓ conjClosure (U ⊔ V₀) H) x⁻¹ =
      V ⊓ conjClosure (U ⊔ V₀) H := by
    rw [E3.conjSubgroup_inf, hIxinv, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one]
  have hstep6 : ⁅V ⊓ conjClosure (U ⊔ V₀) H, conjSubgroup V x⁻¹⁆ = ⊥ := by
    have h : conjSubgroup ⁅conjSubgroup V x ⊓ conjClosure (U ⊔ V₀) H, V⁆ x⁻¹ = ⊥ := by
      rw [hstep5bot, E3.conjSubgroup_bot]
    rwa [E3.conjSubgroup_commutator, hVxinvI] at h
  have hVxinv_cent : conjSubgroup V x⁻¹ ≤ centralizer (V ⊓ conjClosure (U ⊔ V₀) H : Set G) := by
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := conjSubgroup V x⁻¹)
      (H₂ := V ⊓ conjClosure (U ⊔ V₀) H)).mp ?_
    rw [Subgroup.commutator_comm (conjSubgroup V x⁻¹) (V ⊓ conjClosure (U ⊔ V₀) H)]
    exact hstep6
  have hUVI : U ≤ V ⊓ conjClosure (U ⊔ V₀) H :=
    le_inf c.cex.le (le_sup_left.trans (le_conjClosure (U ⊔ V₀) H))
  have hVxinv_CU : conjSubgroup V x⁻¹ ≤ centralizer (U : Set G) :=
    hVxinv_cent.trans (Subgroup.centralizer_le hUVI)
  have hD_Mx : D ≤ conjSubgroup M x := by
    have h := E3.conjSubgroup_mono_left x hDM
    rwa [hxD] at h
  have hV_Mx : V ≤ conjSubgroup M x := (V_le_R c).trans (hRD.trans hD_Mx)
  have hVxinv_M : conjSubgroup V x⁻¹ ≤ M := by
    have h := E3.conjSubgroup_mono_left x⁻¹ hV_Mx
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
  have hxinvM : x⁻¹ ∈ M :=
    Cex16.mem_of_conj_le_centralizer h15 hS c.cex (le_inf hVxinv_M hVxinv_CU)
  exact hxnotM (by simpa using M.inv_mem hxinvM)

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81