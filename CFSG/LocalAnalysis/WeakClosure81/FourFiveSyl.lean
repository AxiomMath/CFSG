module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveComp
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q]

private theorem fourFive_le_normalizer_centralizer {A Y : Subgroup Q}
    (h : A ≤ Subgroup.normalizer (Y : Set Q)) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer (Y : Set Q) : Set Q) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    have hz' : a⁻¹ * z * a ∈ Y :=
      (Subgroup.mem_normalizer_iff''.mp (h ha) z).mp hz
    have hxz := hx (a⁻¹ * z * a) hz'
    calc z * (a * x * a⁻¹) = a * ((a⁻¹ * z * a) * x) * a⁻¹ := by group
      _ = a * (x * (a⁻¹ * z * a)) * a⁻¹ := by rw [hxz]
      _ = (a * x * a⁻¹) * z := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    have hz' : a * z * a⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (h ha) z).mp hz
    have hxz := hx (a * z * a⁻¹) hz'
    have h := congrArg (fun t => a⁻¹ * t * a) hxz
    simpa using h

private theorem fourFive_isSylowIn_two_inf_of_isSubnormal {T H L : Subgroup Q}
    (h : IsSubnormal L H) : IsSylowIn 2 T H → IsSylowIn 2 (T ⊓ L) L := by
  induction h generalizing T with
  | refl K => intro hT; rwa [inf_eq_left.mpr hT.le]
  | @step L M K hLM hMn _ ih =>
      intro hT
      have h1 : IsSylowIn 2 (T ⊓ M) M := ih hT
      have h2 := h1.inf_normal hLM hMn
      rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

private theorem fourFive_autNL_le_normalizer (T J : Subgroup Q) :
    F12.autNL T J ≤ Subgroup.normalizer (J : Set Q) := by
  rw [F12.autNL]
  exact sup_le inf_le_right Subgroup.le_normalizer

private theorem fourFive_quotient_autNL_isPGroup {T J : Subgroup Q} (hT : IsPGroup 2 T)
    [hJn : (J.subgroupOf (F12.autNL T J)).Normal] :
    IsPGroup 2 (F12.autNL T J ⧸ (J.subgroupOf (F12.autNL T J))) := by
  set S : Subgroup Q := T ⊓ normalizer (J : Set Q) with hS
  have hSJnorm : S ≤ Subgroup.normalizer (J : Set Q) := by rw [hS]; exact inf_le_right
  have hS2 : IsPGroup 2 S := by rw [hS]; exact hT.to_le inf_le_left
  have hD_eq : F12.autNL T J = S ⊔ J := by rw [F12.autNL, ← hS]
  have hSd : S ≤ F12.autNL T J := by rw [hD_eq]; exact le_sup_left
  have hJd : J ≤ F12.autNL T J := by rw [hD_eq]; exact le_sup_right
  let φ : S →* F12.autNL T J ⧸ (J.subgroupOf (F12.autNL T J)) :=
    (QuotientGroup.mk' (J.subgroupOf (F12.autNL T J))).comp (Subgroup.inclusion hSd)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (J.subgroupOf (F12.autNL T J)) y
    have hd : (d : Q) ∈ (↑(S ⊔ J) : Set Q) := by
      rw [← hD_eq]
      exact d.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S J hSJnorm] at hd
    obtain ⟨s, hs, j, hj, hsj⟩ := hd
    refine ⟨⟨s, hs⟩, ?_⟩
    have hd' : d = ⟨s, hSd hs⟩ * ⟨j, hJd hj⟩ := Subtype.ext (by simpa using hsj.symm)
    rw [hd', map_mul]
    have hj1 : QuotientGroup.mk' (J.subgroupOf (F12.autNL T J)) ⟨j, hJd hj⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((Subgroup.mem_subgroupOf).mpr hj)
    rw [hj1, mul_one]
    rfl
  exact hS2.of_surjective φ hφ

theorem fourFive_component_normal_autNL {T J : Subgroup Q} :
    (J.subgroupOf (F12.autNL T J)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (fourFive_autNL_le_normalizer T J)

theorem fourFive_sylow_inf_component {T N J : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    (hN : FourFiveNMN N) (hJ : IsComponentOf J N) : IsSylowIn 2 (T ⊓ J) J := by
  have hNn : (N.subgroupOf ⊤).Normal := hN.normal.subgroupOf ⊤
  have hTN : IsSylowIn 2 (T ⊓ N) N := hT.inf_normal le_top hNn
  have h := fourFive_isSylowIn_two_inf_of_isSubnormal hJ.2.1 hTN
  rwa [inf_assoc, inf_eq_right.mpr hJ.1] at h

theorem fourFive_sylow_autNL {T N J : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) :
    IsSylowIn 2 (T ⊓ normalizer (J : Set Q)) (F12.autNL T J) := by
  set S : Subgroup Q := T ⊓ normalizer (J : Set Q) with hS
  set D : Subgroup Q := F12.autNL T J with hD
  have hD_eq : D = S ⊔ J := by rw [hD, F12.autNL, ← hS]
  have hSd : S ≤ D := by rw [hD_eq]; exact le_sup_left
  have hS2 : IsPGroup 2 S := by rw [hS]; exact hT.isPGroup.to_le inf_le_left
  have hJn : (J.subgroupOf D).Normal := by rw [hD]; exact fourFive_component_normal_autNL
  have hJd : J ≤ D := by rw [hD_eq]; exact le_sup_right
  have hSJ : S ⊓ J = T ⊓ J := by
    rw [hS, inf_assoc, inf_eq_right.mpr Subgroup.le_normalizer]
  have hkey : S.relIndex D = (S ⊓ J).relIndex J := by
    haveI := hJn
    have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal
      (J.subgroupOf D) (S.subgroupOf D)
    have hsup : J.subgroupOf D ⊔ S.subgroupOf D = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hJd hSd]
      have hJS : J ⊔ S = D := by rw [sup_comm, hD_eq]
      rw [hJS, Subgroup.subgroupOf_self]
    rw [hsup, Subgroup.relIndex_top_right] at h1
    rw [Subgroup.relIndex_subgroupOf hJd, ← Subgroup.inf_relIndex_right] at h1
    exact h1
  have hodd : ¬ 2 ∣ S.relIndex D := by
    rw [hkey, hSJ]
    exact (fourFive_sylow_inf_component hT hN hJ).not_dvd_relIndex
  exact ⟨hSd, hS2, hodd⟩

theorem fourFive_autC_isPGroup {T N J : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) : IsPGroup 2 (F12.autC T J) := by
  haveI hJn : (J.subgroupOf (F12.autNL T J)).Normal := fourFive_component_normal_autNL
  have hquot : IsPGroup 2 (F12.autNL T J ⧸ (J.subgroupOf (F12.autNL T J))) :=
    fourFive_quotient_autNL_isPGroup hT.isPGroup
  haveI : IsSimpleGroup ↥J := (fourFive_nmn_component_simple hN hJ).1
  have hcenter : Subgroup.center ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) (fourFive_nmn_component_simple hN hJ).2
  have hCJ : F12.autC T J ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : x ∈ F12.autC T J ∧ x ∈ J := Subgroup.mem_inf.mp hx
    have hxcent : x ∈ Subgroup.centralizer (J : Set Q) := by
      have hxD := hx'.1
      rw [F12.autC] at hxD
      exact (Subgroup.mem_inf.mp hxD).2
    have hxJ : x ∈ J := hx'.2
    have hxcenter : (⟨x, hxJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent (y : Q) y.2)
    rw [hcenter] at hxcenter
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxcenter)
  let D := F12.autNL T J
  haveI hJnD : (J.subgroupOf D).Normal := hJn
  let π : D →* D ⧸ (J.subgroupOf D) := QuotientGroup.mk' (J.subgroupOf D)
  let φ : F12.autC T J →* D ⧸ (J.subgroupOf D) :=
    π.comp (Subgroup.inclusion (show F12.autC T J ≤ D from inf_le_left))
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a⁻¹ * b) = 1 := by
      simp only [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : (Subgroup.inclusion (show F12.autC T J ≤ D from inf_le_left)) (a⁻¹ * b)
        ∈ J.subgroupOf D := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((a⁻¹ * b : F12.autC T J) : Q) ∈ J := by
      simpa using Subgroup.mem_subgroupOf.mp h2
    have h4 : ((a⁻¹ * b : F12.autC T J) : Q) ∈ F12.autC T J ⊓ J := ⟨(a⁻¹ * b).2, h3⟩
    rw [hCJ] at h4
    have h5 : (a⁻¹ * b : F12.autC T J) = 1 := Subtype.ext (Subgroup.mem_bot.mp h4)
    exact inv_mul_eq_one.mp h5
  exact hquot.of_injective φ hφ

theorem fourFive_autC_le {T N J : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) : F12.autC T J ≤ T ⊓ normalizer (J : Set Q) := by
  have hS := fourFive_sylow_autNL hT hN hJ
  have hC2 := fourFive_autC_isPGroup hT hN hJ
  have hCD : F12.autC T J ≤ F12.autNL T J := inf_le_left
  have hDnormJ : F12.autNL T J ≤ Subgroup.normalizer (J : Set Q) :=
    fourFive_autNL_le_normalizer T J
  have hCn : ((F12.autC T J).subgroupOf (F12.autNL T J)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCD).mpr
      ((le_inf Subgroup.le_normalizer
        (fourFive_le_normalizer_centralizer hDnormJ)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  exact hS.le_of_normal hCD hCn hC2

end CFSG.LocalAnalysis.WeakClosure81
