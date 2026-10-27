module

public import Mathlib.GroupTheory.Sylow

import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem q2nN7_le_sylow_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H F : Subgroup G} (hFH : F ≤ H) (hFn : (F.subgroupOf H).Normal) (hFp : IsPGroup p F)
    (P : Sylow p G) (hPH : (P : Subgroup G) ≤ H) : F ≤ P := by
  haveI : (F.subgroupOf H).Normal := hFn
  have hFp' : IsPGroup p (F.subgroupOf H) := by
    intro x
    obtain ⟨k, hk⟩ := hFp ⟨x.1.1, x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hle : F.subgroupOf H ≤ (P.subtype hPH : Subgroup H) :=
    IsPGroup.le_sylow_of_normal hFp' (P.subtype hPH)
  intro f hf
  have hmem : (⟨f, hFH hf⟩ : H) ∈ F.subgroupOf H := hf
  exact hle hmem

theorem q2nN7_exists_sylow_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H F : Subgroup G) (hFH : F ≤ H) (hFn : (F.subgroupOf H).Normal) (hFp : IsPGroup p F)
    (hnorm : Subgroup.normalizer (F : Set G) ≤ H)
    (hwc : ∀ y : G, (∀ f ∈ F, y * f * y⁻¹ ∈ H) → ∀ f ∈ F, y * f * y⁻¹ ∈ F) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ H := by
  classical
  let Q : Sylow p H := Classical.arbitrary _
  let P₀ : Subgroup G := (Q : Subgroup H).map H.subtype
  have hP₀p : IsPGroup p P₀ := Q.isPGroup'.map H.subtype
  have hP₀H : P₀ ≤ H := Subgroup.map_subtype_le _
  have hFQ : F.subgroupOf H ≤ (Q : Subgroup H) := by
    haveI : (F.subgroupOf H).Normal := hFn
    have hFp' : IsPGroup p (F.subgroupOf H) := by
      intro x
      obtain ⟨k, hk⟩ := hFp ⟨x.1.1, x.2⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    exact IsPGroup.le_sylow_of_normal hFp' Q
  have hFP₀ : F ≤ P₀ := by
    intro f hf
    exact Subgroup.mem_map.mpr ⟨⟨f, hFH hf⟩, hFQ hf, rfl⟩
  obtain ⟨T, hP₀T⟩ := hP₀p.exists_le_sylow
  have hTP₀ : T ≤ P₀ := by
    by_contra hnot
    have hRne : P₀.subgroupOf (T : Subgroup G) ≠ ⊤ := by
      intro htop
      exact hnot (Subgroup.subgroupOf_eq_top.mp htop)
    let R : Subgroup T := P₀.subgroupOf (T : Subgroup G)
    have hRlt : R < ⊤ := lt_of_le_of_ne le_top hRne
    haveI : Group.IsNilpotent T := IsPGroup.isNilpotent (p := p) T.isPGroup'
    have hlt : R < Subgroup.normalizer (R : Set T) :=
      Group.normalizerCondition_of_isNilpotent R hRlt
    obtain ⟨y, hyN, hyR⟩ := IsConcreteLE.exists_of_lt hlt
    have hyP₀ : (y : G) ∉ P₀ := fun h =>
      hyR (Subgroup.mem_subgroupOf.mpr h)
    have hyNormP₀ : (y : G) ∈ Subgroup.normalizer (P₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · intro z hz
        obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hz
        have hmem : (⟨f, hP₀T hf⟩ : T) ∈ R := Subgroup.mem_subgroupOf.mpr hf
        have hconj := (Subgroup.mem_set_normalizer_iff.mp hyN ⟨f, hP₀T hf⟩).mp hmem
        simpa using Subgroup.mem_subgroupOf.mp hconj
      · exact (Subgroup.card_map_of_injective (f := (MulAut.conj (y : G)).toMonoidHom)
          (MulAut.conj (y : G)).injective).ge
    have hyH : (y : G) ∈ H := by
      have hconjH : ∀ f ∈ F, (y : G) * f * (y : G)⁻¹ ∈ H := fun f hf =>
        hP₀H (by
          have := (Subgroup.mem_set_normalizer_iff.mp hyNormP₀ f).mp (hFP₀ hf)
          simpa using this)
      have hconjF : ∀ f ∈ F, (y : G) * f * (y : G)⁻¹ ∈ F := hwc (y : G) hconjH
      have hmaple : F.map (MulAut.conj (y : G)) ≤ F := by
        intro z hz
        obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hz
        simpa using hconjF f hf
      have hmapEq : F.map (MulAut.conj (y : G)) = F := by
        refine Subgroup.eq_of_le_of_card_ge hmaple ?_
        exact (Subgroup.card_map_of_injective (f := (MulAut.conj (y : G)).toMonoidHom)
          (MulAut.conj (y : G)).injective).ge
      exact hnorm (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapEq)
    have hyHnormQ : (⟨(y : G), hyH⟩ : H) ∈ Subgroup.normalizer (Q : Set H) := by
      have hmem : (⟨(y : G), hyH⟩ : H) ∈ (Subgroup.normalizer (P₀ : Set G)).subgroupOf H :=
        hyNormP₀
      have hQeq : P₀.subgroupOf H = (Q : Subgroup H) :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective (Q : Subgroup H)
      rw [Subgroup.subgroupOf_normalizer_eq hP₀H, hQeq] at hmem
      exact hmem
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_pow_pow_eq_one y
    have hkH : (⟨(y : G), hyH⟩ : H) ^ p ^ k = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    have hzp : IsPGroup p (Subgroup.zpowers (⟨(y : G), hyH⟩ : H)) := by
      refine IsPGroup.of_card_dvd_pow (n := k) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hkH
    have hmemInf : (⟨(y : G), hyH⟩ : H) ∈
        (Subgroup.zpowers (⟨(y : G), hyH⟩ : H) : Subgroup H) ⊓
          Subgroup.normalizer (Q : Set H) :=
      ⟨Subgroup.mem_zpowers _, hyHnormQ⟩
    have hEq := IsPGroup.inf_normalizer_sylow hzp Q
    rw [hEq] at hmemInf
    exact hyP₀ (Subgroup.mem_map.mpr ⟨⟨(y : G), hyH⟩, hmemInf.2, rfl⟩)
  exact ⟨T, hTP₀.trans hP₀H⟩

theorem q2nN7_exists_central {X : Type*} [Group X] {p : ℕ} [Fact p.Prime] (P : Subgroup X)
    (hP : IsPGroup p P) (E : Set X) (hE : E.Finite) (hcard : ¬ p ∣ E.ncard)
    (hconj : ∀ y ∈ P, ∀ τ ∈ E, y * τ * y⁻¹ ∈ E) :
    ∃ τ ∈ E, ∀ y ∈ P, y * τ = τ * y := by
  classical
  let act : P → E → E := fun y τ =>
    ⟨y.1 * τ.1 * y.1⁻¹, hconj y.1 y.2 τ.1 τ.2⟩
  have hone : ∀ τ : E, act 1 τ = τ := fun τ => Subtype.ext (by simp [act])
  have hmul : ∀ y z : P, ∀ τ : E, act (y * z) τ = act y (act z τ) :=
    fun y z τ => Subtype.ext (by simp [act, mul_assoc])
  letI : MulAction P E :=
    { smul := act
      one_smul := hone
      mul_smul := hmul }
  have hcard' : ¬ p ∣ Nat.card E := by
    rwa [Nat.card_coe_set_eq]
  obtain ⟨τ, hτ⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card E hcard'
  refine ⟨τ.1, τ.2, fun y hy => ?_⟩
  have hfix : (⟨y, hy⟩ : P) • τ = τ := (MulAction.mem_fixedPoints.mp hτ) ⟨y, hy⟩
  have hval : y * τ.1 * y⁻¹ = τ.1 := congrArg Subtype.val hfix
  calc y * τ.1 = (y * τ.1 * y⁻¹) * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = τ.1 * y := by rw [hval]

end CFSG.StandardType.FrameRoute.FS81

end
