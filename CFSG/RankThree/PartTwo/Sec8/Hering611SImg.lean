module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvMap
public import CFSG.RankThree.PartTwo.Sec8.Hering611SGenB

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mk_eq_of_isPGroup {K D : Subgroup G} (hD3 : IsPGroup 3 D) {x y : K}
    (hx : (x : G) ∈ D) (hy : (y : G) ∈ D)
    (hxy : QuotientGroup.mk' (aschbacherSolvableCore 3 K) x =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) y) : x = y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
  have hmem : ((x⁻¹ * y : K) : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := ⟨_, hxy, rfl⟩
  have hD : ((x⁻¹ * y : K) : G) ∈ D := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact D.mul_mem (D.inv_mem hx) hy
  have hbot : D ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ :=
    KFacts.inf_eq_bot_of_coprime hD3 (Sec11.not_three_dvd_card_inSubgroup_theta K)
  have h1 : ((x⁻¹ * y : K) : G) ∈ D ⊓ inSubgroup (aschbacherSolvableCore 3) K :=
    ⟨hD, hmem⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp (Subtype.ext h1)

theorem card_imageSub_of_isPGroup {K D : Subgroup G} (hDK : D ≤ K) (hD3 : IsPGroup 3 D) :
    Nat.card (imageSub K D) = Nat.card D := by
  set f : (D.subgroupOf K) →* (K ⧸ aschbacherSolvableCore 3 K) :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp (D.subgroupOf K).subtype with hf
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (eq_of_mk_eq_of_isPGroup hD3 (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2) hab)
  have hrange : f.range = imageSub K D := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]

theorem mem_of_mk_mem_imageSub {K D D₁ : Subgroup G} (hD3 : IsPGroup 3 D) (hD₁ : D₁ ≤ D)
    (hDK : D ≤ K) {x : K} (hx : (x : G) ∈ D)
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3 K) x ∈ imageSub K D₁) :
    (x : G) ∈ D₁ := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
  have hxy : y = x :=
    eq_of_mk_eq_of_isPGroup hD3 (hD₁ (Subgroup.mem_subgroupOf.mp hy)) hx hyx
  rw [← hxy]
  exact Subgroup.mem_subgroupOf.mp hy

theorem exists_lift_normalizer {K D : Subgroup G} (hDK : D ≤ K) (hD3 : IsPGroup 3 D)
    {wb : K ⧸ aschbacherSolvableCore 3 K}
    (hw : wb ∈ Subgroup.normalizer (imageSub K D : Set (K ⧸ aschbacherSolvableCore 3 K))) :
    ∃ w : K, (w : G) ∈ Subgroup.normalizer (D : Set G) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) w = wb := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) wb
  have hN3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) :=
    Sec11.not_three_dvd_card_inSubgroup_theta K
  have hDN : D ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
    fun x hx => Sec6.le_normalizer_theta K (hDK hx)
  have hyN : (y : G) ∈ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
    Sec6.le_normalizer_theta K y.2
  have hyB : ∀ b ∈ D, (y : G) * b * (y : G)⁻¹ ∈
      D ⊔ inSubgroup (aschbacherSolvableCore 3) K := by
    intro b hb
    have hbK : b ∈ K := hDK hb
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨b, hbK⟩ : K) ∈
        imageSub K D := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
    have hu : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (y * ⟨b, hbK⟩ * y⁻¹) ∈
        imageSub K D := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hw
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨b, hbK⟩)).mp h1
    obtain ⟨d, hd, hdu⟩ := Subgroup.mem_map.mp hu
    have hθ : d⁻¹ * (y * ⟨b, hbK⟩ * y⁻¹) ∈ aschbacherSolvableCore 3 K := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hdu
      exact QuotientGroup.eq.mp hdu
    have hmemN : ((d⁻¹ * (y * ⟨b, hbK⟩ * y⁻¹) : K) : G) ∈
        inSubgroup (aschbacherSolvableCore 3) K := ⟨_, hθ, rfl⟩
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have key : (y : G) * b * (y : G)⁻¹ =
        (d : G) * ((d⁻¹ * (y * ⟨b, hbK⟩ * y⁻¹) : K) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [key]
    exact Subgroup.mul_mem_sup hdD hmemN
  obtain ⟨n, hn, hnN⟩ := Hering611.exists_mul_mem_normalizer hD3 hN3 hDN hyN hyB
  obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hn
  have hmn' : (m : G) = n := hmn
  refine ⟨y * m, ?_, ?_⟩
  · rw [Subgroup.coe_mul, hmn']
    exact hnN
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hym : (y * m)⁻¹ * y = m⁻¹ := by group
    rw [hym]
    exact (aschbacherSolvableCore 3 K).inv_mem hm

end CFSG.RankThree.PartTwo.Sec8.Hering611
