module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvMap

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def preimageSub (K : Subgroup G)
    (W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) : Subgroup G :=
  (W.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 K))).map K.subtype

theorem mem_preimageSub {K : Subgroup G} {W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} {x : G} :
    x ∈ preimageSub K W ↔
      ∃ hx : x ∈ K, QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨x, hx⟩ ∈ W := by
  unfold preimageSub
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨z.2, hz⟩
  · rintro ⟨hx, hW⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hW, rfl⟩

theorem preimageSub_le (K : Subgroup G) (W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
    preimageSub K W ≤ K := by
  unfold preimageSub
  exact Subgroup.map_subtype_le _

theorem imageSub_preimageSub (K : Subgroup G) (W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
    imageSub K (preimageSub K W) = W := by
  have hS : (preimageSub K W).subgroupOf K =
      W.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (preimageSub_le K W)
  unfold imageSub
  rw [hS]
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K)) W

theorem mem_preimageSub_iff_mk_mem {K : Subgroup G}
    {W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} (x : K) :
    (x : G) ∈ preimageSub K W ↔ QuotientGroup.mk' (aschbacherSolvableCore 3 K) x ∈ W := by
  rw [mem_preimageSub]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

private theorem card_comap_mk'_core {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (U : Subgroup (X ⧸ N)) :
    Nat.card (U.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card U := by
  have h1 := Subgroup.card_mul_index (U.comap (QuotientGroup.mk' N))
  rw [Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective N)] at h1
  have h2 := Subgroup.card_mul_index U
  have h3 := Subgroup.card_mul_index N
  have hU0 : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hU0)
  rw [h1, ← h3, Subgroup.index_eq_card, ← h2]
  ring

theorem card_preimageSub (K : Subgroup G) (W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
    Nat.card (preimageSub K W) =
      Nat.card (inSubgroup (aschbacherSolvableCore 3) K) * Nat.card W := by
  unfold preimageSub inSubgroup
  rw [Subgroup.card_subtype, Subgroup.card_subtype,
    card_comap_mk'_core (aschbacherSolvableCore 3 K) W]

theorem inf_theta_eq_bot_of_isPGroup {p : ℕ} [Fact p.Prime] {K D : Subgroup G}
    (hD : IsPGroup p D)
    (hθ : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) :
    D ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ :=
  KFacts.inf_eq_bot_of_coprime hD hθ

theorem mk_injOn_of_isPGroup {p : ℕ} [Fact p.Prime] {K D : Subgroup G} (hD : IsPGroup p D)
    (hθ : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) {x y : K}
    (hx : (x : G) ∈ D) (hy : (y : G) ∈ D)
    (hxy : QuotientGroup.mk' (aschbacherSolvableCore 3 K) x =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) y) : x = y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
  have hmem : ((x⁻¹ * y : K) : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := ⟨_, hxy, rfl⟩
  have hD' : ((x⁻¹ * y : K) : G) ∈ D := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact D.mul_mem (D.inv_mem hx) hy
  have h1 : ((x⁻¹ * y : K) : G) ∈ D ⊓ inSubgroup (aschbacherSolvableCore 3) K :=
    ⟨hD', hmem⟩
  rw [inf_theta_eq_bot_of_isPGroup hD hθ, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp (Subtype.ext h1)

theorem card_imageSub_gen {p : ℕ} [Fact p.Prime] {K D : Subgroup G} (hDK : D ≤ K)
    (hD : IsPGroup p D) (hθ : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) :
    Nat.card (imageSub K D) = Nat.card D := by
  set f : (D.subgroupOf K) →* (K ⧸ aschbacherSolvableCore 3 K) :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp (D.subgroupOf K).subtype with hf
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (mk_injOn_of_isPGroup hD hθ (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2) hab)
  have hrange : f.range = imageSub K D := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]

theorem exists_lift_normalizer_gen {p : ℕ} [Fact p.Prime] {K D : Subgroup G} (hDK : D ≤ K)
    (hD : IsPGroup p D) (hθ : ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K))
    {wb : K ⧸ aschbacherSolvableCore 3 K}
    (hw : wb ∈ Subgroup.normalizer (imageSub K D : Set (K ⧸ aschbacherSolvableCore 3 K))) :
    ∃ w : K, (w : G) ∈ Subgroup.normalizer (D : Set G) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) w = wb := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) wb
  have hDN : D ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
    fun x hx => Sec6.le_normalizer_theta K (hDK hx)
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
    have hθu : d⁻¹ * (y * ⟨b, hbK⟩ * y⁻¹) ∈ aschbacherSolvableCore 3 K := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hdu
      exact QuotientGroup.eq.mp hdu
    have hmemN : ((d⁻¹ * (y * ⟨b, hbK⟩ * y⁻¹) : K) : G) ∈
        inSubgroup (aschbacherSolvableCore 3) K := ⟨_, hθu, rfl⟩
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have key : (y : G) * b * (y : G)⁻¹ =
        (d : G) * ((d⁻¹ * (y * ⟨b, hbK⟩ * y⁻¹) : K) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [key]
    exact Subgroup.mul_mem_sup hdD hmemN
  obtain ⟨t, htθ, htN, -⟩ := KFacts.exists_mul_mem_normalizer hD hθ hDN hyB
  obtain ⟨m, hm, hmt⟩ := Subgroup.mem_map.mp htθ
  have hmt' : (m : G) = t := hmt
  refine ⟨m * y, ?_, ?_⟩
  · rw [Subgroup.coe_mul, hmt']
    exact htN
  · have hm1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) m = 1 :=
      (QuotientGroup.eq_one_iff m).mpr hm
    rw [map_mul, hm1, one_mul]

end CFSG.RankThree.PartTwo.Sec8.Hering611
