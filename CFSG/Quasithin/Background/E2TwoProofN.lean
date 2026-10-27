module

public import CFSG.Quasithin.Background.E2TwoProofBar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native B6

namespace E2P

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

theorem isPGroup_quotient_of_sup {G : Type*} [Group G] {N T : Subgroup G} [N.Normal]
    (hT : IsPGroup 2 T) (hNT : N ⊔ T = ⊤) : IsPGroup 2 (G ⧸ N) := by
  have hT2' : IsPGroup 2 (T.map (QuotientGroup.mk' N)) := hT.map _
  have heq : T.map (QuotientGroup.mk' N) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hy : y ∈ N ⊔ T := by rw [hNT]; trivial
    rw [Subgroup.mem_sup_of_normal_left] at hy
    obtain ⟨n, hn, t, ht, rfl⟩ := hy
    refine ⟨t, ht, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have := (inferInstance : N.Normal).conj_mem _ hn t⁻¹
    simpa [mul_assoc] using this
  rw [heq] at hT2'
  exact hT2'.of_equiv Subgroup.topEquiv

theorem mem_of_odd_orderOf {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : IsPGroup 2 (G ⧸ N)) {z : G} (hz : ¬ 2 ∣ orderOf z) : z ∈ N := by
  obtain ⟨k, hk⟩ := hN (QuotientGroup.mk z)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  refine mem_of_pow_mem_of_coprime hk ?_
  exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hz).symm

theorem not_isSolvable_of_isQuasisimple {G : Type*} [Group G] [Finite G]
    (hG : CFSG.IsQuasisimple G) : ¬ Group.IsSolvable G := by
  obtain ⟨hperf, hs, -⟩ := hG
  have hnt : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Subsingleton (G ⧸ Subgroup.center G) := Quotient.instSubsingletonQuotient _
    exact hs.toNontrivial.exists_pair_ne.elim fun a ha => ha.elim fun b hab => hab
      (Subsingleton.elim a b)
  exact Group.IsPerfect.not_isSolvable G

namespace Setting

variable {L : Subgroup (E2.StarQuot M H)} {K : Subgroup Γ} (S : Setting H T M L K)
include S

theorem normal_kZero (hLn : L.Normal) : (K.subgroupOf H).Normal := by
  set K₀ := K.subgroupOf H
  have hK₀ : K₀ ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp S.cComp
  have hinj := map_injOn_cComp_top (starMap M H) (isSolvable_ker_starMap S.minPar)
  have hK₀L : K₀.map (starMap M H) = L := S.star_eq
  refine ⟨fun k hk h => ?_⟩
  set K₁ := K₀.map (MulAut.conj h).toMonoidHom with hK₁
  have hconj : K₁ ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥H) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj h) hK₀
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective] at h1
  have himage : K₁.map (starMap M H) = K₀.map (starMap M H) := by
    have h1 : K₁.map (starMap M H) =
        (K₀.map (starMap M H)).map (MulAut.conj (starMap M H h)).toMonoidHom := by
      rw [hK₁, Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [h1, hK₀L]
    exact conjSub_eq_self (Subgroup.le_normalizer_of_normal (Subgroup.mem_top _))
  have heq := hinj hconj hK₀ himage
  have : h * k * h⁻¹ ∈ K₁ := ⟨k, hk, rfl⟩
  rwa [heq] at this

theorem kbar_normal (hLn : L.Normal) : (kbar H K).Normal :=
  (S.normal_kZero hLn).map _ (QuotientGroup.mk'_surjective _)

theorem kbar_sup_tbar : kbar H K ⊔ (T.subgroupOf H).map (barMap H) = ⊤ := by
  have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le S.le,
      Subgroup.map_subgroupOf_eq_of_le S.minPar.isSylow.1, Subgroup.map_top,
      Subgroup.range_subtype]
    exact S.sup_eq.symm
  rw [kbar, ← Subgroup.map_sup, h1, Subgroup.map_top]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

theorem tbar_isPGroup : IsPGroup 2 ((T.subgroupOf H).map (barMap H)) := by
  have hT2 : IsPGroup 2 (T.subgroupOf H) :=
    S.minPar.isSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe S.minPar.isSylow.1).symm
  exact hT2.map _

theorem jbar_le_kbar (hLn : L.Normal) : jbar M H ≤ kbar H K := by
  have := S.kbar_normal hLn
  have hq := isPGroup_quotient_of_sup S.tbar_isPGroup S.kbar_sup_tbar
  intro z hz
  refine mem_of_odd_orderOf hq ?_
  intro h2
  apply S.card_jbar_odd
  have h1 : orderOf z ∣ Nat.card (jbar M H) := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(jbar M H))
    rwa [Subgroup.orderOf_mk] at this
  exact h2.trans h1

theorem isSolvable_jbar : Group.IsSolvable (jbar M H) := by
  rw [← S.kerIn_bar]
  exact S.minPar_bar.isSolvable_kerIn

theorem commute_of_mem_jbar (h36 : A36CoreForSQTKCat) {z k : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hz : z ∈ jbar M H) (hzK : z ∈ kbar H K) (hk : k ∈ kbar H K) : z * k = k * z := by
  have hq := S.kbar_isQuasisimple h36
  have hJn : (jbar M H).Normal := by
    rw [← S.kerIn_bar]
    infer_instance
  have hNn : ((jbar M H).subgroupOf (kbar H K)).Normal := hJn.subgroupOf _
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with htop | hcen
  · exfalso
    apply not_isSolvable_of_isQuasisimple hq
    have hle : kbar H K ≤ jbar M H := by
      intro y hy
      have : (⟨y, hy⟩ : ↥(kbar H K)) ∈ (jbar M H).subgroupOf (kbar H K) := by rw [htop]; trivial
      exact this
    have := S.isSolvable_jbar
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  · have hmem : (⟨z, hzK⟩ : ↥(kbar H K)) ∈ Subgroup.center ↥(kbar H K) := hcen hz
    have := Subgroup.mem_center_iff.mp hmem ⟨k, hk⟩
    exact (congrArg Subtype.val this).symm

theorem center_le_jbar (hLn : L.Normal) :
    (Subgroup.center ↥(kbar H K)).map (kbar H K).subtype ≤ jbar M H := by
  have hKn := S.kbar_normal hLn
  set C := (Subgroup.center ↥(kbar H K)).map (kbar H K).subtype with hC
  have hCn : C.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨z, hz, rfl⟩ g
    have hgz : g * (z : ↥H ⧸ CFSG.pCore 2 ↥H) * g⁻¹ ∈ kbar H K := hKn.conj_mem _ z.2 g
    refine ⟨⟨_, hgz⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk' : g⁻¹ * (k : ↥H ⧸ CFSG.pCore 2 ↥H) * g ∈ kbar H K := by
      have := hKn.conj_mem _ k.2 g⁻¹
      simpa using this
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp (SetLike.mem_coe.mp hz) ⟨_, hk'⟩)
    simp only [Subgroup.coe_mul] at hc ⊢
    calc (k : ↥H ⧸ CFSG.pCore 2 ↥H) * (g * z * g⁻¹)
        = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * k := by group
  have hCnil : Group.IsNilpotent C := by
    have : IsMulCommutative C := by
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a, ⟨a', ha, rfl⟩⟩ := a
      obtain ⟨b, ⟨b', hb, rfl⟩⟩ := b
      apply Subtype.ext
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp ha b')
      simpa using this.symm
    infer_instance
  have hle : C ≤ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := le_sSup ⟨hCn, hCnil⟩
  have hns : ¬ Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H) := fun hs => by
    have := isSolvable_ker_barMap H
    exact S.ns (Group.isSolvable_of_ker_le_range (barMap H).ker.subtype (barMap H)
      (by rw [Subgroup.range_subtype]))
  rw [S.minPar_bar.fittingSubgroup_eq_kerIn (open_pCore_bar H) hns, S.kerIn_bar] at hle
  exact hle

theorem mem_kerIn_iff (h36 : A36CoreForSQTKCat) (hLn : L.Normal) (x : Γ) :
    x ∈ kerIn M H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H := by
  have hQ : pCoreOf 2 H = (CFSG.pCore 2 ↥H).map H.subtype := rfl
  have hKQ : K ⊔ pCoreOf 2 H = (K.subgroupOf H ⊔ CFSG.pCore 2 ↥H).map H.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le S.le, ← hQ]
  have hbarK : ∀ y₀ : ↥H, y₀ ∈ K.subgroupOf H ⊔ CFSG.pCore 2 ↥H → barMap H y₀ ∈ kbar H K := by
    intro y₀ hy
    have h1 : barMap H y₀ ∈ (K.subgroupOf H ⊔ CFSG.pCore 2 ↥H).map (barMap H) := ⟨y₀, hy, rfl⟩
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  have hker : ∀ z : ↥H, barMap H z = 1 → z ∈ CFSG.pCore 2 ↥H := fun z hz => by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
  constructor
  · intro hx
    have hxH : x ∈ H := S.minPar.kerIn_le_H hx
    set x₀ : ↥H := ⟨x, hxH⟩
    have hx₀J : x₀ ∈ (kerIn M H).subgroupOf H := hx
    have hxbarJ : barMap H x₀ ∈ jbar M H := ⟨x₀, hx₀J, rfl⟩
    have hxbarK : barMap H x₀ ∈ kbar H K := S.jbar_le_kbar hLn hxbarJ
    obtain ⟨k₀, hk₀, hk₀x⟩ := hxbarK
    have hq : k₀⁻¹ * x₀ ∈ CFSG.pCore 2 ↥H := hker _ (by rw [map_mul, map_inv, hk₀x, inv_mul_cancel])
    have hx₀KQ : x₀ ∈ K.subgroupOf H ⊔ CFSG.pCore 2 ↥H := by
      have : x₀ = k₀ * (k₀⁻¹ * x₀) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk₀) (Subgroup.mem_sup_right hq)
    refine ⟨hKQ ▸ ⟨x₀, hx₀KQ, rfl⟩, fun y hy => ?_⟩
    rw [hKQ] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hybar := hbarK y₀ hy₀
    have hcomm := S.commute_of_mem_jbar h36 hxbarJ (S.jbar_le_kbar hLn hxbarJ) hybar
    have h1 : barMap H (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    rw [hQ]
    exact ⟨_, hker _ h1, rfl⟩
  · rintro ⟨hxKQ, hcomm⟩
    rw [hKQ] at hxKQ
    obtain ⟨x₀, hx₀, rfl⟩ := hxKQ
    have hxbarK := hbarK x₀ hx₀
    have hcen : (⟨barMap H x₀, hxbarK⟩ : ↥(kbar H K)) ∈ Subgroup.center ↥(kbar H K) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨k, k₀, hk₀, rfl⟩
      apply Subtype.ext
      have hk₀KQ : (k₀ : Γ) ∈ K ⊔ pCoreOf 2 H := by
        rw [hKQ]
        exact ⟨k₀, Subgroup.mem_sup_left hk₀, rfl⟩
      have h1 := hcomm _ hk₀KQ
      rw [hQ] at h1
      obtain ⟨q, hq, hqeq⟩ := h1
      have hqe : q = x₀ * k₀ * x₀⁻¹ * k₀⁻¹ := Subtype.ext hqeq
      have h2 : barMap H (x₀ * k₀ * x₀⁻¹ * k₀⁻¹) = 1 := by
        rw [← hqe, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hq
      simp only [map_mul, map_inv] at h2
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hxJ : barMap H x₀ ∈ jbar M H := S.center_le_jbar hLn ⟨_, hcen, rfl⟩
    obtain ⟨j₀, hj₀, hj₀x⟩ := hxJ
    have hq : j₀⁻¹ * x₀ ∈ CFSG.pCore 2 ↥H :=
      hker _ (by rw [map_mul, map_inv, hj₀x, inv_mul_cancel])
    have hJ : j₀⁻¹ * x₀ ∈ (kerIn M H).subgroupOf H := by
      rw [← ker_starMap]
      exact S.pCore_le_ker hq
    have hx₀J : x₀ ∈ (kerIn M H).subgroupOf H := by
      have : x₀ = j₀ * (j₀⁻¹ * x₀) := by group
      rw [this]
      exact Subgroup.mul_mem _ hj₀ hJ
    exact hx₀J

end Setting

end E2P

end CFSG.Quasithin
