module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Quot
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.GroupTheory.PerfectResidualNodes

public section

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem mem_sup_decomp_of_le_normalizer {G : Type*} [Group G] {K θ : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (θ : Set G)) {x : G} (hx : x ∈ K ⊔ θ) :
    ∃ k ∈ K, ∃ t ∈ θ, k * t = x := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right K θ hK
  have hx' : x ∈ ((K ⊔ θ : Subgroup G) : Set G) := hx
  rw [h] at hx'
  exact Set.mem_mul.mp hx'

theorem exists_perfect_lift_normalizer_sylow {G : Type*} [Group G] [Finite G]
    {θ H K S : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hθH : θ ≤ H) (hHθ : H ≤ Subgroup.normalizer (θ : Set G))
    (hSθ : S ≤ θ) (hSp : IsPGroup p S) (hSidx : ¬ p ∣ S.relIndex θ)
    (hKH : K ≤ H) (hKperf : ⁅K, K⁆ = K) :
    ∃ K₁ : Subgroup G, K₁ ≤ H ∧ K₁ ≤ Subgroup.normalizer (S : Set G) ∧ ⁅K₁, K₁⁆ = K₁ ∧
      K₁ ⊔ θ = K ⊔ θ := by
  have hMθ : K ⊔ θ ≤ Subgroup.normalizer (θ : Set G) := (sup_le hKH hθH).trans hHθ
  have hKθ : K ≤ Subgroup.normalizer (θ : Set G) := le_sup_left.trans hMθ
  haveI hθM : (θ.subgroupOf (K ⊔ θ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hMθ
  haveI hQfin : Finite (↥(K ⊔ θ) ⧸ θ.subgroupOf (K ⊔ θ)) := inferInstance
  have hSθp : IsPGroup p (S.subgroupOf θ) := hSp.comap_subtype
  obtain ⟨P, hP⟩ : ∃ P : Sylow p θ, (P : Subgroup θ) = S.subgroupOf θ :=
    ⟨hSθp.toSylow hSidx, rfl⟩
  have hfrat : ∀ g ∈ K ⊔ θ, ∃ x ∈ θ, x⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ :=
      CFSG.RankThree.PartTwo.Sec6.exists_inv_mul_mem_normalizer_sylow P (hMθ hg)
    refine ⟨x, hx, ?_⟩
    rw [hP, Subgroup.map_subgroupOf_eq_of_le hSθ] at hxg
    exact hxg
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = (K ⊔ θ) ⊓ Subgroup.normalizer (S : Set G) :=
    ⟨_, rfl⟩
  have hEM : E ≤ K ⊔ θ := by rw [hE]; exact inf_le_left
  have hEN : E ≤ Subgroup.normalizer (S : Set G) := by rw [hE]; exact inf_le_right
  have hgE : ∀ g ∈ K ⊔ θ, ∃ x ∈ θ, ∃ e ∈ E, g = x * e := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ := hfrat g hg
    have he : x⁻¹ * g ∈ E := by
      rw [hE]
      exact Subgroup.mem_inf.mpr
        ⟨mul_mem (inv_mem ((le_sup_right : θ ≤ K ⊔ θ) hx)) hg, hxg⟩
    exact ⟨x, hx, x⁻¹ * g, he, (mul_inv_cancel_left x g).symm⟩
  have hQperf : Group.IsPerfect (↥(K ⊔ θ) ⧸ θ.subgroupOf (K ⊔ θ)) := by
    haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hKperf
    refine Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' (θ.subgroupOf (K ⊔ θ))).comp
      (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ θ))) ?_
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (θ.subgroupOf (K ⊔ θ)) q
    obtain ⟨k, hk, t, ht, hkt⟩ := mem_sup_decomp_of_le_normalizer hKθ m.2
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← hkt, inv_mul_cancel_left]
    exact ht
  obtain ⟨f, hf⟩ : ∃ f : ↥E →* (↥(K ⊔ θ) ⧸ θ.subgroupOf (K ⊔ θ)),
      ∀ x : ↥E, f x = QuotientGroup.mk' (θ.subgroupOf (K ⊔ θ)) (Subgroup.inclusion hEM x) :=
    ⟨(QuotientGroup.mk' (θ.subgroupOf (K ⊔ θ))).comp (Subgroup.inclusion hEM), fun x => rfl⟩
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (θ.subgroupOf (K ⊔ θ)) q
    obtain ⟨x, hx, e, he, hxe⟩ := hgE m.1 m.2
    have hxM : x ∈ K ⊔ θ := (le_sup_right : θ ≤ K ⊔ θ) hx
    refine ⟨⟨e, he⟩, ?_⟩
    rw [hf]
    have hx' : (⟨x, hxM⟩ : ↥(K ⊔ θ)) ∈ θ.subgroupOf (K ⊔ θ) :=
      Subgroup.mem_subgroupOf.mpr hx
    have h1 : QuotientGroup.mk' (θ.subgroupOf (K ⊔ θ))
        (⟨x, hxM⟩ : ↥(K ⊔ θ)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx'
    have hm : m = (⟨x, hxM⟩ : ↥(K ⊔ θ)) * Subgroup.inclusion hEM ⟨e, he⟩ :=
      Subtype.ext (by simp [hxe])
    rw [hm, map_mul, h1, one_mul]
  have hfrange : f.range = ⊤ := MonoidHom.range_eq_top_of_surjective f hfsurj
  have hfR : Group.IsPerfect f.range := by
    rw [hfrange]
    exact Group.IsPerfect.top_iff.mpr hQperf
  have htr := (CFSG.perfect_residual_transport f).1
  have hmap : (CFSG.perfectResidual ↥E).map f = f.range :=
    htr.trans (CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect hfR)
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : Subgroup G, K₁ = (CFSG.perfectResidual ↥E).map E.subtype :=
    ⟨_, rfl⟩
  have hK₁E : K₁ ≤ E := by rw [hK₁]; exact Subgroup.map_subtype_le _
  have hK₁_mem : ∀ x ∈ CFSG.perfectResidual ↥E, (x : G) ∈ K₁ := by
    intro x hx
    rw [hK₁]
    exact Subgroup.mem_map_of_mem E.subtype hx
  have hEK₁ : ∀ e ∈ E, e ∈ K₁ ⊔ θ := by
    intro e he
    have hfe : f ⟨e, he⟩ ∈ f.range := MonoidHom.mem_range.mpr ⟨⟨e, he⟩, rfl⟩
    rw [← hmap] at hfe
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hfe
    rw [hf, hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hxe
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at hxe
    have hmem : (x : G)⁻¹ * e ∈ θ := hxe
    have hx' : (x : G) ∈ K₁ := hK₁_mem x hx
    have hdecomp : e = (x : G) * ((x : G)⁻¹ * e) := (mul_inv_cancel_left _ _).symm
    rw [hdecomp]
    exact mul_mem (Subgroup.mem_sup_left hx') (Subgroup.mem_sup_right hmem)
  refine ⟨K₁, ?_, ?_, ?_, ?_⟩
  · exact hK₁E.trans (hEM.trans (sup_le hKH hθH))
  · exact hK₁E.trans hEN
  · haveI : Group.IsPerfect (CFSG.perfectResidual ↥E) :=
      (CFSG.perfect_residual_characterization (G := ↥E)).2.2.1
    have hp : Group.IsPerfect ↥K₁ := by
      rw [hK₁]
      exact Group.IsPerfect.map E.subtype
    exact Subgroup.isPerfect_iff.mp hp
  · apply le_antisymm
    · exact sup_le (hK₁E.trans hEM) le_sup_right
    · intro g hg
      obtain ⟨x, hx, e, he, rfl⟩ := hgE g hg
      exact mul_mem (Subgroup.mem_sup_right hx) (hEK₁ e he)

theorem not_centralizes_of_mem_sup {G : Type*} [Group G] [Finite G] {θ K₁ S : Subgroup G}
    (hK₁θ : K₁ ≤ Subgroup.normalizer (θ : Set G)) (hK₁S : K₁ ≤ Subgroup.normalizer (S : Set G))
    (hSθ : S ≤ θ) (hθ3 : ¬ 3 ∣ Nat.card θ) {d : G} (hd : d ∈ K₁ ⊔ θ)
    (hdS : d ∈ Subgroup.normalizer (S : Set G)) (hd3 : d ^ 3 = 1)
    (hnt : ∃ s ∈ S, d * s * d⁻¹ ≠ s) :
    ∃ k ∈ K₁, ∃ s ∈ S, k * s * k⁻¹ ≠ s := by
  by_contra hcon
  have hcon' : ∀ k ∈ K₁, ∀ s ∈ S, k * s * k⁻¹ = s := fun k hk s hs =>
    not_not.mp (fun h => hcon ⟨k, hk, s, hs, h⟩)
  obtain ⟨k, hk, t, ht, hkt⟩ := mem_sup_decomp_of_le_normalizer hK₁θ hd
  have htS : t ∈ Subgroup.normalizer (S : Set G) := by
    have h1 : k⁻¹ * d ∈ Subgroup.normalizer (S : Set G) := mul_mem (inv_mem (hK₁S hk)) hdS
    have h2 : k⁻¹ * d = t := by rw [← hkt, inv_mul_cancel_left]
    rwa [h2] at h1
  have key : ∀ s ∈ S, d * s * d⁻¹ = t * s * t⁻¹ := by
    intro s hs
    have hts : t * s * t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp htS s).mp hs
    have h2 : k * (t * s * t⁻¹) * k⁻¹ = t * s * t⁻¹ := hcon' k hk _ hts
    rw [← hkt]
    calc k * t * s * (k * t)⁻¹ = k * (t * s * t⁻¹) * k⁻¹ := by group
      _ = t * s * t⁻¹ := h2
  have hc3 : ∀ s ∈ S, t ^ 3 * s * (t ^ 3)⁻¹ = s := by
    intro s hs
    have hs1 : t * s * t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp htS s).mp hs
    have hs2 : t * (t * s * t⁻¹) * t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp htS _).mp hs1
    have hd3' : d * (d * d) = 1 := by rw [← pow_three]; exact hd3
    have e0 : d * (d * (d * s * d⁻¹) * d⁻¹) * d⁻¹ = s := by
      have h3 : d * (d * (d * s * d⁻¹) * d⁻¹) * d⁻¹ = (d * (d * d)) * s * (d * (d * d))⁻¹ := by
        group
      rw [h3, hd3', inv_one, one_mul, mul_one]
    rw [key s hs, key _ hs1, key _ hs2] at e0
    rw [pow_three]
    calc t * (t * t) * s * (t * (t * t))⁻¹ = t * (t * (t * s * t⁻¹) * t⁻¹) * t⁻¹ := by group
      _ = s := e0
  have hC3 : t ^ 3 ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    calc s * t ^ 3 = (t ^ 3 * s * (t ^ 3)⁻¹) * t ^ 3 := by rw [hc3 s hs]
      _ = t ^ 3 * s := by group
  have ht_n : t ^ Nat.card θ = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨t, ht⟩ : θ)))
  have hgcd : Nat.gcd 3 (Nat.card θ) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hbez : (1 : ℤ) = 3 * Nat.gcdA 3 (Nat.card θ) + (Nat.card θ : ℤ) * Nat.gcdB 3 (Nat.card θ) := by
    have h := Nat.gcd_eq_gcd_ab 3 (Nat.card θ)
    rw [hgcd] at h
    push_cast at h
    linarith
  have hC3' : t ^ (3 : ℤ) ∈ Subgroup.centralizer (S : Set G) := by
    simpa using hC3
  have hcen : t ∈ Subgroup.centralizer (S : Set G) := by
    have h1 : t = t ^ (3 * Nat.gcdA 3 (Nat.card θ) + (Nat.card θ : ℤ) * Nat.gcdB 3 (Nat.card θ)) := by
      rw [← hbez, zpow_one]
    rw [h1, zpow_add, zpow_mul, zpow_mul, zpow_natCast, ht_n, one_zpow, mul_one]
    exact zpow_mem hC3' _
  have hts : ∀ s ∈ S, t * s * t⁻¹ = s := by
    intro s hs
    have h := (Subgroup.mem_centralizer_iff.mp hcen) s hs
    rw [← h, mul_inv_cancel_right]
  obtain ⟨s0, hs0, hne⟩ := hnt
  exact hne ((key s0 hs0).trans (hts s0 hs0))

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_of_component_center_bot {X : Type*} [Group X] {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (hZ : Subgroup.center J = ⊥) : IsSimpleGroup J := by
  have hs : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  let e : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem isSimple_quotient_of_map_eq {a : G} {K₁ : Subgroup G}
    (hK₁a : K₁ ≤ Subgroup.centralizer ({a} : Set G))
    [((inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))).subgroupOf
      K₁).Normal]
    {J : Subgroup (QAt a)}
    (hJ : (K₁.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) = J) (hs : IsSimpleGroup J) :
    IsSimpleGroup (K₁ ⧸ (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))).subgroupOf K₁) := by
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : ↥K₁ →* QAt a, ∀ k : ↥K₁,
      f₀ k = QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) ⟨(k : G), hK₁a k.2⟩ :=
    ⟨(QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))).comp (Subgroup.inclusion hK₁a),
      fun k => rfl⟩
  have hrange : f₀.range = J := by
    rw [← hJ]
    ext x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [hf₀ k]
      have hk : (⟨(k : G), hK₁a k.2⟩ : CAt a) ∈
          K₁.subgroupOf (Subgroup.centralizer ({a} : Set G)) :=
        Subgroup.mem_subgroupOf.mpr k.2
      exact Subgroup.mem_map_of_mem _ hk
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact MonoidHom.mem_range.mpr ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, hf₀ _⟩
  have hker : f₀.ker = (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))).subgroupOf K₁ := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf₀ k, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hk
      exact Subgroup.mem_map_of_mem (Subgroup.centralizer ({a} : Set G)).subtype hk
    · intro hk
      have hk' : (k : G) ∈ (aschbacherSolvableCore 3 (CAt a)).map
          (Subgroup.centralizer ({a} : Set G)).subtype := hk
      obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hk'
      have hyeq : y = ⟨(k : G), hK₁a k.2⟩ := Subtype.ext hyk
      rw [hyeq] at hy
      exact hy
  have e1 : ↥K₁ ⧸ f₀.ker ≃* f₀.range := QuotientGroup.quotientKerEquivRange f₀
  have e2 := QuotientGroup.quotientMulEquivOfEq (M := (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))).subgroupOf K₁) (N := f₀.ker) hker.symm
  have e3 : f₀.range ≃* J := MulEquiv.subgroupCongr hrange
  exact (e2.trans (e1.trans e3)).isSimpleGroup

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

theorem theta_centralizer_le_centralizer {a : G} :
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.centralizer ({a} : Set G) :=
  Subgroup.map_subtype_le _

theorem mem_theta_centralizer_iff {a : G} (y : CAt a) :
    (y : G) ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) ↔
      y ∈ aschbacherSolvableCore 3 (CAt a) :=
  Subgroup.mem_map_iff_mem (Subgroup.centralizer ({a} : Set G)).subtype_injective

theorem map_mem_thetaQuot_of_mem_sup {a : G} {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({a} : Set G)) {g : G}
    (hgC : g ∈ Subgroup.centralizer ({a} : Set G))
    (hg : g ∈ K ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (⟨g, hgC⟩ : CAt a) ∈
      (K.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) := by
  have hKn : K ≤ Subgroup.normalizer
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    (hK.trans Subgroup.le_normalizer).trans
      (CFSG.RankThree.PartTwo.Sec6.normalizer_le_normalizer_theta _)
  obtain ⟨k, hk, t, ht, hkt⟩ := mem_sup_decomp_of_le_normalizer hKn hg
  have hkC : k ∈ Subgroup.centralizer ({a} : Set G) := hK hk
  have htC : t ∈ Subgroup.centralizer ({a} : Set G) := theta_centralizer_le_centralizer ht
  have hxeq : (⟨g, hgC⟩ : CAt a) = (⟨k, hkC⟩ : CAt a) * (⟨t, htC⟩ : CAt a) :=
    Subtype.ext hkt.symm
  have htθ : (⟨t, htC⟩ : CAt a) ∈ aschbacherSolvableCore 3 (CAt a) :=
    (mem_theta_centralizer_iff ⟨t, htC⟩).mp ht
  have hπt : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (⟨t, htC⟩ : CAt a) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact htθ
  refine Subgroup.mem_map.mpr ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
  rw [hxeq, map_mul, hπt, mul_one]

theorem map_thetaQuot_le_of_le_sup {a : G} {K₁ K₀ : Subgroup G}
    (h0 : K₀ ≤ Subgroup.centralizer ({a} : Set G))
    (hle : K₁ ≤ K₀ ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    (K₁.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) ≤
      (K₀.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
  have hxK : (x : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hx
  exact map_mem_thetaQuot_of_mem_sup h0 x.2 (hle hxK)

theorem map_thetaQuot_eq_of_sup_eq {a : G} {K₁ K₀ : Subgroup G}
    (h1 : K₁ ≤ Subgroup.centralizer ({a} : Set G)) (h0 : K₀ ≤ Subgroup.centralizer ({a} : Set G))
    (hsup : K₁ ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) =
      K₀ ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) :
    (K₁.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) =
      (K₀.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) := by
  apply le_antisymm
  · exact map_thetaQuot_le_of_le_sup h0 (le_of_le_of_eq le_sup_left hsup)
  · exact map_thetaQuot_le_of_le_sup h1 (le_of_le_of_eq le_sup_left hsup.symm)

theorem inf_sup_theta_eq {a : G} {K K' : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({a} : Set G)) (hK' : K' ≤ Subgroup.centralizer ({a} : Set G))
    (hinf : (K.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) ⊓
      (K'.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) = ⊥) :
    (K ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) ⊓
      (K' ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) =
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    have hgC : g ∈ Subgroup.centralizer ({a} : Set G) :=
      (sup_le hK theta_centralizer_le_centralizer) hg1
    have hA := map_mem_thetaQuot_of_mem_sup hK hgC hg1
    have hB := map_mem_thetaQuot_of_mem_sup hK' hgC hg2
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (⟨g, hgC⟩ : CAt a) ∈
        (K.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) ⊓
          (K'.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) :=
      Subgroup.mem_inf.mpr ⟨hA, hB⟩
    rw [hinf, Subgroup.mem_bot] at h1
    have h2 : (⟨g, hgC⟩ : CAt a) ∈ aschbacherSolvableCore 3 (CAt a) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exact (mem_theta_centralizer_iff ⟨g, hgC⟩).mpr h2
  · exact le_inf le_sup_right le_sup_right

theorem commutator_le_theta_of_map_commutator_eq_bot {a : G} {K₁ K₂ : Subgroup G}
    (h1 : K₁ ≤ Subgroup.centralizer ({a} : Set G)) (h2 : K₂ ≤ Subgroup.centralizer ({a} : Set G))
    (hc : ⁅(K₁.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))),
      (K₂.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)))⁆ = ⊥) :
    ⁅K₁, K₂⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  refine Subgroup.commutator_le.mpr ?_
  intro g₁ hg₁ g₂ hg₂
  have hC₁ : g₁ ∈ Subgroup.centralizer ({a} : Set G) := h1 hg₁
  have hC₂ : g₂ ∈ Subgroup.centralizer ({a} : Set G) := h2 hg₂
  have hxA : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (⟨g₁, hC₁⟩ : CAt a) ∈
      (K₁.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg₁)
  have hyB : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a)) (⟨g₂, hC₂⟩ : CAt a) ∈
      (K₂.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg₂)
  have hcomm := Subgroup.commutator_mem_commutator hxA hyB
  rw [hc, Subgroup.mem_bot] at hcomm
  have hπ : QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))
      ⁅(⟨g₁, hC₁⟩ : CAt a), (⟨g₂, hC₂⟩ : CAt a)⁆ = 1 := by
    rw [map_commutatorElement]
    exact hcomm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπ
  exact (mem_theta_centralizer_iff ⁅(⟨g₁, hC₁⟩ : CAt a), (⟨g₂, hC₂⟩ : CAt a)⁆).mpr hπ

end CFSG.RankThree.PartTwo.Sec11
