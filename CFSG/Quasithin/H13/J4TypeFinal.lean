module

public import CFSG.Quasithin.H13.J4TypeJ4
public import CFSG.Quasithin.H13.J4Sylow

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4

theorem mem_center_map_iff {G : Type*} [Group G] {S : Subgroup G} {x : G} :
    x ∈ (Subgroup.center S).map S.subtype ↔ x ∈ S ∧ ∀ y ∈ S, y * x = x * y := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hs ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)

theorem isConj_of_twoCentral {G : Type*} [Group G] [Finite G]
    (hZ : ∀ S : Sylow 2 G, Nat.card (Subgroup.center S) = 2) {z z' : G} (hz : z ≠ 1)
    (hz' : z' ≠ 1) {S S' : Sylow 2 G}
    (hzS : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hzS' : z' ∈ (Subgroup.center (S' : Subgroup G)).map (S' : Subgroup G).subtype) :
    IsConj z z' := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S S'
  obtain ⟨hzS1, hzS2⟩ := mem_center_map_iff.1 hzS
  have hx : g * z * g⁻¹ ∈ (Subgroup.center ((g • S : Sylow 2 G) : Subgroup G)).map
      ((g • S : Sylow 2 G) : Subgroup G).subtype := by
    rw [mem_center_map_iff, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨⟨z, hzS1, rfl⟩, fun y hy => ?_⟩
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    show g * s * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * s * g⁻¹)
    have := hzS2 s hs
    calc g * s * g⁻¹ * (g * z * g⁻¹) = g * (s * z) * g⁻¹ := by group
      _ = g * (z * s) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * (g * s * g⁻¹) := by group
  set K := (Subgroup.center ((g • S : Sylow 2 G) : Subgroup G)).map
    ((g • S : Sylow 2 G) : Subgroup G).subtype
  have hK : (K : Set G).ncard = 2 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hZ _
  have hsub : ({1, z'} : Set G) ⊆ K := by
    rintro _ (rfl | rfl)
    · exact K.one_mem
    · exact hzS'
  have heq : ({1, z'} : Set G) = K :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hK, Set.ncard_pair hz'.symm]) (Set.toFinite _)
  have hxK : g * z * g⁻¹ ∈ ({1, z'} : Set G) := heq ▸ hx
  rcases hxK with h | h
  · exfalso
    apply hz
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h]
    group
  · exact isConj_iff.2 ⟨g, h⟩

theorem twoCentral_of_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G] {z : G} {z' : G'}
    {S : Sylow 2 G} (hzS : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (e : G ≃* G') (hz : e z = z') :
    orderOf z' = orderOf z ∧
      ∃ S' : Sylow 2 G', z' ∈ (Subgroup.center (S' : Subgroup G')).map
        (S' : Subgroup G').subtype := by
  subst hz
  refine ⟨MulEquiv.orderOf_eq e z, ?_⟩
  have : Finite G' := Finite.of_equiv _ e.toEquiv
  have hcard : Nat.card ((S : Subgroup G).map e.toMonoidHom) =
      2 ^ (Nat.card G').factorization 2 := by
    rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  refine ⟨Sylow.ofCard _ hcard, ?_⟩
  obtain ⟨h1, h2⟩ := mem_center_map_iff.1 hzS
  rw [mem_center_map_iff, Sylow.coe_ofCard]
  refine ⟨⟨z, h1, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  show e y * e z = e z * e y
  rw [← map_mul, ← map_mul, h2 y hy]

theorem orderOf_tJ : orderOf tJ = 2 := by
  apply orderOf_eq_prime
  · rw [sq]
    apply Subtype.ext
    rw [Subgroup.coe_mul, OneMemClass.coe_one]
    exact t_mul_t
  · intro h
    have h1 := congrArg Subtype.val h
    rw [OneMemClass.coe_one] at h1
    exact t_ne_one h1

theorem tJ_twoCentral
    :
    ∃ S : Sylow 2 J, tJ ∈ (Subgroup.center (S : Subgroup J)).map (S : Subgroup J).subtype := by
  have := finite_J'
  have hF : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_le_C
  refine ⟨S, mem_center_map_iff.2 ⟨?_, fun y hy => ?_⟩⟩
  · have hP : IsPGroup 2 (Subgroup.zpowers tJ) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_tJ, pow_one]
    have hle : (S : Subgroup J) ≤
        Subgroup.normalizer ((Subgroup.zpowers tJ : Subgroup J) : Set J) := by
      intro s hs
      have h1 : s ∈ Subgroup.centralizer ((Subgroup.zpowers tJ : Subgroup J) : Set J) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact hS hs
      exact Subgroup.centralizer_le_normalizer _ h1
    have hmax := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hP hle) le_sup_left
    rw [← hmax]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tJ)
  · exact (Subgroup.mem_centralizer_iff.1 (hS hy) tJ (Set.mem_singleton tJ)).symm

theorem concreteJ4_typeJ4
    :
    IsSimpleGroup CFSG.Blueprint.NativeSporadic.J4 ∧
      (∃ a b : CFSG.Blueprint.NativeSporadic.J4, a * b ≠ b * a) ∧
      (∀ S : Sylow 2 CFSG.Blueprint.NativeSporadic.J4, Nat.card (Subgroup.center S) = 2) ∧
      (∀ z z' : CFSG.Blueprint.NativeSporadic.J4, orderOf z = 2 → orderOf z' = 2 →
        (∃ S : Sylow 2 CFSG.Blueprint.NativeSporadic.J4,
          z ∈ (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)).map
          (S : Subgroup CFSG.Blueprint.NativeSporadic.J4).subtype) →
        (∃ S : Sylow 2 CFSG.Blueprint.NativeSporadic.J4,
          z' ∈ (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)).map
          (S : Subgroup CFSG.Blueprint.NativeSporadic.J4).subtype) →
        IsConj z z') ∧
      ∀ z₀ : CFSG.Blueprint.NativeSporadic.J4, orderOf z₀ = 2 →
        (∃ S : Sylow 2 CFSG.Blueprint.NativeSporadic.J4,
          z₀ ∈ (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)).map
          (S : Subgroup CFSG.Blueprint.NativeSporadic.J4).subtype) →
        IsTypeJ4Centralizer CFSG.Blueprint.NativeSporadic.J4 z₀ := by
  have hfin : Finite CFSG.Blueprint.NativeSporadic.J4 := fam_j4_simplicity.1
  have := finite_J'
  have hZ := sylowTwo_centers.{0}.2.2.2.2.1
  have hne : ∀ x : CFSG.Blueprint.NativeSporadic.J4, orderOf x = 2 → x ≠ 1 := fun x hx h => by
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hconj : ∀ z z' : CFSG.Blueprint.NativeSporadic.J4, orderOf z = 2 → orderOf z' = 2 →
      (∃ S : Sylow 2 CFSG.Blueprint.NativeSporadic.J4,
        z ∈ (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)).map
          (S : Subgroup CFSG.Blueprint.NativeSporadic.J4).subtype) →
      (∃ S : Sylow 2 CFSG.Blueprint.NativeSporadic.J4,
        z' ∈ (Subgroup.center (S : Subgroup CFSG.Blueprint.NativeSporadic.J4)).map
          (S : Subgroup CFSG.Blueprint.NativeSporadic.J4).subtype) →
      IsConj z z' := fun z z' hz hz' ⟨S, hS⟩ ⟨S', hS'⟩ =>
    isConj_of_twoCentral hZ (hne z hz) (hne z' hz') hS hS'
  refine ⟨isSimpleGroup_J4, ?_, hZ, hconj, fun z₀ hz₀ hS₀ => ?_⟩
  ·
    by_contra hab
    push Not at hab
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 CFSG.Blueprint.NativeSporadic.J4))
    have h1 : Subgroup.center S = ⊤ := by
      rw [eq_top_iff]
      intro s _
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hab _ _)
    have h2 := hZ S
    have hf : (86775571046077562880 : ℕ).factorization 2 = 21 := by
      rw [← CFSG.Sporadic.J4Schreier.card_J4J]
      exact CFSG.Sporadic.J4Schreier.factorization_card_J
    rw [h1, Subgroup.card_top, Sylow.card_eq_multiplicity, card_J4, hf] at h2
    norm_num at h2
  ·
    obtain ⟨S, hS⟩ := tJ_twoCentral
    obtain ⟨t4, ht4⟩ : ∃ y, (seedEquiv j4Facts.mat).symm tJ = y := ⟨_, rfl⟩
    obtain ⟨hord, S', hS'⟩ := @twoCentral_of_mulEquiv J CFSG.Blueprint.NativeSporadic.J4
      (Subgroup.toGroup J) Units.instGroup _ _ _ _ hS (seedEquiv j4Facts.mat).symm ht4
    rw [orderOf_tJ] at hord
    obtain ⟨g, hg⟩ := isConj_iff.1 (hconj _ _ hord hz₀ ⟨S', hS'⟩ hS₀)
    have h1 : IsTypeJ4Centralizer CFSG.Blueprint.NativeSporadic.J4 t4 :=
      @IsTypeJ4Centralizer.of_mulEquiv J CFSG.Blueprint.NativeSporadic.J4 (Subgroup.toGroup J)
        Units.instGroup _ _ _ isTypeJ4Centralizer_tJ (seedEquiv j4Facts.mat).symm ht4
    have hg' : MulAut.conj g t4 = z₀ := by
      rw [MulAut.conj_apply]
      exact hg
    exact @IsTypeJ4Centralizer.of_mulEquiv CFSG.Blueprint.NativeSporadic.J4
      CFSG.Blueprint.NativeSporadic.J4 Units.instGroup Units.instGroup _ _ _ h1 (MulAut.conj g) hg'

end CFSG.Quasithin.H13.J4
