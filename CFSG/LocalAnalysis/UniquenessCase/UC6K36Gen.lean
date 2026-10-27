module

public import CFSG.Open.LocalVocabulary
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup

variable {G : Type*} [Group G]

theorem perfect_le_of_le_sup_of_isSolvable {P S K : Subgroup G} (hP : Group.IsPerfect P)
    (hS : Group.IsSolvable S) (hSK : S ≤ normalizer (K : Set G)) (hPSK : P ≤ S ⊔ K) : P ≤ K := by
  set N : Subgroup G := normalizer (K : Set G) with hN
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hSKN : S ⊔ K ≤ N := sup_le hSK hKN
  have hPN : P ≤ N := hPSK.trans hSKN
  haveI : (K.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let π : N →* N ⧸ K.subgroupOf N := QuotientGroup.mk' (K.subgroupOf N)
  have hS' : Group.IsSolvable (S.subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hSK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSK).injective
  haveI : Group.IsPerfect P := hP
  haveI hP' : Group.IsPerfect (P.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPN).symm.surjective
  have hsolv : Group.IsSolvable ((S.subgroupOf N).map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap (S.subgroupOf N)) (π.subgroupMap_surjective _)
  have hle : (P.subgroupOf N).map π ≤ (S.subgroupOf N).map π := by
    have h1 : P.subgroupOf N ≤ (S ⊔ K).subgroupOf N := fun x hx => hPSK hx
    rw [Subgroup.subgroupOf_sup hSK hKN] at h1
    refine (Subgroup.map_mono h1).trans ?_
    rw [Subgroup.map_sup]
    have hbot : (K.subgroupOf N).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hbot, sup_bot_eq]
  haveI hT : Group.IsPerfect ((P.subgroupOf N).map π) := Group.IsPerfect.map π
  have hTs : Group.IsSolvable ((P.subgroupOf N).map π) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hbot : (P.subgroupOf N).map π = ⊥ := by
    by_contra hne
    haveI : Nontrivial ((P.subgroupOf N).map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable _ hTs
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro x hx
  exact hbot (show (⟨x, hPN hx⟩ : N) ∈ P.subgroupOf N from hx)

theorem eq_of_forall_mul_mem_center {K : Subgroup G} (hK : Group.IsPerfect K) {g : G}
    (hg : g ∈ normalizer (K : Set G))
    (hz : ∀ k ∈ K, ∀ y ∈ K, (k⁻¹ * (g * k * g⁻¹)) * y = y * (k⁻¹ * (g * k * g⁻¹))) :
    ∀ k ∈ K, g * k * g⁻¹ = k := by
  haveI : Group.IsPerfect K := hK
  have hmem : ∀ k ∈ K, k⁻¹ * (g * k * g⁻¹) ∈ K := fun k hk =>
    K.mul_mem (K.inv_mem hk) ((Subgroup.mem_normalizer_iff.1 hg k).1 hk)
  let δ : K →* K :=
    { toFun := fun k => ⟨k⁻¹ * (g * k * g⁻¹), hmem k k.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun k1 k2 => by
        apply Subtype.ext
        have h1 := hz k1 k1.2 (k2⁻¹ : G) (K.inv_mem k2.2)
        show ((k1 * k2 : K) : G)⁻¹ * (g * ((k1 * k2 : K) : G) * g⁻¹) =
          ((k1 : G)⁻¹ * (g * (k1 : G) * g⁻¹)) * ((k2 : G)⁻¹ * (g * (k2 : G) * g⁻¹))
        calc ((k1 * k2 : K) : G)⁻¹ * (g * ((k1 * k2 : K) : G) * g⁻¹)
            = (k2 : G)⁻¹ * ((k1 : G)⁻¹ * (g * k1 * g⁻¹)) * (g * k2 * g⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
          _ = ((k1 : G)⁻¹ * (g * k1 * g⁻¹)) * (k2 : G)⁻¹ * (g * k2 * g⁻¹) := by
              rw [← h1]
          _ = _ := by group }
  haveI : Group.IsPerfect δ.range := Group.IsPerfect.range δ
  haveI : IsMulCommutative δ.range := ⟨⟨fun a b => by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    have hxy := hz x x.2 (δ y : G) (δ y).2
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
    exact hxy⟩⟩
  intro k hk
  have h0 : (⟨δ ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ : δ.range) = 1 := Subsingleton.elim _ _
  have h1 : (δ ⟨k, hk⟩ : K) = 1 := congrArg Subtype.val h0
  have h2 : k⁻¹ * (g * k * g⁻¹) = 1 := congrArg Subtype.val h1
  calc g * k * g⁻¹ = k * (k⁻¹ * (g * k * g⁻¹)) := by group
    _ = k := by rw [h2, mul_one]

theorem le_pCoreOf_of_normal {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hp : IsPGroup p N) : N ≤ CFSG.Open.pCoreOf p H := by
  have hp' : IsPGroup p (N.subgroupOf H) :=
    hp.of_injective (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNH).injective
  have h1 : N.subgroupOf H ≤ CFSG.pCore p ↥H := le_sSup ⟨hN, hp'⟩
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le hNH] at h2
  exact h2

theorem exists_conj_le_sylow_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {K : Subgroup G} (hK : K.IsSubnormal) {A : Subgroup G} (hAK : A ≤ K) (hA : IsPGroup p A) :
    ∃ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hK
  have hA' : IsPGroup p (A.subgroupOf K) :=
    hA.of_injective (Subgroup.subgroupOfEquivOfLe hAK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAK).injective
  obtain ⟨R', hR'⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) R' R
  refine ⟨(g : G), g.2, fun a ha => ?_⟩
  have h1 : (⟨a, hAK ha⟩ : K) ∈ (R' : Subgroup K) := hR' (show (⟨a, hAK ha⟩ : K) ∈ A.subgroupOf K from ha)
  have h2 : (MulAut.conj g • (⟨a, hAK ha⟩ : K)) ∈ ((g • R' : Sylow p K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [hg] at h2
  have h3 : ((MulAut.conj g • (⟨a, hAK ha⟩ : K) : K) : G) ∈ (P : Subgroup G) ⊓ K := by
    rw [← hR]
    exact ⟨_, h2, rfl⟩
  have h4 : ((MulAut.conj g • (⟨a, hAK ha⟩ : K) : K) : G) = (g : G) * a * (g : G)⁻¹ := rfl
  rw [h4] at h3
  exact h3.1

end CFSG.LocalAnalysis.UniquenessCase.UCK
