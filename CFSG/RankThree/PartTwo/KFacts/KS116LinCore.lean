module

public import CFSG.RankThree.PartTwo.KFacts.KS116LinPair
public import CFSG.RankThree.PartTwo.KFacts.KS116LinAbelian
public import CFSG.RankThree.PartTwo.KFacts.KS116LinNonab

public section

namespace CFSG.RankThree.PartTwo.KFacts.NDC

section MinimalNormal

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

theorem exists_minimal_nonscalar_normal [Finite G] (ρ : Representation F G V)
    (T : Subgroup G) [T.Normal] [Group.IsSolvable T]
    (h : ∃ t ∈ T, ¬ ∃ c : F, ρ t = c • (1 : V →ₗ[F] V)) :
    ∃ B : Subgroup G, B.Normal ∧ B ≤ T ∧
      (∃ b ∈ B, ¬ ∃ c : F, ρ b = c • (1 : V →ₗ[F] V)) ∧
      (∀ x ∈ B, ∀ y ∈ B, ∃ c : F, ρ ⁅x, y⁆ = c • (1 : V →ₗ[F] V)) := by
  obtain ⟨t, ht, hnt⟩ := h
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) :=
    {B | B.Normal ∧ B ≤ T ∧ ∃ b ∈ B, ¬ ∃ c : F, ρ b = c • (1 : V →ₗ[F] V)}
  have hTS : T ∈ S := ⟨inferInstance, le_rfl, t, ht, hnt⟩
  obtain ⟨B, hBS, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min S ⟨T, hTS⟩
  obtain ⟨hBn, hBT, b, hb, hbn⟩ := hBS
  refine ⟨B, hBn, hBT, ⟨b, hb, hbn⟩, ?_⟩
  haveI : B.Normal := hBn
  have hB1 : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hb
    exact hbn ⟨1, by rw [hb, map_one, one_smul]⟩
  have hlt : ⁅B, B⁆ < B := by
    haveI : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBT)
    haveI : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB1
    rw [← B.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial B
  have hB'le : ⁅B, B⁆ ≤ B := Subgroup.commutator_le_left B B
  have hB'scalar : ∀ g ∈ ⁅B, B⁆, ∃ c : F, ρ g = c • (1 : V →ₗ[F] V) := by
    intro g hg
    by_contra hgn
    have hmem : ⁅B, B⁆ ∈ S := ⟨inferInstance, hB'le.trans hBT, g, hg, hgn⟩
    exact hmin _ hmem hlt
  intro x hx y hy
  exact hB'scalar _ (Subgroup.commutator_mem_commutator hx hy)

end Rep

end MinimalNormal

section ScalarNormal

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

theorem scalar_of_normal_solvable [Finite F] [Module.Finite F V] [Finite G] (h2 : (2 : F) ≠ 0)
    (ρ : Representation F G V)
    (hirr : ∀ U : Submodule F V, (∀ g, U ≤ U.comap (ρ g)) → U = ⊥ ∨ U = ⊤)
    (hd2 : 2 ≤ Module.finrank F V) (hd3 : Module.finrank F V ≤ 3)
    (T K : Subgroup G) [T.Normal] [Group.IsSolvable T] (h3 : ¬ 3 ∣ Nat.card T)
    (hK : ⁅K, K⁆ = K) (hK1 : ∃ k ∈ K, ρ k ≠ 1) :
    ∀ t ∈ T, ∃ c : F, ρ t = c • (1 : V →ₗ[F] V) := by
  by_contra hcon
  have hnt : ∃ t ∈ T, ¬ ∃ c : F, ρ t = c • (1 : V →ₗ[F] V) := by
    by_contra hno
    apply hcon
    intro t ht
    by_contra hnsc
    exact hno ⟨t, ht, hnsc⟩
  obtain ⟨B, hBn, hBT, ⟨b0, hb0B, hb0⟩, hsc⟩ := exists_minimal_nonscalar_normal ρ T hnt
  haveI : B.Normal := hBn
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hns : ∃ b ∈ B, ∀ c : F, ρ b ≠ c • (1 : V →ₗ[F] V) :=
    ⟨b0, hb0B, fun c hc => hb0 ⟨c, hc⟩⟩
  obtain ⟨k0, hk0K, hk0⟩ := hK1
  by_cases hab : ∀ b ∈ B, ∀ b' ∈ B, ρ b * ρ b' = ρ b' * ρ b
  · by_cases hsimple : ∀ U : Submodule F V, (∀ b ∈ B, U ≤ U.comap (ρ b)) → U = ⊥ ∨ U = ⊤
    · have hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B :=
        fun k _ b hb => hBn.conj_mem b hb k
      have hcomm := commute_of_simple_abelian ρ B K hKB hK hab hsimple
      have hc : ∀ a ∈ K, ∀ b ∈ K, ρ a * ρ b = ρ b * ρ a := fun a ha b hb =>
        schur_commute ρ B hsimple (ρ a) (ρ b) (fun x hx => hcomm a ha x hx)
          (fun x hx => hcomm b hb x hx)
      exact hk0 (perfect_trivial_of_comm ρ hK hc k0 hk0K)
    · have hnsimple : ∃ U : Submodule F V, (∀ b ∈ B, U ≤ U.comap (ρ b)) ∧ U ≠ ⊥ ∧ U ≠ ⊤ := by
        push_neg at hsimple
        exact hsimple
      exact hk0 (eigen_case ρ hirr hd2 hd3 B K hab hns hK hnsimple k0 hk0K)
  · have hnab : ∃ x ∈ B, ∃ y ∈ B, ρ x * ρ y ≠ ρ y * ρ x := by
      push_neg at hab
      obtain ⟨b, hb, b', hb', hne⟩ := hab
      exact ⟨b, hb, b', hb', hne⟩
    have hd : Module.finrank F V = 2 ∨ Module.finrank F V = 3 := by omega
    rcases hd with hd | hd
    · exact hk0 (nonabelian_two h2 hd ρ B K hsc hnab hK k0 hk0K)
    · obtain ⟨x, hx, y, hy, hne⟩ := hnab
      obtain ⟨c, hc⟩ := hsc x hx y hy
      have h3dvd : 3 ∣ orderOf ⁅x, y⁆ := three_dvd_orderOf_commutator hd ρ x y c hc hne
      have hmemB : ⁅x, y⁆ ∈ B :=
        Subgroup.commutator_le_right B B (Subgroup.commutator_mem_commutator hx hy)
      have hmemT : ⁅x, y⁆ ∈ T := hBT hmemB
      have hord : orderOf ⁅x, y⁆ ∣ Nat.card T := by
        have hdvd := orderOf_dvd_natCard (⟨⁅x, y⁆, hmemT⟩ : T)
        rwa [Subgroup.orderOf_mk] at hdvd
      exact h3 (dvd_trans h3dvd hord)

end Rep

end ScalarNormal

section CoreIrreducible

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

theorem core_irreducible {F : Type} [Field F] [Finite F] {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V] (h2 : (2 : F) ≠ 0)
    (ρ : Representation F G V)
    (hirr : ∀ U : Submodule F V, (∀ g, U ≤ U.comap (ρ g)) → U = ⊥ ∨ U = ⊤)
    (hd3 : Module.finrank F V ≤ 3)
    (T K : Subgroup G) (n : G) [T.Normal] [Group.IsSolvable T] (h3 : ¬ 3 ∣ Nat.card T)
    (hK : ⁅K, K⁆ = K) (hKT : ⁅K, K.map (MulAut.conj n).toMonoidHom⁆ ≤ T) :
    ∀ k ∈ K, ρ k = 1 := by
  by_cases hd1 : Module.finrank F V ≤ 1
  · exact perfect_trivial_of_comm ρ hK (fun a _ b _ => comm_of_finrank_le_one hd1 (ρ a) (ρ b))
  have hd2 : 2 ≤ Module.finrank F V := by omega
  by_contra hne
  push_neg at hne
  obtain ⟨k, hk, hkne⟩ := hne
  obtain ⟨K', hK'def⟩ : ∃ K' : Subgroup G, K' = K.map (MulAut.conj n).toMonoidHom :=
    ⟨_, rfl⟩
  rw [← hK'def] at hKT
  have hK' : ⁅K', K'⁆ = K' := by
    rw [hK'def, ← Subgroup.map_commutator, hK]
  have hT : ∀ t ∈ T, ∃ c : F, ρ t = c • (1 : V →ₗ[F] V) :=
    scalar_of_normal_solvable h2 ρ hirr hd2 hd3 T K h3 hK ⟨k, hk, hkne⟩
  have hsc : ∀ a ∈ K, ∀ b ∈ K', ∃ c : F, ρ ⁅a, b⁆ = c • (1 : V →ₗ[F] V) := by
    intro a ha b hb
    exact hT ⁅a, b⁆ (hKT (Subgroup.commutator_mem_commutator ha hb))
  have hc : ∀ a ∈ K, ∀ b ∈ K', ρ a * ρ b = ρ b * ρ a :=
    commute_of_scalar_commutators ρ K K' hK' hsc
  have hmem : n * k * n⁻¹ ∈ K' := by
    rw [hK'def]
    exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  have hconj : ρ (n * k * n⁻¹) ≠ 1 := by
    intro h
    apply hkne
    calc ρ k = ρ (n⁻¹ * (n * k * n⁻¹) * n) := congrArg (⇑ρ) (by group)
      _ = ρ n⁻¹ * ρ (n * k * n⁻¹) * ρ n := by simp only [map_mul]
      _ = 1 := by rw [h, mul_one, ← map_mul, inv_mul_cancel, map_one]
  exact no_commuting_perfect_pair hd3 ρ K K' hK hK' hc ⟨k, hk, hkne⟩ ⟨n * k * n⁻¹, hmem, hconj⟩

end Rep

end CoreIrreducible

end CFSG.RankThree.PartTwo.KFacts.NDC

end
