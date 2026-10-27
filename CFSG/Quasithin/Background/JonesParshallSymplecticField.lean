module

public import CFSG.Quasithin.Background.JonesParshallBasic
public import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
import CFSG.Quasithin.Background.JonesParshallWords

public section

namespace CFSG.Quasithin.JonesParshall

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Alternating
open LinearMap (BilinForm)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] def spNatA (B : BilinForm K V) : ↥(bilinIsometryGroup B) →* AddMonoid.End V where
  toFun g := ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V).toAddMonoidHom
  map_one' := rfl
  map_mul' _ _ := rfl

theorem spNatA_apply (B : BilinForm K V) (g : ↥(bilinIsometryGroup B)) (x : V) :
    spNatA B g x = ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x :=
  rfl

@[expose] def spTau {B : BilinForm K V} (hB : B.IsAlt) (v : V) : ↥(bilinIsometryGroup B) :=
  ⟨symplecticTransvection B hB v 1, symplecticTransvection_mem_bilinIsometryGroup hB v 1⟩

theorem spNatA_spTau {B : BilinForm K V} (hB : B.IsAlt) (v x : V) :
    spNatA B (spTau hB v) x = x + B x v • v := by
  rw [spNatA_apply]
  change (symplecticTransvection B hB v 1 : V →ₗ[K] V) x = _
  rw [symplecticTransvection_apply, one_mul]

theorem spTau_zero {B : BilinForm K V} (hB : B.IsAlt) : spTau hB (0 : V) = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro x
  change (symplecticTransvection B hB 0 1 : V →ₗ[K] V) x = x
  rw [symplecticTransvection_apply, smul_zero, add_zero]

theorem spTau_mul_self [CharP K 2] {B : BilinForm K V} (hB : B.IsAlt) (v : V) :
    spTau hB v * spTau hB v = 1 := by
  apply Subtype.ext
  change symplecticTransvection B hB v 1 * symplecticTransvection B hB v 1 = 1
  rw [symplecticTransvection_mul, CharTwo.add_self_eq_zero, symplecticTransvection_zero]

theorem spTau_comm {B : BilinForm K V} (hB : B.IsAlt) {v w : V} (hvw : B v w = 0) :
    spTau hB v * spTau hB w = spTau hB w * spTau hB v :=
  Subtype.ext (symplecticTransvection_comm hB hvw 1 1)

theorem Z1A_spTau_mem_span [CharP K 2] {B : BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {f : ↥(bilinIsometryGroup B) → V} (hf : f ∈ Z1A (spNatA B))
    (v : V) : f (spTau hB v) ∈ K ∙ v := by
  by_cases hv : v = 0
  · subst hv
    rw [spTau_zero, Z1A_one hf]
    exact Submodule.zero_mem _
  have h2V : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  have hzv : B (f (spTau hB v)) v = 0 := by
    have h := hf (spTau hB v) (spTau hB v)
    rw [spTau_mul_self, Z1A_one hf, spNatA_spTau, ← add_assoc, h2V, zero_add] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hv
  have hperp : ∀ w : V, B v w = 0 → B (f (spTau hB v)) w = 0 := by
    intro w hvw
    by_cases hwv : w ∈ K ∙ v
    · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hwv
      rw [map_smul, hzv, smul_zero]
    · have h1 := hf (spTau hB v) (spTau hB w)
      rw [spTau_comm hB hvw, hf (spTau hB w) (spTau hB v), spNatA_spTau, spNatA_spTau] at h1
      have h3 : f (spTau hB w) + f (spTau hB v) + B (f (spTau hB v)) w • w =
          f (spTau hB w) + f (spTau hB v) + B (f (spTau hB w)) v • v := by
        rw [add_assoc, h1]
        abel
      have h2 := add_left_cancel h3
      by_contra hne
      apply hwv
      rw [Submodule.mem_span_singleton]
      refine ⟨(B (f (spTau hB v)) w)⁻¹ * B (f (spTau hB w)) v, ?_⟩
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hne, one_smul]
  obtain ⟨u, hu⟩ : ∃ u, B v u = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, B v u ≠ 0 := by
      by_contra h
      exact hv (hnd.1 v fun u => not_not.mp fun hu => h ⟨u, hu⟩)
    exact ⟨(B v u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  have h0 : f (spTau hB v) - B (f (spTau hB v)) u • v = 0 := by
    apply hnd.1
    intro x
    have hw : B v (x - B v x • u) = 0 := by
      rw [map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]
    have h := hperp (x - B v x • u) hw
    simp only [map_sub, map_smul, smul_eq_mul] at h
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact h
  rw [sub_eq_zero.mp h0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem closure_spTau_eq_top {B : BilinForm K V} (hB : B.IsAlt) {s : Set V}
    (hs : Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' s) =
      bilinIsometryGroup B) :
    Subgroup.closure (spTau hB '' s) = ⊤ := by
  apply Subgroup.map_injective (bilinIsometryGroup B).subtype_injective
  have himg : (bilinIsometryGroup B).subtype '' (spTau hB '' s) =
      (fun x => symplecticTransvection B hB x 1) '' s := by
    rw [← Set.image_comp]
    rfl
  rw [MonoidHom.map_closure, himg, hs, Subgroup.map_top, Subgroup.range_subtype]

theorem card_Z1A_spNatA_le_pow [Finite K] [CharP K 2] [FiniteDimensional K V]
    {B : BilinForm K V} (hq : 2 < Nat.card K) (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Nat.card (Z1A (spNatA B)) ≤ Nat.card K ^ (Module.finrank K V + 1) := by
  obtain ⟨s, hs0, hscard, hsgen⟩ :=
    exists_card_le_closure_symplecticTransvection_eq hq hB hnd
  have hgen := closure_spTau_eq_top hB hsgen
  have : Finite V := Module.finite_of_finite K
  let ev : ↥(Z1A (spNatA B)) → ((i : s) → ↥(K ∙ (i : V))) := fun f i =>
    ⟨(f : ↥(bilinIsometryGroup B) → V) (spTau hB i), Z1A_spTau_mem_span hB hnd f.2 i⟩
  have hev : Function.Injective ev := by
    intro f f' hff'
    have hmem : (f : ↥(bilinIsometryGroup B) → V) - f' ∈ Z1A (spNatA B) := sub_mem f.2 f'.2
    have hvan : ∀ t ∈ spTau hB '' (s : Set V),
        ((f : ↥(bilinIsometryGroup B) → V) - f') t = 0 := by
      rintro _ ⟨i, hi, rfl⟩
      have h := congrArg Subtype.val (congrFun hff' ⟨i, hi⟩)
      rw [Pi.sub_apply, sub_eq_zero]
      exact h
    exact Subtype.ext (sub_eq_zero.mp (eq_zero_of_vanish_closure hmem hgen hvan))
  have hline : ∀ i : s, Nat.card ↥(K ∙ (i : V)) = Nat.card K := by
    intro i
    rw [Module.natCard_eq_pow_finrank (K := K), finrank_span_singleton (hs0 i i.2), pow_one]
  calc Nat.card (Z1A (spNatA B)) ≤ Nat.card ((i : s) → ↥(K ∙ (i : V))) :=
        Nat.card_le_card_of_injective ev hev
    _ = Nat.card K ^ s.card := by
        simp only [Nat.card_pi, hline, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    _ ≤ Nat.card K ^ (Module.finrank K V + 1) := Nat.pow_le_pow_right Nat.card_pos hscard

theorem coboundaryA_spNatA_injective {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Function.Injective (coboundaryA (spNatA B)) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra hm0
  obtain ⟨v, hv⟩ : ∃ v, B m v ≠ 0 := by
    by_contra h
    exact hm0 (hnd.1 m fun v => not_not.mp fun hv => h ⟨v, hv⟩)
  have h := congrFun hm (spTau hB v)
  rw [coboundaryA_apply, spNatA_spTau, add_sub_cancel_left, Pi.zero_apply] at h
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero (B m))
  exact hv ((smul_eq_zero.mp h).resolve_right hv0)

theorem card_B1A_spNatA {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Nat.card (B1A (spNatA B)) = Nat.card V :=
  (Nat.card_congr (AddMonoidHom.ofInjective (coboundaryA_spNatA_injective hB hnd)).toEquiv).symm

theorem card_Z1A_spNatA_le [Finite K] [CharP K 2] [FiniteDimensional K V]
    {B : BilinForm K V} (hq : 2 < Nat.card K) (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Nat.card (Z1A (spNatA B)) ≤ Nat.card K * Nat.card (B1A (spNatA B)) := by
  rw [card_B1A_spNatA hB hnd, Module.natCard_eq_pow_finrank (K := K) (V := V), ← pow_succ']
  exact card_Z1A_spNatA_le_pow hq hB hnd

theorem exists_card_Z1A_eq_mul_le {G M : Type*} [Group G] [AddCommGroup M] [Finite G] [Finite M]
    {μ : G →* AddMonoid.End M} {c : ℕ} (h : Nat.card (Z1A μ) ≤ c * Nat.card (B1A μ)) :
    ∃ k ≤ c, Nat.card (Z1A μ) = k * Nat.card (B1A μ) := by
  have hH : Nat.card ((B1A μ).addSubgroupOf (Z1A μ)) = Nat.card (B1A μ) :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (B1A_le_Z1A μ)).toEquiv
  have hidx := ((B1A μ).addSubgroupOf (Z1A μ)).index_mul_card
  rw [hH] at hidx
  refine ⟨((B1A μ).addSubgroupOf (Z1A μ)).index, ?_, hidx.symm⟩
  have : Finite (G → M) := Pi.finite
  have hpos : 0 < Nat.card (B1A μ) := Nat.card_pos
  rw [← hidx] at h
  exact Nat.le_of_mul_le_mul_right h hpos

end CFSG.Quasithin.JonesParshall

end
