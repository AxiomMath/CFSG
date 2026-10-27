module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Aut
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Subgroup Matrix

theorem uc22pwI3_exists_cover {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ}
    (hn : 2 < n) (h : IsL3 (X ⧸ Subgroup.center X) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (α : SpecialLinearGroup (Fin 3) K →* X), Nat.card K = 2 ^ n ∧ Function.Surjective α ∧
        α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  haveI : CharP F 2 := uc22pwlie_charP_two (n := n) hF
  have hk : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨α, hα, hαc⟩ := uc22pwlie_exists_slCover (m := 2) (by norm_num) hk hq e
  exact ⟨F, inferInstance, inferInstance, inferInstance, α, hF, hα, hαc⟩

theorem uc22pwI3_exists_cover_sylow {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    {n : ℕ} (hn : 2 < n) (h : IsL3 (X ⧸ Subgroup.center X) n) (U : Sylow 2 X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (α : SpecialLinearGroup (Fin 3) K →* X), Nat.card K = 2 ^ n ∧ Function.Surjective α ∧
        α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) ∧
        (unitriangular 3 K).map α = (U : Subgroup X) := by
  obtain ⟨K, _, _, _, α, hK, hα, hαc⟩ := uc22pwI3_exists_cover hq hn h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Q.mapSurjective hα) U
  refine ⟨K, inferInstance, inferInstance, inferInstance, (MulAut.conj g : X →* X).comp α, hK,
    (MulAut.conj g).surjective.comp hα, ?_, ?_⟩
  · intro s hs
    apply hαc
    have h1 : (MulAut.conj g) (α s) = 1 := hs
    rw [MonoidHom.mem_ker]
    simpa using h1
  · rw [← Subgroup.map_map, ← hQ, ← Sylow.coe_mapSurjective hα, ← coe_sylow_smul, hg]

theorem uc22pwI3_lift {K : Type} [Field K] [Finite K] [CharP K 2] {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hK : 5 ≤ Nat.card K) (α : SpecialLinearGroup (Fin 3) K →* X)
    (hα : Function.Surjective α) (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    (φ : MulAut X)
    (hφ : ∀ x, x ∈ (unitriangular 3 K).map α ↔ φ x ∈ (unitriangular 3 K).map α) :
    ∃ ν : MulAut (SpecialLinearGroup (Fin 3) K), (∀ s, α (ν s) = φ (α s)) ∧
      ∀ s, s ∈ unitriangular 3 K ↔ ν s ∈ unitriangular 3 K := by
  have hρ : Function.Surjective (φ.toMonoidHom.comp α) := φ.surjective.comp hα
  have hρc : (φ.toMonoidHom.comp α).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro s hs
    apply hαc
    have h1 : φ (α s) = 1 := hs
    rw [MonoidHom.mem_ker]
    exact (map_eq_one_iff φ φ.injective).1 h1
  obtain ⟨α', hα'sur, -, hα'⟩ := uc22pwlie_exists_cover_of_closed
    (fun E _ π hπ hc => CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
      (m := 2) (by norm_num) hK hπ hc)
    (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := K) (n := 3) (by norm_num))
    α hα hαc _ hρ hρc
  have hbij : Function.Bijective α' := ⟨Finite.injective_iff_surjective.mpr hα'sur, hα'sur⟩
  let ν : MulAut (SpecialLinearGroup (Fin 3) K) := MulEquiv.ofBijective α' hbij
  have hνα : ∀ s, α (ν s) = φ (α s) := fun s => hα' s
  have hU₀ : IsPGroup 2 (unitriangular 3 K) := by
    obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
    rw [← hQ]
    exact Q.isPGroup'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU₀
  have hpow : ∀ s ∈ unitriangular 3 K, s ^ 2 ^ k = 1 := by
    intro s hs
    have h1 := pow_card_eq_one' (G := unitriangular 3 K) (x := (⟨s, hs⟩ : unitriangular 3 K))
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have hmap : ∀ s ∈ unitriangular 3 K, ν s ∈ unitriangular 3 K := by
    intro s hs
    obtain ⟨u₀, hu₀, hu₀eq⟩ := (hφ _).1 (⟨s, hs, rfl⟩ : α s ∈ (unitriangular 3 K).map α)
    have hzker : u₀⁻¹ * ν s ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu₀eq, hνα, inv_mul_cancel]
    have hzc := hαc hzker
    have e : ν s = u₀ * (u₀⁻¹ * ν s) := by group
    have hN1 : (ν s) ^ 2 ^ k = 1 := by
      rw [← map_pow, hpow s hs, map_one]
    have hz1 : (u₀⁻¹ * ν s) ^ 2 ^ k = 1 := by
      have h2 : (ν s) ^ 2 ^ k = u₀ ^ 2 ^ k * (u₀⁻¹ * ν s) ^ 2 ^ k := by
        conv_lhs => rw [e]
        exact (Commute.mul_pow (Subgroup.mem_center_iff.1 hzc u₀) _)
      rw [hN1, hpow u₀ hu₀, one_mul] at h2
      exact h2.symm
    have hz3 := uc22pwI3_center_pow_three hzc
    have hord : orderOf (u₀⁻¹ * ν s) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz1) (orderOf_dvd_of_pow_eq_one hz3)
    have hgcd : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hgcd] at hord
    have hz : u₀⁻¹ * ν s = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
    rw [hz, mul_one] at e
    rw [e]
    exact hu₀
  refine ⟨ν, hνα, fun s => ⟨hmap s, fun hs => ?_⟩⟩
  have hle : (unitriangular 3 K).map ν.toMonoidHom ≤ unitriangular 3 K := by
    rintro _ ⟨t, ht, rfl⟩
    exact hmap t ht
  have heq : (unitriangular 3 K).map ν.toMonoidHom = unitriangular 3 K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (f := ν.toMonoidHom) ν.injective])
  rw [← heq] at hs
  obtain ⟨t, ht, hts⟩ := hs
  have : t = s := ν.injective hts
  rw [← this]
  exact ht

theorem uc22pwI3_pf {K : Type} [Field K] [Finite K] [CharP K 2] {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hK : 5 ≤ Nat.card K) (α : SpecialLinearGroup (Fin 3) K →* X)
    (hα : Function.Surjective α) (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    (φ : MulAut X)
    (hφ : ∀ x, x ∈ (unitriangular 3 K).map α ↔ φ x ∈ (unitriangular 3 K).map α) :
    ∃ i : ℕ, ∀ a : Kˣ, φ (α (uc22pwI3dSL K a)) * (α (uc22pwI3dSL K (a ^ 2 ^ i)))⁻¹ ∈
      (unitriangular 3 K).map α := by
  obtain ⟨ν, hνα, hν⟩ := uc22pwI3_lift hq hK α hα hαc φ hφ
  obtain ⟨i, hi⟩ := uc22pwI3_key ν hν
  refine ⟨i, fun a => ⟨_, hi a, ?_⟩⟩
  rw [map_mul, map_inv, hνα]

end CFSG.LocalAnalysis.UniquenessCase.UC22
