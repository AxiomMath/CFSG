module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.PrimeSetCore
import CFSG.GroupTheory.Fitting.LayerTopBot

@[expose] public section

namespace CFSG.LayerAbelianSylow

private theorem perfect_hom_to_commutative_eq_one {Q : Type*} [Group Q] [Group.IsPerfect Q]
    {A : Type*} [CommGroup A] (f : Q →* A) : f = 1 := by
  rw [← MonoidHom.ker_eq_top_iff]
  refine eq_top_iff.mpr ?_
  rw [← (inferInstance : Group.IsPerfect Q).commutator_eq_top]
  exact Abelianization.commutator_subset_ker f

theorem center_eq_bot_and_three_dvd {X : Type} [Group X] [Finite X] (hO : pPrimeCore 3 X = ⊥)
    (hab : ∀ P : Sylow 3 X, ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {K : Subgroup X}
    (hK : IsComponent K) : Subgroup.center K = ⊥ ∧ 3 ∣ Nat.card K := by
  have hZle : (Subgroup.center K).map K.subtype ≤ pCore 3 X :=
    (LocalCores.center_component_le_center_layer hK).trans
      (WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot (G := X) 3 hO)
  have hZ3 : IsPGroup 3 (Subgroup.center K) :=
    (IsPGroup.to_le (CFSG.pCore_isPGroup (p := 3) (G := X)) hZle).of_equiv
      ((Subgroup.center K).equivMapOfInjective K.subtype K.subtype_injective).symm
  refine ⟨?_, ?_⟩
  ·
    refine (Subgroup.eq_bot_iff_forall (Subgroup.center K)).mpr fun z hz => ?_
    obtain ⟨P⟩ : Nonempty (Sylow 3 K) := inferInstance
    have hPmap : IsPGroup 3 ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
    obtain ⟨Q, hQ⟩ := hPmap.exists_le_sylow
    have hPcomm : IsMulCommutative P := by
      refine IsMulCommutative.of_comm fun a b => Subtype.ext (K.subtype_injective ?_)
      simp only [Subgroup.coe_mul, map_mul]
      exact hab Q (K.subtype a.1) (hQ (Subgroup.mem_map_of_mem K.subtype a.2))
        (K.subtype b.1) (hQ (Subgroup.mem_map_of_mem K.subtype b.2))
    let : CommGroup P := IsMulCommutative.instCommGroup
    have : Group.IsPerfect K := hK.1.1
    let T : K →* P := MonoidHom.transfer (MonoidHom.id P)
    have hT : T = 1 := perfect_hom_to_commutative_eq_one T
    have hkey : ∀ (k : ℕ) (g₀ : K),
        g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup K) → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
      intro k g₀ _
      have hc : Commute (z ^ k) g₀ :=
        (Commute.symm (show Commute g₀ z from Subgroup.mem_center_iff.mp hz g₀)).pow_left k
      rw [mul_assoc, hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    have hpow : z ^ (P : Subgroup K).index = 1 := by
      have hTz : T z = 1 := by rw [hT]; rfl
      rw [MonoidHom.transfer_eq_pow (MonoidHom.id P) z hkey] at hTz
      exact Subtype.ext_iff.mp hTz
    have horder_dvd : orderOf z ∣ (P : Subgroup K).index :=
      orderOf_dvd_iff_pow_eq_one.mpr hpow
    obtain ⟨n, hn⟩ := isPGroup_iff_orderOf_dvd_pow.mp hZ3 ⟨z, hz⟩
    have horder3 : orderOf z ∣ 3 ^ n := by
      rw [← Subgroup.orderOf_coe (⟨z, hz⟩ : Subgroup.center K)] at hn
      exact hn
    have hcop : Nat.Coprime (3 ^ n) (P : Subgroup K).index :=
      ((Fact.out : Nat.Prime 3).coprime_iff_not_dvd.mpr (Sylow.not_dvd_index P)).pow_left n
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop horder3 horder_dvd)
  ·
    by_contra h3
    set π : Set Nat.Primes := {q : Nat.Primes | q.val ≠ 3} with hπ
    have hKπ : IsPiSubgroup π K := fun q hq => by
      rw [hπ]
      exact fun hq3 => h3 (hq3 ▸ hq)
    have htopπ : IsPiSubgroup π (⊤ : Subgroup K) := fun q hq =>
      hKπ q (by rwa [Subgroup.card_top] at hq)
    have htop : (⊤ : Subgroup K) ≤ piCore π K :=
      LocalCores.le_piCore_of_normal (N := (⊤ : Subgroup K)) inferInstance htopπ
    have hcore : piCore π K = ⊤ := top_le_iff.mp htop
    have hmap_top : (⊤ : Subgroup K).map K.subtype = K := by
      rw [← MonoidHom.range_eq_map K.subtype, Subgroup.range_subtype]
    have hsub := LocalCores.prime_set_core_subnormal_intersection (G := X) π hK.2
    rw [hcore, hmap_top] at hsub
    have hKle : K ≤ piCore π X := by rw [hsub]; exact inf_le_right
    have hpi : piCore π X = pPrimeCore 3 X := by
      rw [hπ]
      exact (CFSG.pPrimeCore_eq_piCore (G := X) 3).symm
    rw [hpi] at hKle
    have hKbot : K = ⊥ := eq_bot_iff.mpr (hO ▸ hKle)
    have hnt : Nontrivial K := LocalCores.isQuasisimple_nontrivial hK.1
    exact (not_subsingleton_iff_nontrivial.mpr hnt) (by rw [hKbot]; infer_instance)

end CFSG.LayerAbelianSylow

end
