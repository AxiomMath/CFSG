module

public import CFSG.LieType.SteinbergBRSuzukiNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.RankThree.S4Free.Basic

public section

namespace CFSG.RankThree.S4Free

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.SteinbergBR Subgroup
open scoped LinearAlgebra.Projectivization

namespace Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K] {X : Type*} [Group X]

theorem suzukiB_le_normalizer_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
  sup_le le_normalizer (suzuki_borel_structure hK).2.2.2.1

theorem exists_mem_sylow_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    (S : Sylow 2 X) :
    ∃ g : suzukiGroup a K, ∀ x : X, x ∈ (S : Subgroup X) ↔ g⁻¹ * e x * g ∈ suzukiU a K := by
  have hUX : IsPGroup 2 ((suzukiU a K).comap e.toMonoidHom) :=
    (isPGroup_suzukiU hK).comap_of_injective e.toMonoidHom e.injective
  have hidx : ¬ 2 ∣ ((suzukiU a K).comap e.toMonoidHom).index := by
    rw [index_comap_of_surjective _ e.surjective]
    exact not_two_dvd_index_suzukiU hK
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨x₀, hx₀⟩ := MulAction.exists_smul_eq X (hUX.toSylow hidx) S
  refine ⟨e x₀, fun x => ?_⟩
  rw [← hx₀, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, hUX.toSylow_coe hidx]
  change (MulAut.conj x₀)⁻¹ x ∈ (suzukiU a K).comap e.toMonoidHom ↔ _
  rw [MulAut.inv_apply, MulAut.conj_symm_apply, mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]

theorem sylow_ne_bot (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    {S : Subgroup X} {g : suzukiGroup a K}
    (hS : ∀ x : X, x ∈ S ↔ g⁻¹ * e x * g ∈ suzukiU a K) : S ≠ ⊥ := by
  intro hbot
  have hU : suzukiU a K ≠ ⊥ := by
    intro h
    have hcard := (suzuki_unipotent_structure hK).2.1
    rw [h, card_bot] at hcard
    have : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
    nlinarith
  obtain ⟨u, hu, hu1⟩ := (suzukiU a K).bot_or_exists_ne_one.resolve_left hU
  have hmem : e.symm (g * u * g⁻¹) ∈ S := by
    rw [hS, MulEquiv.apply_symm_apply]
    simpa [mul_assoc] using hu
  rw [hbot, mem_bot, MulEquiv.map_eq_one_iff] at hmem
  apply hu1
  calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
    _ = 1 := by rw [hmem]; group

theorem conj_mem_suzukiB_of_mem_normalizer (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) {S : Subgroup X} {g : suzukiGroup a K}
    (hS : ∀ x ∈ S, g⁻¹ * e x * g ∈ suzukiU a K) {P : Subgroup X} (hPS : P ≤ S) (hP : P ≠ ⊥)
    {n : X} (hn : n ∈ normalizer (P : Set X)) : g⁻¹ * e n * g ∈ suzukiB a K := by
  obtain ⟨x, hxP, hx1⟩ := P.bot_or_exists_ne_one.resolve_left hP
  have hω : g • suzukiInfty K ∈ suzukiOmega a K :=
    suzuki_smul_mem_suzukiOmega hK g (suzukiInfty_mem_suzukiOmega a K)
  have hfix : e n • g • suzukiInfty K = g • suzukiInfty K := by
    by_contra hne
    have hx' : n⁻¹ * x * n ∈ P := by
      have := (mem_normalizer_iff.1 (inv_mem hn) x).1 hxP
      rwa [inv_inv] at this
    have h1 := smul_eq_of_mem_conj_suzukiU hK (hS _ (hPS hx'))
    refine smul_ne_of_mem_conj_suzukiU hK (hS x (hPS hxP)) (by simpa using hx1)
      (suzuki_smul_mem_suzukiOmega hK (e n) hω) hne ?_
    rw [map_mul, map_mul, map_inv] at h1
    have key : ∀ y : ℙ K (Fin 4 → K), e x • e n • y = e n • ((e n)⁻¹ * e x * e n) • y := by
      intro y
      rw [smul_smul, smul_smul]
      congr 1
      group
    rw [key, h1]
  rw [← (suzuki_ovoid_stabilizer hK).1, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hfix,
    inv_smul_smul]

theorem mem_normalizer_of_conj_mem_suzukiB (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) {S : Subgroup X} {g : suzukiGroup a K}
    (hS : ∀ x : X, x ∈ S ↔ g⁻¹ * e x * g ∈ suzukiU a K) {n : X}
    (hn : g⁻¹ * e n * g ∈ suzukiB a K) : n ∈ normalizer (S : Set X) := by
  refine mem_normalizer_iff.2 fun h => ?_
  have hconj : g⁻¹ * e (n * h * n⁻¹) * g =
      (g⁻¹ * e n * g) * (g⁻¹ * e h * g) * (g⁻¹ * e n * g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    group
  rw [hS, hS, hconj]
  exact mem_normalizer_iff.1 (suzukiB_le_normalizer_suzukiU hK hn) _

theorem normalizer_eq_map_suzukiB (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) {S : Subgroup X} {g : suzukiGroup a K}
    (hS : ∀ x : X, x ∈ S ↔ g⁻¹ * e x * g ∈ suzukiU a K) :
    normalizer (S : Set X) = (suzukiB a K).map ((MulAut.conj g).trans e.symm).toMonoidHom := by
  ext n
  rw [mem_map_equiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulAut.conj_symm_apply]
  exact ⟨fun hn => conj_mem_suzukiB_of_mem_normalizer hK e (fun x hx => (hS x).1 hx) le_rfl
    (sylow_ne_bot hK e hS) hn, mem_normalizer_of_conj_mem_suzukiB hK e hS⟩

theorem normalizer_le_normalizer_sylow (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) {P : Subgroup X} (hPS : P ≤ S) (hP : P ≠ ⊥) :
    normalizer (P : Set X) ≤ normalizer ((S : Subgroup X) : Set X) := by
  obtain ⟨g, hS⟩ := exists_mem_sylow_iff hK e S
  exact fun n hn => mem_normalizer_of_conj_mem_suzukiB hK e hS
    (conj_mem_suzukiB_of_mem_normalizer hK e (fun x hx => (hS x).1 hx) hPS hP hn)

theorem card_normalizer_sylow (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    (S : Sylow 2 X) :
    Nat.card (normalizer ((S : Subgroup X) : Set X)) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  obtain ⟨g, hS⟩ := exists_mem_sylow_iff hK e S
  rw [normalizer_eq_map_suzukiB hK e hS, card_map_of_injective (MulEquiv.injective _),
    (suzuki_borel_structure hK).2.2.2.2.2.2.2]

theorem normalizer_sylow_ne_top (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K)
    (S : Sylow 2 X) : normalizer ((S : Subgroup X) : Set X) ≠ ⊤ := by
  intro htop
  have h := card_normalizer_sylow hK e S
  rw [htop, card_top, Nat.card_congr e.toEquiv, suzuki_order hK] at h
  have hq : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  have hpos : 0 < (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
    Nat.mul_pos (by positivity) (by omega)
  have h2 : (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * 1 =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [mul_one, h]
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  nlinarith

theorem oTwo_eq_bot (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a K) :
    oTwo X = ⊥ := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  by_contra hne
  have hQ : IsPGroup 2 (oTwo X) :=
    CFSG.isPGroup_of_isPiSubgroup_singleton (CFSG.LocalCores.piCore_isPiSubgroup _)
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  refine normalizer_sylow_ne_top hK e S (eq_top_iff.2 ?_)
  rw [← normalizer_eq_top_iff.2 (inferInstance : (oTwo X).Normal)]
  exact normalizer_le_normalizer_sylow hK e S hQS hne

end Suzuki

open Suzuki

end CFSG.RankThree.S4Free
