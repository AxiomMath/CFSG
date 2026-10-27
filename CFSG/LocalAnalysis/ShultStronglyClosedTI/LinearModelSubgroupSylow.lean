module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearSylowGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u v

section Generic

variable {G : Type v} [Group G]

theorem isCyclic_and_card_dvd_of_inf_eq_bot [Finite G] {B U T W : Subgroup G} (hUB : U ≤ B)
    [hUn : (U.subgroupOf B).Normal] (hTB : T ≤ B) (hsup : U ⊔ T = B) [IsCyclic T] (hWB : W ≤ B)
    (hWU : W ⊓ U = ⊥) : IsCyclic W ∧ Nat.card W ∣ Nat.card T := by
  let π := QuotientGroup.mk' (U.subgroupOf B)
  let φ : W →* B ⧸ U.subgroupOf B := π.comp (Subgroup.inclusion hWB)
  let ψ : T →* B ⧸ U.subgroupOf B := π.comp (Subgroup.inclusion hTB)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    have hwU : ((w : G)) ∈ U := by
      have h : Subgroup.inclusion hWB w ∈ U.subgroupOf B := (QuotientGroup.eq_one_iff _).mp hw
      exact h
    have h : (w : G) ∈ W ⊓ U := ⟨w.property, hwU⟩
    rw [hWU, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext h)
  have hψ : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro q _
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) q
    have hb : b ∈ U.subgroupOf B ⊔ T.subgroupOf B := by
      rw [← Subgroup.subgroupOf_sup hUB hTB, hsup, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top b
    have hle : U.subgroupOf B ⊔ T.subgroupOf B ≤ ψ.range.comap π := by
      refine sup_le (fun x hx => ?_) (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
      have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      change π x ∈ ψ.range
      rw [hx1]
      exact ψ.range.one_mem
    exact hle hb
  have hQ : IsCyclic (B ⧸ U.subgroupOf B) := isCyclic_of_surjective ψ hψ
  exact ⟨isCyclic_of_injective φ hφ, (Subgroup.card_dvd_of_injective φ hφ).trans
    (Subgroup.card_dvd_of_surjective (f := ψ) hψ)⟩

theorem le_sylow_of_le_normalizer {p : ℕ} (P : Sylow p G) {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hQN : Q ≤ Subgroup.normalizer (P : Set G)) : Q ≤ P := by
  have hsup := P.is_maximal' (hQ.to_sup_of_normal_right' P.isPGroup' hQN) le_sup_right
  exact hsup ▸ le_sup_left

end Generic

variable {K : Type u} [Field K] [Finite K]

theorem rootGroup_centralizer_eq {f : ℕ} (hcard : Nat.card K = 2 ^ f) {u : PSL2MatrixGroup K}
    (hu : u ∈ psl2UpperUnipotentSubgroup K) (hu1 : u ≠ 1) :
    Subgroup.centralizer ({u} : Set (PSL2MatrixGroup K)) = psl2UpperUnipotentSubgroup K := by
  let : CharP K 2 := charP_two_of_card hcard
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup hcard
  refine le_antisymm ?_ ?_
  swap
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (rootGroup_commute hx hu).eq
  intro c hc
  have hcomm : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcN : c ∈ psl2Borel K := by
    rw [← psl2UpperUnipotent_normalizer_eq_borel K]
    have huS : u ∈ S := by
      change u ∈ (S : Subgroup (PSL2MatrixGroup K)); rw [hS]; exact hu
    have hucS : u ∈ c • S := by
      change u ∈ (S : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj c).toMonoidHom
      refine Subgroup.mem_map.mpr ⟨u, huS, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcomm, mul_inv_cancel_right]
    have heq := TwoCoreGrowth.psl2_nonidentity_unique_sylow f hcard S (c • S) u hu1 huS hucS
    rw [← hS]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact heq.symm
  rw [psl2Borel_eq_map] at hcN
  obtain ⟨A, hA, rfl⟩ := hcN
  obtain ⟨b, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
  have hb : b ≠ 0 := by
    rintro rfl
    exact hu1 (by rw [sl2UpperUnipotent_zero, map_one])
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).mp hA
  have hconj := sl2Borel_conj_upperUnipotent hA b
  have hcomm' : A * sl2UpperUnipotent b = sl2UpperUnipotent b * A :=
    psl2QuotientMap_injective (K := K) (by rw [map_mul, map_mul]; exact hcomm)
  rw [hcomm', mul_assoc, mul_inv_cancel, mul_one] at hconj
  have hpar : A.val 0 0 ^ 2 * b = b := by
    have h := congrArg (fun B : SL(2, K) => B.val 0 1) hconj
    simpa [sl2UpperUnipotent] using h.symm
  have hsq : A.val 0 0 ^ 2 = 1 := by
    have h : (A.val 0 0 ^ 2 - 1) * b = 0 := by rw [sub_mul, hpar, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hb)
  have h00 : A.val 0 0 = 1 := CharTwo.sq_inj.mp (hsq.trans (one_pow 2).symm)
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rwa [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h
  have h11 : A.val 1 1 = 1 := by simpa [h00] using hdet
  refine (mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨A.val 0 1, ?_⟩
  congr 1
  apply Subtype.ext
  change A.val = !![1, A.val 0 1; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem exists_sylow_eq_conj_rootGroup {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (P : Sylow 2 (PSL2MatrixGroup K)) :
    ∃ g : PSL2MatrixGroup K, (P : Subgroup (PSL2MatrixGroup K)) =
      (psl2UpperUnipotentSubgroup K).map (MulAut.conj g).toMonoidHom := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2MatrixGroup K) S P
  refine ⟨g, ?_⟩
  rw [← hg, ← hS]
  rfl

theorem sylow_centralizer_eq {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (P : Sylow 2 (PSL2MatrixGroup K)) {u : PSL2MatrixGroup K} (hu : u ∈ P) (hu1 : u ≠ 1) :
    Subgroup.centralizer ({u} : Set (PSL2MatrixGroup K)) = P := by
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_rootGroup hcard P
  have hu' : u ∈ (psl2UpperUnipotentSubgroup K).map (MulAut.conj g).toMonoidHom := hg ▸ hu
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu'
  have hu₀1 : u₀ ≠ 1 := by
    rintro rfl
    exact hu1 (map_one _)
  rw [hg, ← rootGroup_centralizer_eq hcard hu₀ hu₀1]
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map_equiv,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g⁻¹ * x * g * u₀ = g⁻¹ * (x * (g * u₀ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u₀ * g⁻¹) * x) * g := by rw [h]
      _ = u₀ * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * u₀ * g⁻¹) = g * (g⁻¹ * x * g * u₀) * g⁻¹ := by group
      _ = g * (u₀ * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * u₀ * g⁻¹ * x := by group

theorem sylow_normalizer_complement_cyclic {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (P : Sylow 2 (PSL2MatrixGroup K)) {W : Subgroup (PSL2MatrixGroup K)}
    (hWN : W ≤ Subgroup.normalizer (P : Set (PSL2MatrixGroup K)))
    (hWP : W ⊓ (P : Subgroup (PSL2MatrixGroup K)) = ⊥) :
    IsCyclic W ∧ Nat.card W ∣ Nat.card K - 1 := by
  let : CharP K 2 := charP_two_of_card hcard
  let : IsCyclic (torus K) := torus_isCyclic
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_rootGroup hcard P
  let e : PSL2MatrixGroup K ≃* PSL2MatrixGroup K := MulAut.conj g
  let W' := W.map e.symm.toMonoidHom
  have hN : Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) =
      (psl2Borel K).map e.toMonoidHom := by
    change Subgroup.normalizer ((P : Subgroup (PSL2MatrixGroup K)) : Set (PSL2MatrixGroup K)) = _
    rw [hg, ← Subgroup.map_normalizer_eq_of_bijective _ e.bijective,
      psl2UpperUnipotent_normalizer_eq_borel]
  have hW'B : W' ≤ psl2Borel K := by
    intro x hx
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hx
    have h := hWN hx
    rw [hN, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h
    exact h
  have hW'U : W' ⊓ psl2UpperUnipotentSubgroup K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxU⟩ := Subgroup.mem_inf.mp hx
    change x ∈ W.map e.symm.toMonoidHom at hxW
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hxW
    have hxP : e x ∈ (P : Subgroup (PSL2MatrixGroup K)) := by
      rw [hg]
      exact Subgroup.mem_map_of_mem _ hxU
    have h : e x ∈ W ⊓ (P : Subgroup (PSL2MatrixGroup K)) := ⟨hxW, hxP⟩
    rw [hWP, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h
    exact Subgroup.mem_bot.mpr h
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_inf_eq_bot (hUn := psl2UpperUnipotent_normal_in_borel)
    psl2UpperUnipotent_le_borel torus_le_borel rootGroup_sup_torus hW'B hW'U
  let c : W ≃* W' := W.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  refine ⟨c.isCyclic.mpr hcyc, ?_⟩
  rw [Nat.card_congr c.toEquiv, ← card_torus]
  exact hdvd

theorem odd_card_sylow_normalizer_inf {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (P Q : Sylow 2 (PSL2MatrixGroup K)) (hPQ : P ≠ Q) :
    Odd (Nat.card (Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) ⊓
      Subgroup.normalizer (Q : Set (PSL2MatrixGroup K)) : Subgroup (PSL2MatrixGroup K))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  have hxorder : orderOf (x : PSL2MatrixGroup K) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hzp : IsPGroup 2 (Subgroup.zpowers (x : PSL2MatrixGroup K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxorder, pow_one])
  have hxP : (x : PSL2MatrixGroup K) ∈ P :=
    le_sylow_of_le_normalizer P hzp (Subgroup.zpowers_le_of_mem x.property.1)
      (Subgroup.mem_zpowers _)
  have hxQ : (x : PSL2MatrixGroup K) ∈ Q :=
    le_sylow_of_le_normalizer Q hzp (Subgroup.zpowers_le_of_mem x.property.2)
      (Subgroup.mem_zpowers _)
  have hx1 : (x : PSL2MatrixGroup K) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxorder
    exact absurd hxorder (by norm_num)
  exact hPQ (Sylow.ext
    (TwoCoreGrowth.psl2_nonidentity_unique_sylow f hcard P Q _ hx1 hxP hxQ))

end CFSG.ShultStronglyClosedTI.LinearModel
