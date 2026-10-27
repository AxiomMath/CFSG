module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdBorelGeneric
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieL3
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOB

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem inner_of_prime_L3 {X : Type} [Group X] [Finite X] {m r : ℕ} (hX : IsL3 X m)
    (hr : r.Prime) (hrm : ¬ r ∣ 6 * m) {α : MulAut X} (hα : α ^ r = 1) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  have h := CFSG.Quasithin.A318P.outer_dvd_linear
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  refine uc22p2214_out_mem_of_card_dvd (m := 6 * m) ?_ hr hrm hα
  refine h.trans ?_
  calc 2 * m * Nat.gcd 3 (2 ^ m - 1) ∣ 2 * m * 3 := Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left _ _)
    _ = 6 * m := by ring

private theorem pow_mem_projUnitriangular_of_mem_projUpperTriangular {K : Type} [Field K]
    [Finite K] {n : ℕ} {c : projectiveSL n K} (hc : c ∈ projUpperTriangular n K) :
    c ^ (Nat.card K - 1) ∈ projUnitriangular n K := by
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hc
  rw [← map_pow]
  exact Subgroup.mem_map_of_mem (proj n K)
    (CFSG.Quasithin.H13.FiveNorm.LieL3.pow_card_sub_one_mem_unitriangular hA)

private theorem pow_mem_of_mem_normalizer_projectiveSL {K : Type} [Field K] [Finite K] [CharP K 2]
    (U : Sylow 2 (projectiveSL 3 K)) {b : projectiveSL 3 K}
    (hb : b ∈ Subgroup.normalizer ((U : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K))) :
    b ^ (Nat.card K - 1) ∈ (U : Subgroup (projectiveSL 3 K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := CFSG.SeitzReduction.LinearPilot.exists_conj_projUnitriangular
    (n := 3) (K := K) (by norm_num) U
  have hb' : ∀ h : projectiveSL 3 K, h ∈ (U : Subgroup (projectiveSL 3 K)) ↔
      b * h * b⁻¹ ∈ (U : Subgroup (projectiveSL 3 K)) :=
    Subgroup.mem_normalizer_iff.mp hb
  have hcN : g⁻¹ * b * g ∈
      Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have k1 : g⁻¹ * (b * (g * h * g⁻¹) * b⁻¹) * g = g⁻¹ * b * g * h * (g⁻¹ * b * g)⁻¹ := by
      group
    have k2 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    show h ∈ projUnitriangular 3 K ↔ g⁻¹ * b * g * h * (g⁻¹ * b * g)⁻¹ ∈ projUnitriangular 3 K
    rw [← k1, ← hg, ← hb', hg, k2]
  rw [normalizer_projUnitriangular 2] at hcN
  have hpow := pow_mem_projUnitriangular_of_mem_projUpperTriangular hcN
  have hconj : ∀ k : ℕ, g⁻¹ * b ^ k * g = (g⁻¹ * b * g) ^ k := by
    intro k
    have := conj_pow (a := g⁻¹) (b := b) (i := k)
    rw [inv_inv] at this
    exact this.symm
  rw [hg, hconj]
  exact hpow

theorem pow_mem_of_mem_normalizer_L3 {X : Type} [Group X] [Finite X] {m : ℕ} (hX : IsL3 X m)
    (S : Sylow 2 X) {b : X} (hb : b ∈ Subgroup.normalizer ((S : Subgroup X) : Set X)) :
    b ^ (2 ^ m - 1) ∈ (S : Subgroup X) := by
  have hL : CFSG.Blueprint.LieModel X .PSL 3 2 m := hX
  obtain ⟨hadm, K, hF, hFin, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
  have hm : 1 ≤ m := hadm.2.1
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm hK
  let eP : X ≃* projectiveSL 3 K :=
    e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K)
  let U : Sylow 2 (projectiveSL 3 K) := Sylow.mapSurjective (f := eP.toMonoidHom) eP.surjective S
  have hUsub : (U : Subgroup (projectiveSL 3 K)) = (S : Subgroup X).map eP.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eP.toMonoidHom) eP.surjective S
  have hbP : eP b ∈ Subgroup.normalizer ((U : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) := by
    rw [hUsub, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hb
  have hpow := pow_mem_of_mem_normalizer_projectiveSL U hbP
  have hpow' : eP (b ^ (Nat.card K - 1)) ∈ (S : Subgroup X).map eP.toMonoidHom := by
    rw [map_pow, ← hUsub]
    exact hpow
  have hfin : b ^ (Nat.card K - 1) ∈ (S : Subgroup X) := by
    have h := (Subgroup.mem_map_equiv (f := eP)).1 hpow'
    rwa [MulEquiv.symm_apply_apply] at h
  rw [← hK]
  exact hfin

theorem kob_L3 {Y : Type} [Group Y] [Finite Y] {n r : ℕ} (hX : IsL3 Y n)
    (hZ : Subgroup.center Y = ⊥) (hr : r.Prime) (hr2 : r ≠ 2) (hrn : ¬ r ∣ 6 * n)
    (hrq : ¬ r ∣ 2 ^ n - 1) (S : Sylow 2 Y) {θ : MulAut Y} (hθ : θ ^ r = 1)
    (hS : ∀ x ∈ (S : Subgroup Y), θ x ∈ (S : Subgroup Y)) : θ = 1 :=
  eq_one_of_inner_of_noR hZ S
    (noR_of_pow_mem hr hr2 ((Nat.Prime.coprime_iff_not_dvd hr).2 hrq) S
      fun _ hb => pow_mem_of_mem_normalizer_L3 hX S hb)
    (inner_of_prime_L3 hX hr hrn hθ) hθ hS

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOB

end
