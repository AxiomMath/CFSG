module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUHeart
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private theorem ggQTUo_scalar_eq_diagHom {K : Type} [Field K] {n : ℕ} (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c = diagHom n (fun _ => c) :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply])

theorem ggQTwoXInLU_onto {N : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hN3 : ¬ 3 ∣ N)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K) {b : G} (hb : b ∈ Bs) :
    ∃ (s : ↥(unitarySU 2 1 K N)) (t : Fin N → Kˣ),
      (s : GL (Fin N) K) = diagHom N t ∧ F.φ s = b := by
  let P : Kˣ := ∏ i, F.δ b i
  have hcard : Nat.card K = 4 := by
    rw [F.field.card]
    norm_num
  have hcard_units : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hcard]
  have hcop : Nat.Coprime N 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3).symm
  have hcop' : Nat.Coprime 3 N := Nat.coprime_comm.mpr hcop
  have hcop'' : Nat.Coprime (Nat.card Kˣ) N := by
    rw [hcard_units]
    exact hcop'
  have hbij : Function.Bijective (fun x : Kˣ => x ^ N) :=
    Nat.Coprime.pow_left_bijective (n := N) (G := Kˣ) hcop''
  obtain ⟨c, hc⟩ := hbij.surjective P⁻¹
  let t : Fin N → Kˣ := fun i => c * F.δ b i
  have hprod : ∏ i, t i = 1 := by
    simp only [t]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change c ^ N * P = 1
    change c ^ N = P⁻¹ at hc
    rw [hc, inv_mul_cancel]
  have ht3 : ∀ i, t i ^ 3 = 1 := by
    intro i
    have hc3 : c ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := c)
      rwa [hcard_units] at h
    have hd3 : (F.δ b i) ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := F.δ b i)
      rwa [hcard_units] at h
    simp only [t]
    rw [mul_pow, hc3, hd3, mul_one]
  have hs_mem : diagHom N t ∈ unitarySU 2 1 K N := by
    rw [mem_unitarySU_iff F.field]
    refine ⟨?_, ?_⟩
    · rw [det_diagHom, ← Units.coe_prod, hprod, Units.val_one]
    · rw [coe_diagHom, Matrix.diagonal_map (map_zero F.field.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [F.field.bar_apply, show 2 ^ 1 = 2 by norm_num, ← pow_succ, ← Units.val_pow_eq_pow_val,
        ht3 i, Units.val_one]
  let s : ↥(unitarySU 2 1 K N) := ⟨diagHom N t, hs_mem⟩
  have hφs_bs : F.φ s ∈ Bs := ggQTwoXInLU_heart hS F s t rfl
  have hg_bs : b⁻¹ * F.φ s ∈ Bs :=
    Subgroup.mul_mem Bs (Subgroup.inv_mem Bs hb) hφs_bs
  have hg_cent : b⁻¹ * F.φ s ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← F.range_eq] at hy
    obtain ⟨u, hu⟩ := hy
    rw [← hu]
    have hpair := F.pair b hb
    rw [SUTorus.mem_suPairs] at hpair
    let B : GL (Fin N) K := diagHom N (F.δ b)
    let v : ↥(unitarySU 2 1 K N) := ⟨B * (u : GL (Fin N) K) * B⁻¹, (hpair.1 u).mp u.2⟩
    have hv : (v : GL (Fin N) K) = B * (u : GL (Fin N) K) * B⁻¹ := rfl
    have hb_act : b * F.φ u * b⁻¹ = F.φ v := hpair.2 u v hv
    have hsB : (s : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) c * B := by
      change diagHom N t = Matrix.GeneralLinearGroup.scalar (Fin N) c * B
      have ht_eq : t = (fun _ : Fin N => c) * F.δ b := by
        funext i
        rfl
      rw [ht_eq, map_mul, ← ggQTUo_scalar_eq_diagHom]
    have hscalar_comm : ∀ x : GL (Fin N) K,
        x * Matrix.GeneralLinearGroup.scalar (Fin N) c =
          Matrix.GeneralLinearGroup.scalar (Fin N) c * x := by
      intro x
      exact (commute_scalar c x).eq
    have hconj : F.φ s * F.φ u * (F.φ s)⁻¹ = F.φ v := by
      calc F.φ s * F.φ u * (F.φ s)⁻¹
          = F.φ (s * u) * (F.φ s)⁻¹ := by rw [← map_mul]
        _ = F.φ (s * u) * F.φ s⁻¹ := by rw [← map_inv]
        _ = F.φ (s * u * s⁻¹) := by rw [← map_mul]
        _ = F.φ v := by
          congr 1
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hsB]
          calc (Matrix.GeneralLinearGroup.scalar (Fin N) c * B) * (u : GL (Fin N) K) *
                (Matrix.GeneralLinearGroup.scalar (Fin N) c * B)⁻¹
              = Matrix.GeneralLinearGroup.scalar (Fin N) c *
                  (B * (u : GL (Fin N) K) * B⁻¹) *
                    (Matrix.GeneralLinearGroup.scalar (Fin N) c)⁻¹ := by group
            _ = (B * (u : GL (Fin N) K) * B⁻¹) *
                  Matrix.GeneralLinearGroup.scalar (Fin N) c *
                    (Matrix.GeneralLinearGroup.scalar (Fin N) c)⁻¹ := by
                  rw [hscalar_comm (B * (u : GL (Fin N) K) * B⁻¹)]
            _ = B * (u : GL (Fin N) K) * B⁻¹ := by group
    have hcomm_u : (b⁻¹ * F.φ s) * F.φ u = F.φ u * (b⁻¹ * F.φ s) := by
      calc (b⁻¹ * F.φ s) * F.φ u
          = b⁻¹ * (F.φ s * F.φ u * (F.φ s)⁻¹) * F.φ s := by group
        _ = b⁻¹ * (b * F.φ u * b⁻¹) * F.φ s := by rw [hconj, hb_act]
        _ = F.φ u * (b⁻¹ * F.φ s) := by group
    exact hcomm_u.symm
  have hg_inf : b⁻¹ * F.φ s ∈ Bs ⊓ Subgroup.centralizer (ggG0 3 B x L D J : Set G) :=
    Subgroup.mem_inf.mpr ⟨hg_bs, hg_cent⟩
  have hbot : Bs ⊓ Subgroup.centralizer (ggG0 3 B x L D J : Set G) = ⊥ :=
    bstar_inf_centralizer_ggG0_eq_bot hS.1.1
  have hg_one : b⁻¹ * F.φ s = 1 := by
    rw [hbot] at hg_inf
    simpa using hg_inf
  have hφs_eq_b : F.φ s = b := by
    have h := congrArg (fun x => b * x) hg_one
    simpa using h
  exact ⟨s, t, rfl, hφs_eq_b⟩

end CFSG.StandardType

end
