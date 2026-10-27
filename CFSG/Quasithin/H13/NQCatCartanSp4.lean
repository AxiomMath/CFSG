module

public import CFSG.Quasithin.H13.NQCatCartanBasic
public import CFSG.Quasithin.Vol2.F134LieSp4

public section

namespace CFSG.Quasithin.H13.NQCat.CartanSp4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauEquiv tauMat_apply tauPair tauAut
  tauAut_proj tauAut_mul_self frobAut)

variable {K : Type} [Field K]

theorem fieldSp_torusHom (σ : K ≃+* K) (t : Fin 2 → Kˣ) :
    fieldSp 2 K σ (SymplecticTorusWeyl.torusHom t) =
      SymplecticTorusWeyl.torusHom (fun j => Units.map σ.toRingHom.toMonoidHom (t j)) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp, SymplecticTorusWeyl.coe_torusHom, SymplecticTorusWeyl.coe_torusHom,
    diagonal_map (map_zero σ)]
  congr 1
  funext x
  rcases x with x | x <;> simp

theorem tauSp_torusHom [CharP K 2] (t : Fin 2 → Kˣ) :
    tauSp (SymplecticTorusWeyl.torusHom t) =
      SymplecticTorusWeyl.torusHom ![t 0 * t 1, t 0 * (t 1)⁻¹] := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp, SymplecticTorusWeyl.coe_torusHom, SymplecticTorusWeyl.coe_torusHom]
  ext r c
  rw [tauMat_apply]
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [tauPair, mul_comm]

theorem diagHom_torusHom (t : Fin 2 → Kˣ) :
    diagHom 2 K ⟨SymplecticTorusWeyl.torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ = t := by
  funext i
  apply Units.ext
  simp [diagHom, diagEntry, SymplecticTorusWeyl.coe_torusHom]

theorem eq_of_mem_unipotent {b : StatedSp 2 K} (hb : b ∈ borelSubgroup 2 K) {s t : Fin 2 → Kˣ}
    (h : b * SymplecticTorusWeyl.torusHom s * b⁻¹ * (SymplecticTorusWeyl.torusHom t)⁻¹ ∈
      unipotent 2 K) : s = t := by
  have hw : (⟨b, hb⟩ * ⟨_, torus_le_borelSubgroup ⟨s, rfl⟩⟩ * (⟨b, hb⟩ : borelSubgroup 2 K)⁻¹ *
      (⟨_, torus_le_borelSubgroup ⟨t, rfl⟩⟩ : borelSubgroup 2 K)⁻¹ : borelSubgroup 2 K) ∈
      (diagHom 2 K).ker := by
    rw [ker_diagHom, Subgroup.mem_subgroupOf]
    exact h
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, diagHom_torusHom,
    diagHom_torusHom, mul_comm (diagHom 2 K ⟨b, hb⟩) s, mul_assoc s, mul_inv_cancel, mul_one,
    mul_inv_eq_one] at hw
  exact hw

variable [Finite K] [CharP K 2]

theorem map_projUnipotent_tauAut :
    (projUnipotent 2 K).map (tauAut : MulAut (StatedProj (StatedSp 2 K))).toMonoidHom =
      projUnipotent 2 K := by
  have h : (tauAut : MulAut (StatedProj (StatedSp 2 K))).toMonoidHom.comp (proj 2 K) =
      (proj 2 K).comp (tauEquiv (F := K)).toMonoidHom :=
    MonoidHom.ext fun g => tauAut_proj g
  rw [projUnipotent, Subgroup.map_map, h, ← Subgroup.map_map, F134.Sp4.map_tauEquiv_unipotent]

theorem cartanConcl_projSp (hK4 : ∃ s : Finset K, s.card = 4) :
    CartanConcl (StatedProj (StatedSp 2 K)) (projUnipotent 2 K) False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro α _ hαU hN
  left
  obtain ⟨x, m, rfl⟩ := F134.Sp4.exists_eq_conj_mul_tauAut_pow α
  have hxU : (projUnipotent 2 K).map (MulAut.conj x).toMonoidHom = projUnipotent 2 K := by
    rw [map_mul_toMonoidHom, map_pow_eq map_projUnipotent_tauAut m] at hαU
    exact hαU
  have hxN := mem_normalizer_of_map_conj hxU
  rw [normalizer_projUnipotent 2 (by norm_num)] at hxN
  obtain ⟨b, hb, rfl⟩ := hxN
  have htest : ∀ s t : Fin 2 → Kˣ, (tauAut ^ m : MulAut (StatedProj (StatedSp 2 K)))
      (proj 2 K (SymplecticTorusWeyl.torusHom t)) = proj 2 K (SymplecticTorusWeyl.torusHom s) →
      s = t := by
    intro s t hst
    have h1 := hN (proj 2 K (SymplecticTorusWeyl.torusHom t)) (by
      rw [normalizer_projUnipotent 2 (by norm_num)]
      exact mem_map_of_mem _ (torus_le_borelSubgroup ⟨t, rfl⟩))
    rw [MulAut.mul_apply, hst, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← map_inv,
      ← map_mul] at h1
    obtain ⟨u, hu, hπ⟩ := h1
    exact eq_of_mem_unipotent hb
      (CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo hπ ▸ hu)
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hτ : (tauAut : MulAut (StatedProj (StatedSp 2 K))) ^ (2 * i) =
        fieldAut 2 K (frobAut K ^ i) := by
      rw [pow_mul, sq, tauAut_mul_self, map_pow]
    have hσ : frobAut K ^ i = 1 := by
      ext a
      by_cases ha : a = 0
      · rw [ha, map_zero, map_zero]
      have h1 := htest (fun _ => Units.map (frobAut K ^ i).toRingHom.toMonoidHom (Units.mk0 a ha))
        (fun _ => Units.mk0 a ha) (by rw [hτ, fieldAut_proj, fieldSp_torusHom])
      have h2 := congrArg (fun f : Fin 2 → Kˣ => ((f 0 : Kˣ) : K)) h1
      simpa using h2
    exact ⟨proj 2 K b, by rw [hτ, hσ, map_one, mul_one]⟩
  · exfalso
    have hτ : (tauAut : MulAut (StatedProj (StatedSp 2 K))) ^ (2 * i + 1) =
        fieldAut 2 K (frobAut K ^ i) * tauAut := by
      rw [pow_succ, pow_mul, sq, tauAut_mul_self, map_pow]
    obtain ⟨s, hs⟩ := exists_unit_ne_one hK4
    have h1 := htest (fun j => Units.map (frobAut K ^ i).toRingHom.toMonoidHom
      (![(1 : Kˣ) * s, 1 * s⁻¹] j)) ![1, s] (by
        rw [hτ, MulAut.mul_apply, tauAut_proj, tauSp_torusHom, fieldAut_proj, fieldSp_torusHom]
        rfl)
    have h2 := congrArg (fun f : Fin 2 → Kˣ => ((f 0 : Kˣ) : K)) h1
    simp only [Matrix.cons_val_zero, one_mul, Units.coe_map, Units.val_one] at h2
    apply hs
    have h3 : (frobAut K ^ i) (s : K) = (frobAut K ^ i) 1 := by
      rw [map_one]
      exact h2
    exact (frobAut K ^ i).injective h3

end CFSG.Quasithin.H13.NQCat.CartanSp4
