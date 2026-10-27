module

public import CFSG.Quasithin.Vol2.Ch11SecHP2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    CharP F 2 := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨k, hk, hk'⟩ := FiniteField.card F p
  have h1 : (p : ℕ) ^ (k : ℕ) = 2 ^ n := by rw [← hk', ← Nat.card_eq_fintype_card, hF]
  have h2 : p ∣ 2 ^ n := ⟨p ^ ((k : ℕ) - 1), by
    rw [← h1, ← pow_succ']; congr 1; have := k.pos; omega⟩
  have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h2)
  exact h3 ▸ hp

section Coords

variable {W : Type*} [CommGroup W] {F : Type} [Field F] {φ : W → (Fin 3 → F)}

theorem coords_one (hφ : ∀ a b, φ (a * b) = φ a + φ b) : φ 1 = 0 := by
  have := hφ 1 1
  rw [mul_one] at this
  exact left_eq_add.mp this

theorem coords_inv (hφ : ∀ a b, φ (a * b) = φ a + φ b) (a : W) : φ a⁻¹ = -φ a := by
  have := hφ a a⁻¹
  rw [mul_inv_cancel, coords_one hφ] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem coords_mul_inv (hφ : ∀ a b, φ (a * b) = φ a + φ b) (a b : W) :
    φ (a * b⁻¹) = φ a - φ b := by
  rw [hφ, coords_inv hφ, sub_eq_add_neg]

theorem coords_comm (hφ : ∀ a b, φ (a * b) = φ a + φ b) (σ : MulAut W)
    (γ : Matrix (Fin 3) (Fin 3) F) (hσ : ∀ w, φ (σ w) = γ.mulVec (φ w)) (v : W) :
    φ (v * (σ v)⁻¹) = φ v - γ.mulVec (φ v) := by
  rw [coords_mul_inv hφ, hσ]

end Coords

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem comm_mem_V (i : Inp32) {v p : G} (hv : v ∈ fsuV T I) (hp : p ∈ pOf T I H h) :
    v * p * v⁻¹ * p⁻¹ ∈ fsuV T I := by
  have hpN : p ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    d.pCoreOf_le_normalizer_V (d.P_le_pCoreOf i hp)
  have := (Subgroup.mem_normalizer_iff.mp hpN v⁻¹).mp ((fsuV T I).inv_mem hv)
  have h2 : v * p * v⁻¹ * p⁻¹ = v * (p * v⁻¹ * p⁻¹) := by group
  rw [h2]
  exact (fsuV T I).mul_mem hv this

theorem comm_mem_P (i : Inp32) {v p : G} (hv : v ∈ fsuV T I) (hp : p ∈ pOf T I H h) :
    v * p * v⁻¹ * p⁻¹ ∈ pOf T I H h :=
  (pOf T I H h).mul_mem ((Subgroup.mem_normalizer_iff.mp (d.fsuV_le_normalizer_P i hv) p).mp hp)
    ((pOf T I H h).inv_mem hp)

theorem comm_mem_B (i : Inp32) {v p : G} (hv : v ∈ fsuV T I) (hp : p ∈ pOf T I H h) :
    v * p * v⁻¹ * p⁻¹ ∈ bOf T I H := by
  rw [← d.P_inf_centralizer_V i]
  refine Subgroup.mem_inf.mpr ⟨d.comm_mem_P i hv hp, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact comm_of_isElemAbelian (SecA.isElemAbelian_fsuV d.c.s.hyp) hu (d.comm_mem_V i hv hp)

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
