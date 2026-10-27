module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1010Lin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj proj_eq_one_iff scalars)
open CFSG.Quasithin.H13.KG4413 (dg3 coe_dg3 dL3)

section Cartan

variable {K : Type} [Field K]

private theorem dg3_scalar_aux {t : Kˣ × Kˣ} (h : dg3 t ∈ scalars 3 K) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧ t = (c, c) := by
  obtain ⟨c, hc, hA⟩ := h
  refine ⟨c, hc, Prod.ext (Units.ext ?_) (Units.ext ?_)⟩
  · simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 0) 0
  · simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 1) 1

private theorem dt_mem_aux (x : Kˣ) : uc22s218_l3_dt K x ∈ dL3 K :=
  ⟨dg3 (x, 1), ⟨(x, 1), rfl⟩, rfl⟩

private theorem dt_injective_aux : Function.Injective (uc22s218_l3_dt K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : proj 3 K (dg3 (x, 1)) = 1 := hx
  obtain ⟨c, -, hc⟩ := dg3_scalar_aux (proj_eq_one_iff.1 hx')
  exact (congrArg Prod.fst hc).trans (congrArg Prod.snd hc).symm

private theorem dL3_comm_aux {a b : projectiveSL 3 K} (ha : a ∈ dL3 K) (hb : b ∈ dL3 K) :
    a * b = b * a := by
  obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hb
  have e : ∀ s t : Kˣ × Kˣ, proj 3 K (dg3 s) * proj 3 K (dg3 t) = proj 3 K (dg3 (s * t)) :=
    fun s t => by rw [map_mul, map_mul]
  rw [e, e, mul_comm]

end Cartan

section Model

theorem uc22s218_l3_torus_order_three {Y : Type} [Group Y] {n : ℕ} (hY : IsL3 Y n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ℓ ≠ 3 →
        ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2) ∧
      ∃ y ∈ T, orderOf y = 3 := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_l3_exists_model hY
  refine ⟨(dL3 K).map e.symm.toMonoidHom, ?_, fun ℓ hℓ hℓn hℓ3 => ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, dL3_comm_aux hx hy]
  · obtain ⟨A, hAT, hAe, hAc⟩ := uc22s218_l3_exists_elemAbelian hℓ hℓ3 (by rw [hK]; exact hℓn)
    refine ⟨A.map e.symm.toMonoidHom, Subgroup.map_mono hAT,
      CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hAc]
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
      (by rw [Nat.card_units, hK]; exact h3)
    refine ⟨e.symm (uc22s218_l3_dt K w), ⟨uc22s218_l3_dt K w, dt_mem_aux w, rfl⟩, ?_⟩
    rw [MulEquiv.orderOf_eq, orderOf_injective _ dt_injective_aux, hw]

private theorem two_pow_mod_nine {n : ℕ} (h2n : 2 ∣ n) (h3n : ¬ 3 ∣ n) :
    2 ^ n % 9 = 4 ∨ 2 ^ n % 9 = 7 := by
  have h6 : n % 6 = 2 ∨ n % 6 = 4 := by omega
  have h1 : (2 ^ 6) ^ (n / 6) % 9 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hn : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
    rw [Nat.mul_mod, h1, one_mul, Nat.mod_mod]
  rcases h6 with h | h <;> rw [hn, h] <;> norm_num

theorem uc22s218_l3_pRank_mulAut_le_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsL3 Y n)
    (h2n : 2 ∣ n) (h3n : ¬ 3 ∣ n) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_l3_exists_model hY
  have : Finite (MulAut Y) := Finite.of_injective (fun φ : MulAut Y => (φ : Y → Y))
    DFunLike.coe_injective
  have : Finite (MulAut (projectiveSL 3 K)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.finite_mulAut_projectiveSL 3
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e)]
  refine CFSG.HardMathSupport.Solomon.Coordinator.pRank_mulAut_projectiveSL_le_two ?_
  rw [hK]
  exact two_pow_mod_nine h2n h3n

theorem uc22s218_l3_center_eq_one {Y : Type} [Group Y] {n : ℕ} (hY : IsL3 Y n) :
    ∀ y : Y, (∀ x : Y, y * x = x * y) → y = 1 := by
  intro y hy
  obtain ⟨K, _, _, _, -, ⟨e⟩⟩ := uc22s218_l3_exists_model hY
  have hc : e y ∈ Subgroup.center (projectiveSL 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg e (hy (e.symm g))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
    exact h.symm
  rw [CFSG.QuasithinUnique.Setup.X7a.center_projectiveSL_three_eq_bot' (F := K),
    Subgroup.mem_bot] at hc
  exact e.injective (by rw [hc, map_one])

end Model

end CFSG.LocalAnalysis.UniquenessCase.UC22
