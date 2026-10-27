module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveFrame

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

@[expose] def gen5 (ν α β : ZMod 5) (u : ZMod 5 × ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 × ZMod 5 :=
  (ν * u.1, β * u.2.2, u.2.1 + α * u.2.2)

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f : ℕ} (S : StdHyp G Q a b j s p f 3) [Finite G] [Finite Ω] (h5 : p ^ f = 5)
  (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
  {t : G} (ht : t ∈ pairStab G a b) (hot : orderOf t = 8)
  {z₀ v₀ : G} (hz₀ : z₀ ∈ centQ Q j) (hz₀1 : z₀ ≠ 1) (hv₀ : v₀ ∈ AbelianQ.invSub Q j hQab)
  (hv₀1 : v₀ ≠ 1)
include S h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1

theorem exists_gen_formula : ∃ ν α β : ZMod 5, ∀ m,
    t * coord5 z₀ v₀ (t * v₀ * t⁻¹) m * t⁻¹ = coord5 z₀ v₀ (t * v₀ * t⁻¹) (gen5 ν α β m) := by
  set v₁ := t * v₀ * t⁻¹ with hv₁def
  have hz : z₀ ∈ Q := (mem_centQ.mp hz₀).1
  have hv : v₀ ∈ Q := hv₀.1
  have hv1 := S.v₁_mem hQab ht hv₀
  have hv1Q : v₁ ∈ Q := hv1.1
  have htz : t * z₀ * t⁻¹ ∈ centQ Q j := S.root.conj_mem_centQ S.hcomm S.hj ht hz₀
  obtain ⟨m₁, hm₁⟩ := S.coord5_surjective h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1
    (mem_centQ.mp htz).1
  have hm₁2 : m₁.2 = 0 := (S.coord5_mem_centQ_iff h5 hQab ht hot hz₀ hv₀ hv₀1 m₁).mp
    (by rw [hm₁]; exact htz)
  have htv : t * v₁ * t⁻¹ ∈ AbelianQ.invSub Q j hQab :=
    AbelianQ.conj_mem_invSub S.root S.hb S.hcomm S.hj ht.1 hv1
  obtain ⟨m₂, hm₂⟩ := S.coord5_surjective h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1 htv.1
  have hm₂1 : m₂.1 = 0 := (S.coord5_mem_invSub_iff h5 hQab ht hz₀ hz₀1 hv₀ m₂).mp
    (by rw [hm₂]; exact htv)
  refine ⟨m₁.1, m₂.2.2, m₂.2.1, fun m => ?_⟩
  have e1 : t * z₀ * t⁻¹ = pow5 z₀ m₁.1 := by
    rw [← hm₁, coord5, hm₁2]; simp [pow5_zero]
  have e2 : t * v₁ * t⁻¹ = pow5 v₀ m₂.2.1 * pow5 v₁ m₂.2.2 := by
    rw [← hm₂, coord5, hm₂1, pow5_zero, one_mul]
  have h5z := S.pow_five_eq_one h5 hz
  have h5v := S.pow_five_eq_one h5 hv
  have h5v1 := S.pow_five_eq_one h5 hv1Q
  have c01 : v₀ * v₁ = v₁ * v₀ := hQab _ hv _ hv1Q
  have hpow : ∀ (c : ZMod 5), pow5 (pow5 v₀ m₂.2.1 * pow5 v₁ m₂.2.2) c =
      pow5 v₀ (m₂.2.1 * c) * pow5 v₁ (m₂.2.2 * c) := by
    intro c
    have hc : Commute (pow5 v₀ m₂.2.1) (pow5 v₁ m₂.2.2) := commute_pow5 c01 _ _
    rw [pow5, hc.mul_pow]
    change pow5 (pow5 v₀ m₂.2.1) c * pow5 (pow5 v₁ m₂.2.2) c = _
    rw [← pow5_mul h5v, ← pow5_mul h5v1]
  calc t * coord5 z₀ v₀ v₁ m * t⁻¹
      = (t * pow5 z₀ m.1 * t⁻¹) * (t * pow5 v₀ m.2.1 * t⁻¹) * (t * pow5 v₁ m.2.2 * t⁻¹) := by
        rw [coord5]; group
    _ = pow5 (pow5 z₀ m₁.1) m.1 * pow5 v₁ m.2.1 *
          pow5 (pow5 v₀ m₂.2.1 * pow5 v₁ m₂.2.2) m.2.2 := by
        rw [conj_pow5, conj_pow5, conj_pow5, e1, e2]
    _ = pow5 z₀ (m₁.1 * m.1) * pow5 v₁ m.2.1 *
          (pow5 v₀ (m₂.2.1 * m.2.2) * pow5 v₁ (m₂.2.2 * m.2.2)) := by
        rw [← pow5_mul h5z, hpow]
    _ = pow5 z₀ (m₁.1 * m.1) * pow5 v₀ (m₂.2.1 * m.2.2) *
          (pow5 v₁ m.2.1 * pow5 v₁ (m₂.2.2 * m.2.2)) := by
        have := commute_pow5 c01.symm m.2.1 (m₂.2.1 * m.2.2)
        calc pow5 z₀ (m₁.1 * m.1) * pow5 v₁ m.2.1 *
              (pow5 v₀ (m₂.2.1 * m.2.2) * pow5 v₁ (m₂.2.2 * m.2.2))
            = pow5 z₀ (m₁.1 * m.1) * (pow5 v₁ m.2.1 * pow5 v₀ (m₂.2.1 * m.2.2)) *
                pow5 v₁ (m₂.2.2 * m.2.2) := by group
          _ = pow5 z₀ (m₁.1 * m.1) * (pow5 v₀ (m₂.2.1 * m.2.2) * pow5 v₁ m.2.1) *
                pow5 v₁ (m₂.2.2 * m.2.2) := by rw [this]
          _ = _ := by group
    _ = coord5 z₀ v₀ v₁ (gen5 m₁.1 m₂.2.2 m₂.2.1 m) := by
        rw [← pow5_add h5v1, coord5, gen5]

variable {ν α β : ZMod 5}
  (hgf : ∀ m, t * coord5 z₀ v₀ (t * v₀ * t⁻¹) m * t⁻¹ =
    coord5 z₀ v₀ (t * v₀ * t⁻¹) (gen5 ν α β m))
include hgf

omit [Finite G] [Finite Ω] h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1 S in
theorem conj_pow_coord5 (k : ℕ) (m : ZMod 5 × ZMod 5 × ZMod 5) :
    t ^ k * coord5 z₀ v₀ (t * v₀ * t⁻¹) m * (t ^ k)⁻¹ =
      coord5 z₀ v₀ (t * v₀ * t⁻¹) ((gen5 ν α β)^[k] m) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    calc t ^ (k + 1) * coord5 z₀ v₀ (t * v₀ * t⁻¹) m * (t ^ (k + 1))⁻¹
        = t ^ k * (t * coord5 z₀ v₀ (t * v₀ * t⁻¹) m * t⁻¹) * (t ^ k)⁻¹ := by
          rw [pow_succ]; group
      _ = coord5 z₀ v₀ (t * v₀ * t⁻¹) ((gen5 ν α β)^[k] (gen5 ν α β m)) := by rw [hgf, ih]
      _ = _ := by rw [Function.iterate_succ_apply]

theorem nu_mul_nu : ν * ν = -1 := by
  have hψ1 : coord5 z₀ v₀ (t * v₀ * t⁻¹) (1, 0, 0) = z₀ := by
    rw [coord5]; simp [pow5_zero, pow5_one]
  have hgen1 : ∀ c : ZMod 5, gen5 ν α β (c, 0, 0) = (ν * c, 0, 0) := by
    intro c; simp [gen5]
  have hj4 := S.pow_four_eq ht hot
  have hν4 : ν ^ 4 = 1 := by
    have h1 := conj_pow_coord5 hgf 4 (1, 0, 0)
    rw [hψ1, hj4] at h1
    have hjz : j * z₀ * j⁻¹ = z₀ := by
      rw [(mem_centQ.mp hz₀).2]; group
    rw [hjz, show (gen5 ν α β)^[4] (1, 0, 0) = (ν ^ 4, 0, 0) by
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, hgen1]; ring_nf] at h1
    have := S.coord5_injective h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1 (h1.symm.trans hψ1.symm)
    exact congrArg Prod.fst this
  have hν2 : ν ^ 2 ≠ 1 := by
    intro e
    have h1 := conj_pow_coord5 hgf 2 (1, 0, 0)
    rw [hψ1, show (gen5 ν α β)^[2] (1, 0, 0) = (ν ^ 2, 0, 0) by
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, hgen1]; ring_nf,
      e, hψ1] at h1
    have hcomm2 : t ^ 2 * z₀ = z₀ * t ^ 2 := by
      calc t ^ 2 * z₀ = t ^ 2 * z₀ * (t ^ 2)⁻¹ * t ^ 2 := by group
        _ = z₀ * t ^ 2 := by rw [h1]
    have ht2 : t ^ 2 ∈ pairStab G a b := (pairStab G a b).pow_mem ht 2
    have hs2' := S.root.conj_eq_of_commute S.hb S.hsa S.hsb S.hcomm (mem_centQ.mp hz₀).1 hz₀1 ht2
      hcomm2
    have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, S.hs2]
    rw [hs] at hs2'
    have hW2 : t ^ 2 ∈ swapFix G a b s := by
      refine mem_swapFix.mpr ⟨ht2, ?_⟩
      calc s * t ^ 2 = s * t ^ 2 * s * s := by rw [mul_assoc _ s s, S.hs2, mul_one]
        _ = t ^ 2 * s := by rw [hs2']
    have hWj : j ∈ swapFix G a b s := mem_swapFix.mpr ⟨S.hj, S.hsj⟩
    have hW := S.card_swapFix_eq_two h5
    classical
    have : Fintype (swapFix G a b s) := Fintype.ofFinite _
    have hne : ∀ i k : ℕ, i < 8 → k < 8 → i ≠ k → t ^ i ≠ t ^ k := by
      intro i k hi hk hik e
      rw [← hot] at hi hk
      exact hik (pow_injOn_Iio_orderOf hi hk e)
    have h12 : (1 : G) ≠ t ^ 2 := by
      have := hne 0 2 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero] at this
    have h1j : (1 : G) ≠ j := fun e => S.hj1 e.symm
    have h2j : t ^ 2 ≠ j := by rw [← hj4]; exact hne 2 4 (by norm_num) (by norm_num) (by norm_num)
    have hsub : ({⟨1, (swapFix G a b s).one_mem⟩, ⟨t ^ 2, hW2⟩, ⟨j, hWj⟩} :
        Finset (swapFix G a b s)).card ≤ Fintype.card (swapFix G a b s) := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton,
      ← Nat.card_eq_fintype_card, hW] at hsub
    · omega
    · simp only [Finset.mem_singleton, Subtype.mk.injEq]; exact h2j
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨h12, h1j⟩
  revert hν4 hν2
  generalize ν = x
  revert x
  decide

theorem gen5_four :
    (gen5 ν α β)^[4] (0, 1, 0) = (0, -1, 0) ∧ (gen5 ν α β)^[4] (0, 0, 1) = (0, 0, -1) := by
  have hj4 := S.pow_four_eq ht hot
  have hv1 := S.v₁_mem hQab ht hv₀
  have h5v := S.pow_five_eq_one h5 hv₀.1
  have h5v1 := S.pow_five_eq_one h5 hv1.1
  have hinj := S.coord5_injective h5 hQab ht hot hz₀ hz₀1 hv₀ hv₀1
  constructor
  · apply hinj
    rw [← conj_pow_coord5 hgf 4, hj4]
    have e1 : coord5 z₀ v₀ (t * v₀ * t⁻¹) (0, 1, 0) = v₀ := by
      rw [coord5]; simp [pow5_zero, pow5_one]
    have e2 : coord5 z₀ v₀ (t * v₀ * t⁻¹) (0, -1, 0) = v₀⁻¹ := by
      rw [coord5]; simp only [pow5_zero, one_mul, mul_one]; rw [pow5_neg h5v, pow5_one]
    rw [e1, e2]
    exact hv₀.2
  · apply hinj
    rw [← conj_pow_coord5 hgf 4, hj4]
    have e1 : coord5 z₀ v₀ (t * v₀ * t⁻¹) (0, 0, 1) = t * v₀ * t⁻¹ := by
      rw [coord5]; simp [pow5_zero, pow5_one]
    have e2 : coord5 z₀ v₀ (t * v₀ * t⁻¹) (0, 0, -1) = (t * v₀ * t⁻¹)⁻¹ := by
      rw [coord5]; simp only [pow5_zero, one_mul]; rw [pow5_neg h5v1, pow5_one]
    rw [e1, e2]
    exact hv1.2

end StdHyp

end CFSG.UnitaryThreeRecognition
