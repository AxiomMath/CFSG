module

public import CFSG.Quasithin.H13.A5W1618h
public import CFSG.Quasithin.Background.DicksonPerfectSL2
public import CFSG.Quasithin.H13.A5W1618g

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

local notation "StSL" => Assembly.LowTwoRank.StatedSL

section General

variable {G : Type} [Group G]

theorem commutatorElement_mul_of_mem_center {M : Type*} [Group M] {x y c d : M}
    (hc : c ∈ Subgroup.center M) (hd : d ∈ Subgroup.center M) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  rw [Subgroup.mem_center_iff] at hc hd
  have h1 : c * (y * d) = y * d * c := (hc _).symm
  have h2 : d * x⁻¹ = x⁻¹ * d := (hd _).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹
      = x * (c * (y * d)) * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by group
    _ = x * (y * d * c) * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by rw [h1]
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [h2]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_mem_commutator_of_perfect {K Q : Subgroup G} {a : G} (hQK : Q ≤ K)
    (hQn : K ≤ Subgroup.normalizer (Q : Set G)) (hKp : ⁅K, K⁆ = K)
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (h : ∀ k ∈ K, k⁻¹ * a * k * a⁻¹ ∈ Q) :
    ∀ k ∈ K, k⁻¹ * a * k * a⁻¹ ∈ ⁅Q, K⁆ := by
  set U := ⁅Q, K⁆ with hU
  have hUK : U ≤ K := (Subgroup.commutator_mono hQK le_rfl).trans
    (A3.commutator_self_le K)
  have hUn : K ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator hQn Subgroup.le_normalizer
  have hconj : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (hUn hk) u).mp hu
  have haK : ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp ha k).mp hk
  let D : Subgroup G :=
    { carrier := {k | k ∈ K ∧ k⁻¹ * a * k * a⁻¹ ∈ U}
      one_mem' := ⟨K.one_mem, by simp [U.one_mem]⟩
      mul_mem' := fun {k l} hk hl => by
        refine ⟨K.mul_mem hk.1 hl.1, ?_⟩
        have e : (k * l)⁻¹ * a * (k * l) * a⁻¹ =
            l⁻¹ * (k⁻¹ * a * k * a⁻¹) * l⁻¹⁻¹ * (l⁻¹ * a * l * a⁻¹) := by group
        rw [e]
        exact U.mul_mem (hconj _ (K.inv_mem hl.1) _ hk.2) hl.2
      inv_mem' := fun {k} hk => by
        refine ⟨K.inv_mem hk.1, ?_⟩
        have e : k⁻¹⁻¹ * a * k⁻¹ * a⁻¹ = k * (k⁻¹ * a * k * a⁻¹)⁻¹ * k⁻¹ := by group
        rw [e]
        exact hconj _ hk.1 _ (U.inv_mem hk.2) }
  let N : Subgroup ↥K := U.subgroupOf K
  have hN : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).mpr hUn
  let π : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N
  have hcen : ∀ q : ↥K, (q : G) ∈ Q → π q ∈ Subgroup.center (↥K ⧸ N) := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [← map_mul, ← map_mul]
    refine (QuotientGroup.eq).mpr ?_
    show (((k * q)⁻¹ * (q * k) : ↥K) : G) ∈ U
    have e : (((k * q)⁻¹ * (q * k) : ↥K) : G) = ⁅(q : G)⁻¹, (k : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (Q.inv_mem hq) (K.inv_mem k.2)
  have hcomm : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ D := by
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ K := K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx))
      (K.inv_mem hy)
    refine ⟨hxy, ?_⟩
    set dx := x⁻¹ * (a * x * a⁻¹) with hdx
    set dy := y⁻¹ * (a * y * a⁻¹) with hdy
    have hdxQ : dx ∈ Q := by rw [hdx, ← mul_assoc, ← mul_assoc]; exact h x hx
    have hdyQ : dy ∈ Q := by rw [hdy, ← mul_assoc, ← mul_assoc]; exact h y hy
    have hdxK := hQK hdxQ
    have hdyK := hQK hdyQ
    have e1 : a * ⁅x, y⁆ * a⁻¹ = ⁅x * dx, y * dy⁆ := by
      rw [hdx, hdy, commutatorElement_def, commutatorElement_def]; group
    have e2 : π ⟨⁅x * dx, y * dy⁆, by
        rw [← e1]; exact haK _ hxy⟩ = π ⟨⁅x, y⁆, hxy⟩ := by
      have h3 := commutatorElement_mul_of_mem_center (x := π ⟨x, hx⟩) (y := π ⟨y, hy⟩)
        (hcen ⟨dx, hdxK⟩ hdxQ) (hcen ⟨dy, hdyK⟩ hdyQ)
      rw [← map_mul, ← map_mul, ← map_commutatorElement, ← map_commutatorElement] at h3
      convert h3 using 2
    have e3 := (QuotientGroup.eq).mp e2.symm
    have e4 : (⟨⁅x, y⁆, hxy⟩ : ↥K)⁻¹ * ⟨⁅x * dx, y * dy⁆, by rw [← e1]; exact haK _ hxy⟩ =
        (⟨⁅x, y⁆⁻¹ * (a * ⁅x, y⁆ * a⁻¹), K.mul_mem (K.inv_mem hxy) (haK _ hxy)⟩ : ↥K) :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, e1])
    rw [e4] at e3
    have e5 : ⁅x, y⁆⁻¹ * a * ⁅x, y⁆ * a⁻¹ = ⁅x, y⁆⁻¹ * (a * ⁅x, y⁆ * a⁻¹) := by group
    rw [e5]
    exact e3
  have hKD : K ≤ D := by
    calc K = ⁅K, K⁆ := hKp.symm
      _ ≤ D := Subgroup.commutator_le.mpr hcomm
  exact fun k hk => (hKD hk).2

end General

section Block

variable {G : Type} [Group G]

theorem mem_blockZ_of_conj_eq {K₀ : Subgroup G} {F : Type} [Field F] [CharP F 2]
    {α : ↥K₀ →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : ↥(blockU K₀) →* Multiplicative (Fin 2 → F)}
    (hβk : β.ker = (blockZ K₀).subgroupOf (blockU K₀))
    (hβe : ∀ ℓ : ↥K₀, ∀ u v : ↥(blockU K₀), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {y : ↥K₀} (hy3 : α y ^ 3 = 1) (hy1 : α y ≠ 1) {u : ↥(blockU K₀)}
    (hu : (y : G) * u * (y : G)⁻¹ = u) : (u : G) ∈ blockZ K₀ := by
  have h1 := hβe y u u hu.symm
  have hM3 : (α y : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hy3, Matrix.SpecialLinearGroup.coe_one]
  have hM1 : (α y : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h =>
    hy1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one]))
  have h0 := eq_zero_of_mulVec_eq_of_pow_three (α y).2 hM3 hM1 h1.symm
  have hβ1 : β u = 1 := by
    have : Multiplicative.toAdd (β u) = Multiplicative.toAdd (1 : Multiplicative (Fin 2 → F)) :=
      h0.trans rfl
    exact Multiplicative.toAdd.injective this
  have hker : u ∈ β.ker := hβ1
  rw [hβk] at hker
  exact hker

end Block

end CFSG.Quasithin.H13.A5
