module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Derived

@[expose] def derivedCentralizer {H : Type*} [Group H] (G₀ : Subgroup H) (a : H) : Subgroup H :=
  ⁅G₀ ⊓ Subgroup.centralizer {a}, G₀ ⊓ Subgroup.centralizer {a}⁆

theorem derivedCentralizer_le {H : Type*} [Group H] (G₀ : Subgroup H) (a : H) :
    derivedCentralizer G₀ a ≤ G₀ := by
  refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_inf.mp hg₁).1 (Subgroup.mem_inf.mp hg₂).1)
    (inv_mem (Subgroup.mem_inf.mp hg₁).1)) (inv_mem (Subgroup.mem_inf.mp hg₂).1)

end Derived

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem conj_eichler_of_eigen {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u w : V} {α β : K} (hgu : g u = α • u) (hgw : g w = β • w) (s : K) :
    g * eichler Q u (s • w) * g⁻¹ = eichler Q u ((α * β * s) • w) := by
  rw [eichler_conj hg, hgu, map_smul, hgw, eichler_smul_left, smul_smul, smul_smul]
  congr 2
  ring

theorem eichler_mem_derivedCentralizer {G₀ : Subgroup (V ≃ₗ[K] V)}
    (hG₀ : G₀ ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {u w : V} (hw : polar Q u w = 0)
    (hX : ∀ s : K, eichler Q u (s • w) ∈ G₀) {a δ : V ≃ₗ[K] V} (ha : a ∈ G₀) (hδ : δ ∈ G₀)
    (hδa : δ * a = a * δ) {κ κ' μ ν : K} (hau : a u = κ • u) (haw : a w = κ' • w)
    (hκ : κ * κ' = 1) (hδu : δ u = μ • u) (hδw : δ w = ν • w) (hμν : μ * ν ≠ 1) :
    eichler Q u w ∈ derivedCentralizer G₀ a := by
  set x : K → (V ≃ₗ[K] V) := fun s => eichler Q u (s • w) with hx
  have hpol : ∀ s : K, polar Q u (s • w) = 0 := fun s => by
    rw [polar_smul_right_eq, hw, mul_zero]
  have hmul : ∀ s s' : K, x s * x s' = x (s + s') := fun s s' => by
    simp only [hx]
    rw [eichler_mul (hpol s) (hpol s'), add_smul]
  have hinv : ∀ s : K, (x s)⁻¹ = x (-s) := fun s => by
    simp only [hx]
    rw [eichler_inv (hpol s), neg_smul]
  have hxC : ∀ s : K, x s ∈ G₀ ⊓ Subgroup.centralizer {a} := fun s => by
    refine Subgroup.mem_inf.mpr ⟨hX s, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := conj_eichler_of_eigen (hG₀ ha) hau haw s
    rw [hκ, one_mul] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hδC : δ ∈ G₀ ⊓ Subgroup.centralizer {a} := by
    refine Subgroup.mem_inf.mpr ⟨hδ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hδa
  set v : K := (μ * ν - 1)⁻¹ with hv
  have hv1 : (μ * ν - 1) * v = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hμν)
  have h1 : δ * x v * δ⁻¹ = x (μ * ν * v) := conj_eichler_of_eigen (hG₀ hδ) hδu hδw v
  have hcomm : ⁅δ, x v⁆ = x 1 := by
    rw [commutatorElement_def, h1, hinv, hmul]
    congr 1
    linear_combination hv1
  have hmem : ⁅δ, x v⁆ ∈ derivedCentralizer G₀ a :=
    Subgroup.commutator_mem_commutator hδC (hxC v)
  rw [hcomm] at hmem
  simpa [hx] using hmem

end Eichler

section Eigen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mul_comm_of_eigen {S : Set V} (hS : Submodule.span K S = ⊤) {f g : V ≃ₗ[K] V}
    (h : ∀ v ∈ S, ∃ l m : K, f v = l • v ∧ g v = m • v) : f * g = g * f := by
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  show f (g x) = g (f x)
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, m, hf, hg⟩ := h v hv
    rw [hg, hf, map_smul, map_smul, hf, hg, smul_smul, smul_smul, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, map_smul, map_smul, hx]

end Eigen

section Characters

variable {G : Type*} [Group G]

theorem exists_ne_one_mem_ker {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (ψ : G →* Multiplicative (ZMod p)) : ∃ g : G, g ≠ 1 ∧ ψ g = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 := ψ.ker.card_mul_index
  rw [Subgroup.index_ker, hG] at h1
  have h2 : Nat.card ψ.range ≤ p := by
    calc Nat.card ψ.range ≤ Nat.card (Multiplicative (ZMod p)) := Nat.card_le_card_of_injective
          (Subtype.val) Subtype.val_injective
      _ = p := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h3 : p ≤ Nat.card ψ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ψ.ker * Nat.card ψ.range < p * p :=
      calc Nat.card ψ.ker * Nat.card ψ.range < p * Nat.card ψ.range :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.card_pos)
        _ ≤ p * p := Nat.mul_le_mul_left _ h2
    rw [h1] at this
    nlinarith
  have h4 : 1 < Nat.card ψ.ker := lt_of_lt_of_le hp.one_lt h3
  have : Finite ψ.ker := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial ψ.ker := Finite.one_lt_card_iff_nontrivial.mp h4
  obtain ⟨⟨g, hg⟩, hg1⟩ := exists_ne (1 : ψ.ker)
  exact ⟨g, fun h => hg1 (Subtype.ext h), MonoidHom.mem_ker.mp hg⟩

end Characters

section Characters

variable {r p : ℕ} {A : Type*} [Group A]

@[expose] def coordChar (χ : Fin r → (A →* Multiplicative (ZMod p))) (c : Fin r ⊕ Fin r) :
    A →* Multiplicative (ZMod p) :=
  Sum.elim χ (fun i => (χ i)⁻¹) c

theorem coordChar_swap (χ : Fin r → (A →* Multiplicative (ZMod p))) (c : Fin r ⊕ Fin r) :
    coordChar χ c.swap = (coordChar χ c)⁻¹ := by
  rcases c with i | i <;> simp [coordChar]

end Characters

section Zeta

variable {K : Type*} [Field K] {p : ℕ} [NeZero p]

@[expose] def zetaPow (ζ : K) (k : ZMod p) : K := ζ ^ k.val

omit [NeZero p] in
theorem pow_mod_eq_of_pow_eq_one {ζ : K} (hζ : ζ ^ p = 1) (m : ℕ) : ζ ^ (m % p) = ζ ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hζ, one_pow, one_mul]

theorem zetaPow_add {ζ : K} (hζ : ζ ^ p = 1) (k l : ZMod p) :
    zetaPow ζ (k + l) = zetaPow ζ k * zetaPow ζ l := by
  unfold zetaPow
  rw [ZMod.val_add, pow_mod_eq_of_pow_eq_one hζ, pow_add]

omit [NeZero p] in
theorem zetaPow_zero (ζ : K) : zetaPow (p := p) ζ 0 = 1 := by
  simp [zetaPow]

omit [NeZero p] in
theorem zetaPow_ne_zero {ζ : K} (hζ0 : ζ ≠ 0) (k : ZMod p) : zetaPow ζ k ≠ 0 :=
  pow_ne_zero _ hζ0

theorem zetaPow_neg {ζ : K} (hζ : ζ ^ p = 1) (k : ZMod p) :
    zetaPow ζ (-k) = (zetaPow ζ k)⁻¹ := by
  have h := zetaPow_add hζ k (-k)
  rw [add_neg_cancel, zetaPow_zero] at h
  have hne : zetaPow ζ k ≠ 0 := zetaPow_ne_zero (fun h0 => by
    rw [h0, zero_pow (NeZero.ne p)] at hζ
    exact zero_ne_one hζ) k
  exact eq_inv_of_mul_eq_one_right h.symm

end Zeta

end CFSG.RankThree.PartOne.KCOrthogonal
