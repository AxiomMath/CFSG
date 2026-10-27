module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose tau coe_tau lam coe_lam
  radical mem_unipotent_iff unitri card_radical radical_le_unipotent tau_congr eq_sym2 lam_zero)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

variable {K : Type} [Field K]

@[expose] def lev (g : StatedSp 2 K) : K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₀ ι₁

theorem coe_tau_mul_lam' {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (a : K) :
    (((tau hC * lam a : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (unitri a) (C * (unitri (-a))ᵀ) 0 (unitri (-a))ᵀ := by
  rw [Subgroup.coe_mul, Units.val_mul, coe_tau, coe_lam, fromBlocks_multiply]
  simp

theorem lev_tau_mul_lam {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (a : K) :
    lev (tau hC * lam a) = a := by
  rw [lev, coe_tau_mul_lam']
  simp [unitri]

theorem lev_tau {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : lev (tau hC) = 0 := by
  rw [lev, coe_tau]
  simp

theorem lev_mul' {g g' : StatedSp 2 K} (hg : g ∈ unipotent 2 K) (hg' : g' ∈ unipotent 2 K) :
    lev (g * g') = lev g + lev g' := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.1 hg
  obtain ⟨C', hC', a', rfl⟩ := mem_unipotent_iff.1 hg'
  rw [lev_tau_mul_lam, lev_tau_mul_lam]
  rw [lev, Subgroup.coe_mul, Units.val_mul, coe_tau_mul_lam' hC a, coe_tau_mul_lam' hC' a',
    fromBlocks_multiply, fromBlocks_apply₁₁]
  simp [unitri, add_comm]

theorem entry_eq_zero_of_comm {C₀ : Matrix (Fin 2) (Fin 2) K} (hC₀ : C₀ᵀ = C₀) {a : K}
    (ha : a ≠ 0) {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C)
    (h : tau hC * (tau hC₀ * lam a) = (tau hC₀ * lam a) * tau hC) : C 1 1 = 0 := by
  have h' := congrArg (fun g : StatedSp 2 K => ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₀ ι₃) h
  have hL : (((tau hC * (tau hC₀ * lam a) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 1 C 0 1 * fromBlocks (unitri a) (C₀ * (unitri (-a))ᵀ) 0 (unitri (-a))ᵀ := by
    rw [← coe_tau hC, ← coe_tau_mul_lam' hC₀ a]
    rfl
  have hR : (((tau hC₀ * lam a * tau hC : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (unitri a) (C₀ * (unitri (-a))ᵀ) 0 (unitri (-a))ᵀ * fromBlocks 1 C 0 1 := by
    rw [← coe_tau hC, ← coe_tau_mul_lam' hC₀ a]
    rfl
  simp only [hL, hR, fromBlocks_multiply, fromBlocks_apply₁₂] at h'
  have h2 : a * C 1 1 = 0 := by
    simp [unitri, Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, vecMul, dotProduct] at h'
    linear_combination -h'
  exact (mul_eq_zero.mp h2).resolve_left ha

private def entA (x : StatedSp 2 K) : K :=
  ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₀ ι₂

private def entB (x : StatedSp 2 K) : K :=
  ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₀ ι₃

private theorem entA_tau {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : entA (tau hC) = C 0 0 := by
  rw [entA, coe_tau]
  simp

private theorem entB_tau {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : entB (tau hC) = C 0 1 := by
  rw [entB, coe_tau]
  simp

private theorem exists_tau_of_lev_eq_zero {x : StatedSp 2 K} (hx : x ∈ unipotent 2 K)
    (h0 : lev x = 0) : ∃ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C), x = tau hC := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.1 hx
  rw [lev_tau_mul_lam] at h0
  subst h0
  exact ⟨C, hC, by rw [lam_zero, mul_one]⟩

private theorem eq_of_entries {x y : StatedSp 2 K} (hx : x ∈ unipotent 2 K) (hy : y ∈ unipotent 2 K)
    (hx0 : lev x = 0) (hy0 : lev y = 0) {g₀ : StatedSp 2 K} (hg₀ : g₀ ∈ unipotent 2 K)
    (ha : lev g₀ ≠ 0) (hxc : x * g₀ = g₀ * x) (hyc : y * g₀ = g₀ * y)
    (hA : entA x = entA y) (hB : entB x = entB y) : x = y := by
  obtain ⟨C, hC, rfl⟩ := exists_tau_of_lev_eq_zero hx hx0
  obtain ⟨C', hC', rfl⟩ := exists_tau_of_lev_eq_zero hy hy0
  obtain ⟨C₀, hC₀, a₀, rfl⟩ := mem_unipotent_iff.1 hg₀
  rw [lev_tau_mul_lam] at ha
  have h1 := entry_eq_zero_of_comm hC₀ ha hC hxc
  have h2 := entry_eq_zero_of_comm hC₀ ha hC' hyc
  rw [entA_tau, entA_tau] at hA
  rw [entB_tau, entB_tau] at hB
  exact tau_congr _ _ (by rw [eq_sym2 hC, eq_sym2 hC', hA, hB, h1, h2])

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem card_le_pow_three_of_le_unipotent {E : Subgroup (StatedSp 2 K)} (hEU : E ≤ unipotent 2 K)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ Nat.card K ^ 3 := by
  by_cases hlev : ∀ x ∈ E, lev x = 0
  ·
    have hER : E ≤ radical K := fun x hx => by
      obtain ⟨C, hC, rfl⟩ := exists_tau_of_lev_eq_zero (hEU hx) (hlev x hx)
      exact ⟨C, hC, rfl⟩
    calc Nat.card E ≤ Nat.card (radical K) := Subgroup.card_le_of_le hER
      _ = Nat.card K ^ 3 := card_radical
  · push Not at hlev
    obtain ⟨g₀, hg₀E, hg₀⟩ := hlev
    let φ : E →* Multiplicative K :=
      { toFun := fun x => Multiplicative.ofAdd (lev (x : StatedSp 2 K))
        map_one' := by
          have : lev (1 : StatedSp 2 K) = 0 := by
            have := lev_tau (K := K) (C := 0) transpose_zero
            rwa [show tau (K := K) (C := 0) transpose_zero = 1 from by
              apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
              rw [coe_tau, fromBlocks_one]; rfl] at this
          simp [this]
        map_mul' := fun x y => by
          rw [Subgroup.coe_mul, lev_mul' (hEU x.2) (hEU y.2), ofAdd_add] }
    have hker : Nat.card φ.ker ≤ Nat.card K ^ 2 := by
      have hinj : Function.Injective (fun x : φ.ker => (entA ((x : E) : StatedSp 2 K),
          entB ((x : E) : StatedSp 2 K))) := by
        intro x y hxy
        have hA : entA ((x : E) : StatedSp 2 K) = entA ((y : E) : StatedSp 2 K) :=
          congrArg Prod.fst hxy
        have hB : entB ((x : E) : StatedSp 2 K) = entB ((y : E) : StatedSp 2 K) :=
          congrArg Prod.snd hxy
        have hx0 : lev ((x : E) : StatedSp 2 K) = 0 := congrArg Multiplicative.toAdd x.2
        have hy0 : lev ((y : E) : StatedSp 2 K) = 0 := congrArg Multiplicative.toAdd y.2
        apply Subtype.ext
        apply Subtype.ext
        exact eq_of_entries (hEU (x : E).2) (hEU (y : E).2) hx0 hy0 (hEU hg₀E) hg₀
          (hcomm _ (x : E).2 _ hg₀E) (hcomm _ (y : E).2 _ hg₀E) hA hB
      calc Nat.card φ.ker ≤ Nat.card (K × K) := Nat.card_le_card_of_injective _ hinj
        _ = Nat.card K ^ 2 := by rw [Nat.card_prod, sq]
    have hrange : Nat.card φ.range ≤ Nat.card K := by
      calc Nat.card φ.range ≤ Nat.card (Multiplicative K) := Finite.card_subtype_le _
        _ = Nat.card K := rfl
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker] at h1
    rw [← h1, show 3 = 2 + 1 from rfl, pow_succ]
    exact Nat.mul_le_mul hker hrange

private theorem exists_conj_le_unipotent' {Y : Subgroup (StatedSp 2 K)} (hY : IsPGroup 2 Y) :
    ∃ h : StatedSp 2 K, ∀ y ∈ Y, h⁻¹ * y * h ∈ unipotent 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨S, hS⟩, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.unique_symplectic_four_Sylow_center
      (K := K) (Nat.card K) rfl
  obtain ⟨P, hYP⟩ := hY.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (StatedSp 2 K) S P
  refine ⟨h, fun y hy => ?_⟩
  have hyP : y ∈ (P : Subgroup (StatedSp 2 K)) := hYP hy
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyP
  obtain ⟨b, hb, hby⟩ := hyP
  rw [← hby, MulAut.smul_def, MulAut.conj_apply, ← hS]
  simpa [mul_assoc] using hb

theorem card_le_pow_three_of_isPGroup {E : Subgroup (StatedSp 2 K)} (hE : IsPGroup 2 E)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ Nat.card K ^ 3 := by
  obtain ⟨h, hh⟩ := exists_conj_le_unipotent' hE
  set E' : Subgroup (StatedSp 2 K) := E.map (MulAut.conj h⁻¹).toMonoidHom with hE'
  have hmem : ∀ x, x ∈ E' ↔ ∃ y ∈ E, h⁻¹ * y * h = x := fun x => by
    rw [hE', Subgroup.mem_map]
    simp
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
  rw [← hcard]
  refine card_le_pow_three_of_le_unipotent (fun x hx => ?_) (fun x hx y hy => ?_)
  · obtain ⟨y, hyE, rfl⟩ := (hmem x).1 hx
    exact hh y hyE
  · obtain ⟨u, huE, rfl⟩ := (hmem x).1 hx
    obtain ⟨v, hvE, rfl⟩ := (hmem y).1 hy
    have := hcomm u huE v hvE
    calc h⁻¹ * u * h * (h⁻¹ * v * h) = h⁻¹ * (u * v) * h := by group
      _ = h⁻¹ * (v * u) * h := by rw [this]
      _ = h⁻¹ * v * h * (h⁻¹ * u * h) := by group

theorem card_le_pow_three_of_exponent_two {E : Subgroup (StatedSp 2 K)}
    (hsq : ∀ x ∈ E, x * x = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ Nat.card K ^ 3 :=
  card_le_pow_three_of_isPGroup (fun g => ⟨1, Subtype.ext (by
    rw [pow_one, sq]
    exact hsq g g.2)⟩) hcomm

end Sp4Inf

end CFSG.Quasithin
