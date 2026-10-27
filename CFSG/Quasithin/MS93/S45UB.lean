module

import CFSG.Quasithin.MS93.S4A432F
public import CFSG.Quasithin.MS93.ML3Sec
public import CFSG.Quasithin.MS93.S4ASL3

public section

namespace CFSG.Quasithin.MS93.S45U

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section DualFix

variable {F : Type} [Field F]

private theorem mem_span_of_le_orthN' {P : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) {y₀ y : Fin 3 → F} (hy₀ : y₀ ≠ 0)
    (h₀ : P ≤ S4A.orthN y₀) (h : P ≤ S4A.orthN y) : y ∈ Submodule.span F {y₀} := by
  have hP0 : S4A.orthN y₀ = P := S4A.eq_of_le_of_finrank_eq_two h₀ hP (S4A.orthN_ne_top hy₀)
  obtain ⟨i, hi⟩ : ∃ i, y₀ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy₀ (funext hcon)
  have key : ∀ x : Fin 3 → F, y ⬝ᵥ x = (y i / y₀ i) * (y₀ ⬝ᵥ x) := by
    intro x
    set t := (y₀ ⬝ᵥ x) / y₀ i with ht
    have hx : x - t • Pi.single i 1 ∈ S4A.orthN y₀ := by
      show y₀ ⬝ᵥ (x - t • Pi.single i 1) = 0
      rw [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, ht,
        div_mul_cancel₀ _ hi, sub_self]
    have hx' : y ⬝ᵥ (x - t • Pi.single i 1) = 0 := h (hP0 ▸ hx)
    rw [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
      sub_eq_zero] at hx'
    rw [hx', ht]
    ring
  rw [Submodule.mem_span_singleton]
  refine ⟨y i / y₀ i, funext fun j => ?_⟩
  have := key (Pi.single j 1)
  rw [dotProduct_single, mul_one, dotProduct_single, mul_one] at this
  rw [Pi.smul_apply, smul_eq_mul, this]

theorem card_dualFix_le' [Finite F] {A : Subgroup (SL3 F)}
    (hA : 2 ≤ Module.finrank F (CFSG.Quasithin.MS93.commN A)) (S : Set (Fin 3 → F))
    (hS : ∀ y ∈ S, ∀ g ∈ A, CFSG.Quasithin.MS93.dualMat g *ᵥ y = y) :
    Nat.card S ≤ Nat.card F := by
  by_cases h0 : ∀ y ∈ S, y = 0
  · have hsub : S ⊆ {0} := fun y hy => h0 y hy
    calc Nat.card S ≤ Nat.card ({0} : Set (Fin 3 → F)) :=
          Nat.card_mono (Set.finite_singleton 0) hsub
      _ = 1 := Nat.card_unique
      _ ≤ Nat.card F := Nat.card_pos
  push Not at h0
  obtain ⟨y₀, hy₀S, hy₀⟩ := h0
  have h₀ : CFSG.Quasithin.MS93.commN A ≤ S4A.orthN y₀ :=
    S4A.commN_le_orthN (hS y₀ hy₀S)
  have hP : Module.finrank F (CFSG.Quasithin.MS93.commN A) = 2 := by
    have h1 := Submodule.finrank_mono h₀
    have h2 : Module.finrank F (S4A.orthN y₀) < 3 := by
      have := Submodule.finrank_lt (S4A.orthN_ne_top hy₀)
      rwa [Module.finrank_fin_fun] at this
    omega
  have hsub : S ⊆ (Submodule.span F {y₀} : Set (Fin 3 → F)) := fun y hy =>
    mem_span_of_le_orthN' hP hy₀ h₀ (S4A.commN_le_orthN (hS y hy))
  calc Nat.card S ≤ Nat.card (Submodule.span F {y₀} : Set (Fin 3 → F)) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ = Nat.card F := by
        change Nat.card ↥(Submodule.span F {y₀}) = Nat.card F
        rw [Module.natCard_eq_pow_finrank (K := F), finrank_span_singleton hy₀, pow_one]

end DualFix

section NatCount

variable {Γ : Type} [Group Γ] {F : Type} [Field F]

open NatSec in
theorem dualFix_of_comm {L V K Q : Subgroup Γ} {ψ : ↥L →* ↥(StatedSL 3 F)}
    (N : NatSec L V K ψ true) (hQL : Q ≤ L) {v : Γ} (hv : v ∈ V)
    (hC : ∀ t ∈ Q, ⁅v, t⁆ ∈ K) :
    ∀ a ∈ natImage ψ Q, CFSG.Quasithin.MS93.dualMat a *ᵥ N.coord v = N.coord v := by
  intro a ha
  obtain ⟨s, hs, rfl⟩ := mem_natImage.mp ha
  have hcomm := hC (s : Γ) hs
  have e : ⁅v, (s : Γ)⁆ = v * ((s : Γ) * v * (s : Γ)⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  have hmem : ⁅v, (s : Γ)⁆ ∈ V := by
    rw [e]
    exact V.mul_mem hv (V.inv_mem (N.conj_mem s hv))
  have h0 : N.coord ⁅v, (s : Γ)⁆ = 0 := (N.coord_eq_zero_iff hmem).mpr hcomm
  rw [e, N.coord_mul hv (V.inv_mem (N.conj_mem s hv)), N.coord_inv (N.conj_mem s hv),
    N.coord_conj s hv, natAct_true] at h0
  exact (add_neg_eq_zero.mp h0).symm

end NatCount

end CFSG.Quasithin.MS93.S45U
