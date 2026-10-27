module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus
public import CFSG.RankThree.PartTwo.Sec4.E27.D4Classify
public import CFSG.Sporadic.Suz.Simple

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section TypeII

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

@[expose] def StepALayer (σ : X ≃+* X) : Prop :=
  ∀ E : Subgroup (MulAut (C0 σ)), IsElemAbelian 3 E → Nat.card E = 27 →
    (∀ φ : MulAut (C0 σ), tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom) →
    ∀ x : C0 σ, MulAut.conj x ∈ E → x ≠ 1 →
      ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆ ≤
        Subgroup.closure
          {l | l ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆ ∧
            ∃ y ∈ E, y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l}

theorem typeII_seitzHyperGamma_layer (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) (hA : StepALayer σ) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27)
    (hno : ∀ φ : MulAut (C0 σ), tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom) :
    seitzHyperGamma 3 E = ⊤ := by
  have hinj := conj_injective_C0 σ n P.one_le P.card P.frob
  have hI9 := card_innerPart_eq σ n P.one_le P.card P.frob hE hcard
  obtain ⟨x₁, hx₁I, hx₁1⟩ : ∃ x ∈ innerPart σ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : innerPart σ E = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hI9
    omega
  have hx₁E : MulAut.conj x₁ ∈ E := (mem_innerPart σ).mp hx₁I
  have hx₁3 : x₁ ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hE.2 _ hx₁E)
  obtain ⟨x₂, hx₂I, hx₂z⟩ : ∃ x ∈ innerPart σ E, x ∉ Subgroup.zpowers x₁ := by
    by_contra hcon
    push Not at hcon
    have hle : innerPart σ E ≤ Subgroup.zpowers x₁ := hcon
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hx₁3 hx₁1, hI9] at this
    omega
  have hx₂E : MulAut.conj x₂ ∈ E := (mem_innerPart σ).mp hx₂I
  have hx₂1 : x₂ ≠ 1 := fun h => hx₂z (h ▸ one_mem _)
  have hcl₁ := classX_of_no_conj_tau hgold P hn hE hcard hno hx₁E hx₁1
  have hcl₂ := classX_of_no_conj_tau hgold P hn hE hcard hno hx₂E hx₂1
  have hc : x₁ * x₂ = x₂ * x₁ :=
    hinj (by rw [map_mul, map_mul]; exact comm_of_isElemAbelian hE hx₁E hx₂E)
  have hne : Subgroup.zpowers x₁ ≠ Subgroup.zpowers x₂ := fun h =>
    hx₂z (h ▸ Subgroup.mem_zpowers x₂)
  have hgen : ⁅Subgroup.centralizer ({x₁} : Set (C0 σ)), Subgroup.centralizer ({x₁} : Set (C0 σ))⁆ ⊔
      ⁅Subgroup.centralizer ({x₂} : Set (C0 σ)), Subgroup.centralizer ({x₂} : Set (C0 σ))⁆ = ⊤ :=
    closure_layer_two_X σ n hn P.card P.frob hcl₁ hcl₂ hc hne le_sup_left le_sup_right
  have hc₁ : (MulAut.conj x₁ : MulAut (C0 σ)) ≠ 1 := fun h => hx₁1 (hinj (by rw [h, map_one]))
  have hc₂ : (MulAut.conj x₂ : MulAut (C0 σ)) ≠ 1 := fun h => hx₂1 (hinj (by rw [h, map_one]))
  exact seitzHyperGamma_eq_top_of_two_fixed_lines hE hcard hx₁E hx₂E hc₁ hc₂
    (L₁ := ⁅Subgroup.centralizer ({x₁} : Set (C0 σ)), Subgroup.centralizer ({x₁} : Set (C0 σ))⁆)
    (L₂ := ⁅Subgroup.centralizer ({x₂} : Set (C0 σ)), Subgroup.centralizer ({x₂} : Set (C0 σ))⁆)
    (fun l hl => (fixed_conj_iff x₁ l).mpr (commutator_self_le _ hl))
    (fun l hl => (fixed_conj_iff x₂ l).mpr (commutator_self_le _ hl))
    (hA E hE hcard hno x₁ hx₁E hx₁1) (hA E hE hcard hno x₂ hx₂E hx₂1) hgen

end TypeII

end CFSG.RankThree.PartTwo.Sec4.E27
