module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualField
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z X B : Subgroup G}

theorem exists_natDualCoord {n : ℕ} (hc : Ctx M Q Z X) (hw : Width Q Z n) (hn : 2 < n)
    (hVI : CaseVI M Q Z (Lgen M (LB M Q X))) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ' : ↥(Lgen M (LB M Q X)) →* GL (Fin n) F)
      (C : NatDualCoord (φ.comp (Subgroup.inclusion (Lgen_le_H0 hc))) ρ'),
      ρ'.range = StatedSL n F ∧ ρ'.ker = Q.subgroupOf (Lgen M (LB M Q X)) ∧
      ∃ V₁ V₂ : Subgroup G, V₁ ≤ Q ∧ V₂ ≤ Q ∧ (∀ e, e ∈ M₀.img V₁ ↔ (C.Ψ e).2 = 0) ∧
        (∀ e, e ∈ M₀.img V₂ ↔ (C.Ψ e).1 = 0) ∧ ∃ x ∈ M, conjSubgroup x V₁ = V₂ := by
  obtain ⟨n', F, hFfield, hFfin, hFcard, φ', hrange, hker, V₁, V₂, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf,
    hsup, hact₁, hact₂, hx, -⟩ := hVI
  have hSH : Lgen M (LB M Q X) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φ, hΦ, hΦ₁, hΦ₂⟩ := exists_equivariant_coord M₀
    (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  have hq4 := hc.hyp.q4
  have hK1 : 1 < Nat.card K := by rw [h.card]; omega
  have hF1 : 1 < Nat.card F := by rw [hFcard]; omega
  have hcardE : Nat.card M₀.E = Nat.card F ^ (2 * n') := by
    rw [Nat.card_congr Φ.toEquiv, Nat.card_prod, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin n'), Fintype.card_fin, two_mul, pow_add]
  have hcardE' : Nat.card M₀.E = Nat.card F ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := M₀.E), h.finrank_E hw hK1, h.card, hFcard]
  have hnn : n' = n := by
    have := Nat.pow_right_injective hF1 (hcardE.symm.trans hcardE')
    omega
  subst hnn
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ'
    (by omega) hrange (by rw [h.card, hFcard]) Φ hΦ
  refine ⟨F, hFfield, hFfin, φ', C, hrange, hker, V₁, V₂, hV₁Q, hV₂Q, ?_, ?_, hx⟩
  · intro e
    rw [hCΦ]
    exact hΦ₁ e
  · intro e
    rw [hCΦ]
    exact hΦ₂ e

@[expose] def quadDatumOfModel {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) : QuadDatum K M₀.E where
  Qf := M₀.Qf
  B := M₀.B
  Qf_smul := M₀.Qf_smul
  Qf_add := M₀.Qf_add
  alt := M₀.alt
  nondeg := M₀.nondeg

end CFSG.RankThree.GF2n.Stroth80
