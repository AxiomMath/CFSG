module

public import CFSG.RankThree.Co2.Classes
public import CFSG.RankThree.Co2.Partner

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv

@[expose] def PartnerPair (i j : ℕ) : Prop :=
  ∃ Ψ : Subgroup.centralizer ({rep i} : Set Cr) ≃* Subgroup.centralizer ({rep j} : Set Cr),
    Ψ (selfC (rep i)) = centralC rCr_mem_center (rep j) ∧
      Ψ (centralC rCr_mem_center (rep i)) = selfC (rep j)

@[expose] def PartnerElts (a b : Cr) : Prop :=
  ∃ Ψ : Subgroup.centralizer ({a} : Set Cr) ≃* Subgroup.centralizer ({b} : Set Cr),
    Ψ (selfC a) = centralC rCr_mem_center b ∧ Ψ (centralC rCr_mem_center a) = selfC b

theorem PartnerElts.symm {a b : Cr} (h : PartnerElts a b) : PartnerElts b a := by
  obtain ⟨Ψ, h1, h2⟩ := h
  refine ⟨Ψ.symm, ?_, ?_⟩
  · rw [← h2, MulEquiv.symm_apply_apply]
  · rw [← h1, MulEquiv.symm_apply_apply]

theorem conj_rCr (c : Cr) : c * rCr * c⁻¹ = rCr := by
  have := Subgroup.mem_center_iff.1 rCr_mem_center c
  rw [this, mul_inv_cancel_right]

@[expose] def conjTransport {a b : Cr}
    (Ψ : Subgroup.centralizer ({a} : Set Cr) ≃* Subgroup.centralizer ({b} : Set Cr)) (c d : Cr) :
    Subgroup.centralizer ({c * a * c⁻¹} : Set Cr) ≃*
      Subgroup.centralizer ({d * b * d⁻¹} : Set Cr) :=
  ((centralizerConjEquiv c a).symm.trans Ψ).trans (centralizerConjEquiv d b)

theorem PartnerElts.of_conj {a b a' b' : Cr} (h : PartnerElts a b) (ha : IsConj a a')
    (hb : IsConj b b') : PartnerElts a' b' := by
  obtain ⟨Ψ, h1, h2⟩ := h
  obtain ⟨c, rfl⟩ := isConj_iff.1 ha
  obtain ⟨d, rfl⟩ := isConj_iff.1 hb
  have e1 : (centralizerConjEquiv c a).symm (selfC (c * a * c⁻¹)) = selfC a := by
    apply Subtype.ext
    show c⁻¹ * (c * a * c⁻¹) * c = a
    group
  have e2 : (centralizerConjEquiv c a).symm (centralC rCr_mem_center (c * a * c⁻¹)) =
      centralC rCr_mem_center a := by
    apply Subtype.ext
    show c⁻¹ * rCr * c = rCr
    have := conj_rCr c⁻¹
    rwa [inv_inv] at this
  refine ⟨conjTransport Ψ c d, ?_, ?_⟩
  · apply Subtype.ext
    show d * (Ψ ((centralizerConjEquiv c a).symm (selfC (c * a * c⁻¹))) : Cr) * d⁻¹ = rCr
    exact (congrArg (fun x => d * x * d⁻¹)
      ((congrArg (fun x => (Ψ x : Cr)) e1).trans (congrArg Subtype.val h1))).trans (conj_rCr d)
  · apply Subtype.ext
    show d * (Ψ ((centralizerConjEquiv c a).symm (centralC rCr_mem_center (c * a * c⁻¹))) : Cr) *
      d⁻¹ = d * b * d⁻¹
    exact congrArg (fun x => d * x * d⁻¹)
      ((congrArg (fun x => (Ψ x : Cr)) e2).trans (congrArg Subtype.val h2))

theorem PartnerPair.iff (i j : ℕ) : PartnerPair i j ↔ PartnerElts (rep i) (rep j) := Iff.rfl

theorem PartnerElts.card_eq {a b : Cr} (h : PartnerElts a b) :
    Nat.card (Subgroup.centralizer ({a} : Set Cr)) =
      Nat.card (Subgroup.centralizer ({b} : Set Cr)) := by
  obtain ⟨Ψ, -, -⟩ := h
  exact Nat.card_congr Ψ.toEquiv

end CFSG.RankThree.Co2
