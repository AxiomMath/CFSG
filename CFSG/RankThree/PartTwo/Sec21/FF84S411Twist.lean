module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Dict
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG}

@[expose] noncomputable def twistE (e : ↥S ≃* Multiplicative F6) (g : OmG) : ↥S ≃* Multiplicative F6 :=
  e.trans (AddEquiv.toMultiplicative (((g⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6).toAddEquiv))

@[expose] noncomputable def twistPsi (ψ : ↥(Nor S) →* OmG) (g : OmG) : ↥(Nor S) →* OmG :=
  (MulAut.conj g⁻¹).toMonoidHom.comp ψ

theorem toAdd_twistE (g : OmG) (x : ↥S) :
    Multiplicative.toAdd (twistE e g x) = g⁻¹ • Multiplicative.toAdd (e x) := rfl

theorem twistPsi_apply (g : OmG) (n : ↥(Nor S)) : twistPsi ψ g n = g⁻¹ * ψ n * g := by
  simp [twistPsi, MulAut.conj_apply]

theorem OmSet.twist (H : OmSet S e ψ) (g : OmG) : OmSet S (twistE e g) (twistPsi ψ g) where
  surj := by
    intro h
    obtain ⟨n, hn⟩ := H.surj (g * h * g⁻¹)
    refine ⟨n, ?_⟩
    rw [twistPsi_apply, hn]
    group
  ker := by
    ext n
    rw [MonoidHom.mem_ker, twistPsi_apply, ← H.ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg (fun x => g * x * g⁻¹) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      group
  equiv := by
    intro n hn x
    obtain ⟨hx, h⟩ := H.equiv n hn x
    refine ⟨hx, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_twistE, toAdd_ofAdd, twistPsi_apply, toAdd_twistE]
    have h2 := congrArg Multiplicative.toAdd h
    rw [toAdd_ofAdd] at h2
    show g⁻¹ • Multiplicative.toAdd (e ⟨n * (x : G) * n⁻¹, hx⟩) =
      (g⁻¹ * ψ ⟨n, hn⟩ * g) • (g⁻¹ • Multiplicative.toAdd (e x))
    rw [h2, mul_smul, mul_smul, smul_inv_smul]
    rfl
  hq := by
    intro x hx
    rw [toAdd_twistE]
    have : qMinus (g⁻¹ • Multiplicative.toAdd (e x)) = qMinus (Multiplicative.toAdd (e x)) :=
      qMinus_apply_of_mem (g⁻¹).2 _
    rw [this]
    exact H.hq x hx

theorem exists_twist (H : OmSet S e ψ) {s t : ↥S}
    (hqs : qMinus (Multiplicative.toAdd (e s)) = 1) (hqt : qMinus (Multiplicative.toAdd (e t)) = 0)
    (hqst : qMinus (Multiplicative.toAdd (e s) + Multiplicative.toAdd (e t)) = 0)
    (ht0 : Multiplicative.toAdd (e t) ≠ 0) :
    ∃ (e' : ↥S ≃* Multiplicative F6) (ψ' : ↥(Nor S) →* OmG), OmSet S e' ψ' ∧
      Multiplicative.toAdd (e' s) = sig0 ∧ Multiplicative.toAdd (e' t) = tau0 := by
  obtain ⟨g, hgs, hgt⟩ := om_pair_trans hqs hqt hqst ht0
  refine ⟨twistE e g, twistPsi ψ g, H.twist g, ?_, ?_⟩
  · rw [toAdd_twistE, ← hgs, inv_smul_smul]
  · rw [toAdd_twistE, ← hgt, inv_smul_smul]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
