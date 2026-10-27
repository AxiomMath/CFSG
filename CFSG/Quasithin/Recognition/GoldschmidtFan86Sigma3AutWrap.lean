module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Split

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup

structure S4Data {H : Type*} [Group H] (S : Subgroup H) (x : H) : Prop where
  gen : S ⊔ Subgroup.zpowers x = ⊤
  ex : ∃ V D Q0 : Subgroup H, IsKleinFour ↥V ∧ V ≤ D ∧ D ≤ S ∧ Q0 ≤ S ∧
    (∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d) ∧ D ⊓ Q0 = ⊥ ∧ D ⊔ Q0 = S ∧
    Nonempty (↥D ≃* DihedralGroup 4) ∧ (∀ q ∈ Q0, x * q = q * x) ∧ (∀ v ∈ V, x * v * x⁻¹ ∈ V)

section Transport

variable {H : Type*} [Group H] {S V D Q0 : Subgroup H}

theorem subgroupOf_comm (hc : ∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d) :
    ∀ a ∈ D.subgroupOf S, ∀ b ∈ Q0.subgroupOf S, a * b = b * a := fun a ha b hb =>
  Subtype.ext (hc a ha b hb)

theorem subgroupOf_disjoint (hDQ : D ⊓ Q0 = ⊥) : D.subgroupOf S ⊓ Q0.subgroupOf S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : H) ∈ D ⊓ Q0 := ⟨hx.1, hx.2⟩
  rw [hDQ, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (Subtype.ext h1)

theorem subgroupOf_sup (hDS : D ≤ S) (hQS : Q0 ≤ S) (h : D ⊔ Q0 = S) :
    D.subgroupOf S ⊔ Q0.subgroupOf S = ⊤ := by
  rw [← Subgroup.subgroupOf_sup hDS hQS, h, Subgroup.subgroupOf_self]

noncomputable def splitEquiv (hDS : D ≤ S) (hQS : Q0 ≤ S) (hc : ∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d)
    (hDQ : D ⊓ Q0 = ⊥) (h : D ⊔ Q0 = S) (eD : ↥D ≃* DihedralGroup 4) :
    ↥S ≃* DihedralGroup 4 × ↥(Q0.subgroupOf S) :=
  (prodEquivOfSplit (D.subgroupOf S) (Q0.subgroupOf S) (subgroupOf_comm hc)
    (subgroupOf_disjoint hDQ) (subgroupOf_sup hDS hQS h)).symm.trans
    (MulEquiv.prodCongr ((Subgroup.subgroupOfEquivOfLe hDS).trans eD) (MulEquiv.refl _))

theorem splitEquiv_symm_apply (hDS : D ≤ S) (hQS : Q0 ≤ S) (hc : ∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d)
    (hDQ : D ⊓ Q0 = ⊥) (h : D ⊔ Q0 = S) (eD : ↥D ≃* DihedralGroup 4)
    (a : DihedralGroup 4) (b : ↥(Q0.subgroupOf S)) :
    ((splitEquiv hDS hQS hc hDQ h eD).symm (a, b) : H) =
      ((eD.symm a : ↥D) : H) * ((b : S) : H) := by
  show (((prodEquivOfSplit (D.subgroupOf S) (Q0.subgroupOf S) (subgroupOf_comm hc)
    (subgroupOf_disjoint hDQ) (subgroupOf_sup hDS hQS h))
    (((Subgroup.subgroupOfEquivOfLe hDS).trans eD).symm a, b) : ↥S) : H) = _
  rw [prodEquivOfSplit_apply]
  rfl

theorem splitEquiv_apply_of_mem (hDS : D ≤ S) (hQS : Q0 ≤ S)
    (hc : ∀ d ∈ D, ∀ q ∈ Q0, d * q = q * d)
    (hDQ : D ⊓ Q0 = ⊥) (h : D ⊔ Q0 = S) (eD : ↥D ≃* DihedralGroup 4) (v : ↥S) (hv : (v : H) ∈ D) :
    splitEquiv hDS hQS hc hDQ h eD v = (eD ⟨v, hv⟩, 1) := by
  refine (MulEquiv.eq_symm_apply _).1 ?_
  apply Subtype.ext
  rw [splitEquiv_symm_apply]
  simp

end Transport

end CFSG.Quasithin.Fan86.Sigma3
