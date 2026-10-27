module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux1
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

open CFSG.Open
open scoped Pointwise
open CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ]

theorem exists_zpowers_of_isCyclic_quotient {A H : Subgroup Γ} [IsMulCommutative A]
    (h : IsCyclic (A ⧸ H.subgroupOf A)) : ∃ a ∈ A, A ≤ H ⊔ Subgroup.zpowers a := by
  obtain ⟨g, hg⟩ := h.exists_generator
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨(a : Γ), a.2, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := hg (QuotientGroup.mk ⟨z, hz⟩)
  have h1 : (QuotientGroup.mk (a ^ k) : A ⧸ H.subgroupOf A) = QuotientGroup.mk ⟨z, hz⟩ := by
    rw [QuotientGroup.mk_zpow]; exact hk
  have h2 := (QuotientGroup.eq (s := H.subgroupOf A)).mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : z = (a : Γ) ^ k * (((a : Γ) ^ k)⁻¹ * z) := by group
  rw [h3]
  refine mul_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _)) (Subgroup.mem_sup_left ?_)
  simpa using h2

variable [Finite Γ]

theorem le_wSub_sup_cenIn {p : ℕ} (hp : p.Prime) {A B Y : Subgroup Γ} (hA : IsElemAbelian p A)
    (hAY : Admits A Y) (hcop : Nat.Coprime p (Nat.card Y)) (hB : B ≤ A) :
    Y ≤ wSub A B Y ⊔ cenIn Y (B : Set Γ) := by
  have : IsMulCommutative A := hA.1
  have hAp : IsPGroup p A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  have hgen := iSup_centralizer_cyclic_quotient hp hAp hAY hcop
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun H hHA => iSup_le fun hcyc => ?_
  obtain ⟨a, haA, hAa⟩ := exists_zpowers_of_isCyclic_quotient hcyc
  have hHX : H ≤ Subgroup.centralizer
      ((Y ⊓ Subgroup.centralizer (H : Set Γ) : Subgroup Γ) : Set Γ) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 h hh).symm
  rcases le_wSub_or_le_cenIn_of_cyclic hp hA hHA hHX hB haA hAa with h | h
  · exact h.trans ((wSub_mono A B inf_le_left).trans le_sup_left)
  · exact h.trans ((cenIn_mono_left inf_le_left _).trans le_sup_right)

theorem subset_mul_of_abelian {p : ℕ} (hp : p.Prime) {A B Y : Subgroup Γ} (hA : IsElemAbelian p A)
    (hAY : Admits A Y) (hcop : Nat.Coprime p (Nat.card Y)) (hB : B ≤ A)
    (hab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) :
    (Y : Set Γ) ⊆ (wSub A B Y : Set Γ) * (cenIn Y (B : Set Γ) : Set Γ) ∧
      (Y : Set Γ) ⊆ (cenIn Y (B : Set Γ) : Set Γ) * (wSub A B Y : Set Γ) := by
  have hle := le_wSub_sup_cenIn hp hA hAY hcop hB
  have hcomm : ∀ x ∈ wSub A B Y, ∀ z ∈ cenIn Y (B : Set Γ), Commute x z := fun x hx z hz =>
    hab x (wSub_le A B Y hx) z (cenIn_le_left _ _ hz)
  constructor
  · intro y hy
    obtain ⟨w, hw, z, hz, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp (hle hy)
    exact ⟨w, hw, z, hz, rfl⟩
  · intro y hy
    obtain ⟨w, hw, z, hz, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp (hle hy)
    exact ⟨z, hz, w, hw, (hcomm w hw z hz).eq.symm⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
