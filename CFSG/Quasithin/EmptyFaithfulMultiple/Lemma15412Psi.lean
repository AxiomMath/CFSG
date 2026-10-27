module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Class

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem oTwoUpper_sup_eq_self {A B : Subgroup G} (hA : A = oTwoUpper A)
    (hB : B = oTwoUpper B) : A ⊔ B = oTwoUpper (A ⊔ B) := by
  refine le_antisymm (sup_le ?_ ?_) (oTwoUpper_le _)
  · calc A = oTwoUpper A := hA
      _ ≤ oTwoUpper (A ⊔ B) := oTwoUpper_mono le_sup_left
  · calc B = oTwoUpper B := hB
      _ ≤ oTwoUpper (A ⊔ B) := oTwoUpper_mono le_sup_right

namespace Setup

variable (h : Setup T M)
include h

noncomputable abbrev ps (D : Subgroup (MulAut (IntMod (VZ T M) h.elem))) : Subgroup G :=
  psi h.elem h.le_normalizer D

theorem ps_le (D : Subgroup (MulAut (IntMod (VZ T M) h.elem))) : h.ps D ≤ M :=
  psi_le h.elem h.le_normalizer D

theorem autI_ps {D : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hDM : D ≤ autI h.elem M)
    (hD : ∀ x ∈ D, Odd (orderOf x)) : autI h.elem (h.ps D) = D :=
  autI_psi h.elem h.le_normalizer hDM hD

theorem isPGroup_inf_ps (D : Subgroup (MulAut (IntMod (VZ T M) h.elem))) :
    IsPGroup 2 ↥(h.ps D ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
  h.isPGroup_inf.to_le (inf_le_inf_right _ (h.ps_le D))

theorem relIndex_ps {D : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hDM : D ≤ autI h.elem M)
    (hD : ∀ x ∈ D, Odd (orderOf x)) (hodd : Odd (Nat.card D)) :
    (pCoreOf 2 (h.ps D)).relIndex (h.ps D) = Nat.card D := by
  have hN : h.ps D ≤ Subgroup.normalizer (VZ T M : Set G) := (h.ps_le D).trans h.le_normalizer
  rw [relIndex_pCoreOf_eq h.elem hN (by rwa [h.autI_ps hDM hD]) (h.isPGroup_inf_ps D),
    h.autI_ps hDM hD]

theorem pCoreOf_ps {D : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hDM : D ≤ autI h.elem M)
    (hD : ∀ x ∈ D, Odd (orderOf x)) (hodd : Odd (Nat.card D)) :
    pCoreOf 2 (h.ps D) = h.ps D ⊓ Subgroup.centralizer (VZ T M : Set G) :=
  pCoreOf_eq_inf_centralizer h.elem ((h.ps_le D).trans h.le_normalizer)
    (by rwa [h.autI_ps hDM hD]) (h.isPGroup_inf_ps D)

theorem pow_three_mem_ps {D : Subgroup (MulAut (IntMod (VZ T M) h.elem))}
    (hDM : D ≤ autI h.elem M) (hD : ∀ x ∈ D, Odd (orderOf x)) (hodd : Odd (Nat.card D))
    (h3 : ∀ x ∈ D, x ^ 3 = 1) {x : G} (hx : x ∈ h.ps D) : x ^ 3 ∈ pCoreOf 2 (h.ps D) := by
  rw [h.pCoreOf_ps hDM hD hodd]
  refine ⟨(h.ps D).pow_mem hx 3, ?_⟩
  have hxM := h.ps_le D hx
  have hxD : convI h.elem ⟨x, h.le_normalizer hxM⟩ ∈ D := by
    rw [← h.autI_ps hDM hD]
    exact h.convI_mem_autI' hx hxM
  have h1 := h3 _ hxD
  rw [← map_pow] at h1
  exact (convI_eq_one_iff h.elem ⟨x ^ 3, _⟩).1 h1

theorem ps_sup {D₁ D₂ : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (h₁ : D₁ ≤ autI h.elem M)
    (h₂ : D₂ ≤ autI h.elem M) (ho₁ : ∀ x ∈ D₁, Odd (orderOf x))
    (ho₂ : ∀ x ∈ D₂, Odd (orderOf x)) : h.ps (D₁ ⊔ D₂) = h.ps D₁ ⊔ h.ps D₂ := by
  have hN₁ : h.ps D₁ ≤ Subgroup.normalizer (VZ T M : Set G) := (h.ps_le D₁).trans h.le_normalizer
  have hN₂ : h.ps D₂ ≤ Subgroup.normalizer (VZ T M : Set G) := (h.ps_le D₂).trans h.le_normalizer
  have hle : h.ps D₁ ⊔ h.ps D₂ ≤ M := sup_le (h.ps_le D₁) (h.ps_le D₂)
  have hO := oTwoUpper_sup_eq_self (psi_eq_oTwoUpper h.elem h.le_normalizer D₁)
    (psi_eq_oTwoUpper h.elem h.le_normalizer D₂)
  have hC : M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤
      Subgroup.normalizer ((h.ps D₁ ⊔ h.ps D₂ : Subgroup G) : Set G) :=
    B2F.le_normalizer_sup (inf_centralizer_le_normalizer_psi h.elem h.le_normalizer D₁)
      (inf_centralizer_le_normalizer_psi h.elem h.le_normalizer D₂)
  have e := eq_psi_autI h.elem h.le_normalizer hle hO hC h.isPGroup_inf
  rw [autI_sup h.elem hN₁ hN₂, h.autI_ps h₁ ho₁, h.autI_ps h₂ ho₂] at e
  exact e.symm

theorem commutator_thompsonJ_ps {D : Subgroup (MulAut (IntMod (VZ T M) h.elem))}
    (hDM : D ≤ autI h.elem M) (hD : ∀ x ∈ D, Odd (orderOf x))
    (hJN : thompsonJ T ≤ Subgroup.normalizer (h.ps D : Set G))
    (hDJ : ⁅D, autI h.elem (thompsonJ T)⁆ = D) : ⁅h.ps D, thompsonJ T⁆ = h.ps D := by
  set X := h.ps D with hX
  set N := Subgroup.normalizer (VZ T M : Set G)
  have hJM : thompsonJ T ≤ M := (thompsonJ_le_self T).trans h.T_le
  have hXM : X ≤ M := h.ps_le D
  have hCle : ⁅X, thompsonJ T⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx j hj
    rw [commutatorElement_def]
    have h0 : j * x⁻¹ * j⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hJN hj) x⁻¹).mp (X.inv_mem hx)
    have := X.mul_mem hx h0
    simpa [mul_assoc] using this
  refine le_antisymm hCle ?_
  have hDle : D ≤ autI h.elem ⁅X, thompsonJ T⁆ := by
    rw [← hDJ, Subgroup.commutator_le]
    intro d hd j' hj'
    rw [← h.autI_ps hDM hD] at hd
    obtain ⟨x, hx, hxN, rfl⟩ := h.exists_mem_of_mem_autI hd
    obtain ⟨j, hj, hjN, rfl⟩ := h.exists_mem_of_mem_autI hj'
    have hcN : ⁅x, j⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hxN hjN) (N.inv_mem hxN)) (N.inv_mem hjN)
    have e : (⟨⁅x, j⁆, hcN⟩ : N) = ⁅(⟨x, hxN⟩ : N), ⟨j, hjN⟩⁆ := rfl
    have hmem := convI_mem_autI h.elem (Subgroup.commutator_mem_commutator hx hj) hcN
    rw [e, map_commutatorElement] at hmem
    exact hmem
  have hXO : X = oTwoUpper X := psi_eq_oTwoUpper h.elem h.le_normalizer D
  refine hXO.le.trans (oTwoUpper_le_of_pow_mem fun x hx => ?_)
  have hxM := hXM hx
  have hxD : convI h.elem ⟨x, h.le_normalizer hxM⟩ ∈ autI h.elem ⁅X, thompsonJ T⁆ := by
    apply hDle
    rw [← h.autI_ps hDM hD]
    exact h.convI_mem_autI' hx hxM
  obtain ⟨c, hc, q, hq, rfl⟩ := exists_mul_of_convI_mem h.elem h.le_normalizer
    (hCle.trans hXM) hxM hxD
  obtain ⟨k, hk⟩ := h.isPGroup_inf ⟨q, hq⟩
  have hk' : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hqX : q ∈ X := by
    have := X.mul_mem (X.inv_mem (hCle hc)) hx
    simpa using this
  have hqN : q ∈ Subgroup.normalizer ((⁅X, thompsonJ T⁆ : Subgroup G) : Set G) :=
    A4.mem_normalizer_commutator (Subgroup.le_normalizer hqX)
      (normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer (h.inf_le_T hq)))
  obtain ⟨c', hc', hpow⟩ := A4.exists_pow_mul_eq hc hqN (2 ^ k)
  exact ⟨k, by rw [hpow, hk', mul_one]; exact hc'⟩

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
