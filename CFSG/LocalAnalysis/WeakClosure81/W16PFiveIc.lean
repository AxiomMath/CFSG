module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa
public import CFSG.Quasithin.EmptyFaithful.S146Final

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem conjClosure_commutator_mem_of_normalizer {A B C H : Subgroup G}
    (hBH : B ≤ H) (hAnorm : H ≤ Subgroup.normalizer (A : Set G))
    (hCnorm : H ≤ Subgroup.normalizer (C : Set G))
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ C) :
    ∀ k ∈ conjClosure B H, ∀ a ∈ A, a * k * a⁻¹ * k⁻¹ ∈ C := by
  have hKH : conjClosure B H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun x hx y hy =>
      H.mul_mem (H.mul_mem hx (hBH hy)) (H.inv_mem hx)
  intro k hk
  rw [CFSG.Quasithin.conjClosure] at hk
  refine Subgroup.closure_induction (p := fun g _ => ∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ C)
    ?_ ?_ ?_ ?_ hk
  · intro x hx a ha
    obtain ⟨h, hh, b, hb, rfl⟩ := hx
    have ha' : h⁻¹ * a * h ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp (hAnorm hh) a).1 ha
    have h1 : h * ((h⁻¹ * a * h) * b * (h⁻¹ * a * h)⁻¹ * b⁻¹) * h⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hCnorm hh) _).1 (hcomm _ ha' b hb)
    have h2 : a * (h * b * h⁻¹) * a⁻¹ * (h * b * h⁻¹)⁻¹ =
        h * ((h⁻¹ * a * h) * b * (h⁻¹ * a * h)⁻¹ * b⁻¹) * h⁻¹ := by
      group
    rw [h2]
    exact h1
  · intro a ha
    simpa using C.one_mem
  · intro x y hx hy ihx ihy a ha
    have hxH : x ∈ H := hKH hx
    have h1 : a * x * a⁻¹ * x⁻¹ ∈ C := ihx a ha
    have h2 : x * (a * y * a⁻¹ * y⁻¹) * x⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hCnorm hxH) _).1 (ihy a ha)
    have h3 : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
        (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by
      group
    rw [h3]
    exact C.mul_mem h1 h2
  · intro x hx ih a ha
    rw [inv_inv]
    have hxH : x ∈ H := hKH hx
    have h1 : (a * x * a⁻¹ * x⁻¹)⁻¹ ∈ C := C.inv_mem (ih a ha)
    have h2 : x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp (hCnorm hxH) _).1 h1
    have h3 : a * x⁻¹ * a⁻¹ * x = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by
      group
    rw [h3]
    exact h2

theorem IsMinFam16.conjClosure_conjClosure_eq (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    conjClosure V (conjClosure V H) = conjClosure V H := by
  have hsup : S ⊔ conjClosure V H = H := IsMinFam16.sup_conjClosure_eq h1 hS h hH hV
  have hSV : S ≤ Subgroup.normalizer (V : Set G) :=
    h.S_le_M.trans (le_of_eq h.hyp.h6.normalizer_eq.symm)
  have hSK : S ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    hH.1.1.trans (CFSG.Quasithin.le_normalizer_conjClosure V H)
  have h := CFSG.Quasithin.conjClosure_sup_eq_of_normalizes (V := V)
    (A := conjClosure V H) (B := S) hSK hSV
  rw [sup_comm, hsup] at h
  exact h.symm

theorem IsMinFam16.iSub16_eq_conjClosure (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    iSub16 V H = conjClosure (V ⊓ pCoreOf 2 H) (conjClosure V H) := by
  have hsup : S ⊔ conjClosure V H = H := IsMinFam16.sup_conjClosure_eq h1 hS h hH hV
  have hSV : S ≤ Subgroup.normalizer (V : Set G) :=
    h.S_le_M.trans (le_of_eq h.hyp.h6.normalizer_eq.symm)
  have hSO : S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hH.1.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hSZ : S ≤ Subgroup.normalizer (V ⊓ pCoreOf 2 H : Set G) :=
    (le_inf hSV hSO).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := V) (K := pCoreOf 2 H))
  have hSK : S ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    hH.1.1.trans (CFSG.Quasithin.le_normalizer_conjClosure V H)
  have h := CFSG.Quasithin.conjClosure_sup_eq_of_normalizes (V := V ⊓ pCoreOf 2 H)
    (A := conjClosure V H) (B := S) hSK hSZ
  rw [sup_comm, hsup] at h
  unfold iSub16
  exact h

theorem Cex16.comm_mem_iSub16_of_mem_pCoreOf (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) {q k : G}
    (hq : q ∈ pCoreOf 2 (conjClosure V H)) (hk : k ∈ conjClosure V H) :
    q * k * q⁻¹ * k⁻¹ ∈ iSub16 V H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun x hx y hy =>
      H.mul_mem (H.mul_mem hx (hF.1 (h.V_le_S hy))) (H.inv_mem hx)
  have hHK : H ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure V H
  have hA_le_pH : pCoreOf 2 (conjClosure V H) ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (conjClosure V H)).trans hKH)
      (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
        (conjClosure V H)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure V H))
  have hA_le_S : pCoreOf 2 (conjClosure V H) ≤ S :=
    hA_le_pH.trans (h.pCoreOf_le_S h1 hS hF)
  have hV₀_le_I : V₀ ≤ iSub16 V H :=
    (le_inf h.hyp.h6.le (h.V₀_le_pCoreOf h5 hS hF hV)).trans
      (CFSG.Quasithin.le_conjClosure (V ⊓ pCoreOf 2 H) H)
  have hcomm : ∀ a ∈ pCoreOf 2 (conjClosure V H), ∀ b ∈ V,
      a * b * a⁻¹ * b⁻¹ ∈ iSub16 V H :=
    fun a ha b hb => hV₀_le_I (h.comm_mem_V₀ (hA_le_S ha) hb)
  exact conjClosure_commutator_mem_of_normalizer (h.V_le_S.trans hF.1)
    (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjClosure V H)))
    (CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
    hcomm k hk q hq


end CFSG.LocalAnalysis.WeakClosure81

end
