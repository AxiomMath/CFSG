module

public import CFSG.Quasithin.EmptyFaithful.Insp7Final4
public import CFSG.Quasithin.EmptyFaithful.Insp7NumU
public import CFSG.Quasithin.EmptyFaithful.Insp7NumV
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res

import CFSG.Sporadic.Schreier.MathieuOddCoreM11
import CFSG.Sporadic.Schreier.MathieuOddCoreM22
import CFSG.Sporadic.Schreier.MathieuOddCoreM23
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

namespace S143

namespace InspW2

theorem numFactW_m11
    : NumFactW Insp7.M11Fam := by
  refine numFactW_of_not_dvd_aut (fun L _ _ _ ⟨e⟩ hdvd => ?_)
  have hcard : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have hcen : Subgroup.center (NativeSporadic.Carrier .M11) = ⊥ :=
    CFSG.Sporadic.Schreier.m11_center_eq_bot'
  have hA : Nat.card (MulAut L) ≤ 7920 := by
    have h : Nat.card (MulAut (NativeSporadic.Carrier .M11)) ≤
        Nat.card (NativeSporadic.Carrier .M11) := CFSG.Sporadic.Schreier.m11_mulAut_card
    rw [hcard] at h
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact h
  obtain ⟨hZ, hL⟩ := card_quotient_center_of_equiv e hcen
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, Insp7.ker_conj_eq_center, hZ]
  have : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  have hB : Nat.card L ≤ Nat.card (MulAut L) := Nat.card_le_card_of_injective _ hinj
  have hL' : Nat.card L = 7920 := by rw [Nat.card_congr e.toEquiv]; exact hcard
  have hC : Nat.card (MulAut L) = 7920 := by omega
  rw [hC] at hdvd
  exact absurd hdvd (by decide)

theorem numFactW_m22
    : NumFactW Insp7.M22Fam := by
  have : Finite (NativeSporadic.Carrier .M22) := inferInstanceAs (Finite ↥NativeSporadic.M22)
  refine numFactW_of_model_big_inv (X := NativeSporadic.Carrier .M22)
    CFSG.Sporadic.Schreier.m22_center_eq_bot' fun t ht => ?_
  let t' : ↥NativeSporadic.M22 := t
  have h := Insp7.m22_involution_centralizer_card (t' : Equiv.Perm (Fin 22)) t'.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  rw [← map_centralizer_subtype,
    Subgroup.card_map_of_injective (NativeSporadic.M22).subtype_injective] at h
  have h' : Nat.card (Subgroup.centralizer ({t} : Set (NativeSporadic.Carrier .M22))) = 384 :=
    h
  rw [h']
  norm_num

theorem numFactW_m23
    : NumFactW Insp7.M23Fam := by
  have : Finite (NativeSporadic.Carrier .M23) := inferInstanceAs (Finite ↥NativeSporadic.M23)
  refine numFactW_of_model_big_inv (X := NativeSporadic.Carrier .M23)
    CFSG.Sporadic.Schreier.m23_center_eq_bot' fun t ht => ?_
  let t' : ↥NativeSporadic.M23 := t
  have h := Insp7.m23_involution_centralizer_card (t' : Equiv.Perm (Fin 23)) t'.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  rw [← map_centralizer_subtype,
    Subgroup.card_map_of_injective (NativeSporadic.M23).subtype_injective] at h
  have h' : Nat.card (Subgroup.centralizer ({t} : Set (NativeSporadic.Carrier .M23))) = 2688 :=
    h
  rw [h']
  norm_num

open CFSG.ComponentClassification.J2Cover in
theorem numFactW_j2
    : NumFactW Insp7.J2Fam := by
  have h : NumFactW (fun L _ => Nonempty (L ≃* P)) :=
    numFactW_of_model_card_big center_P (by rw [card_P]; norm_num)
  exact numFactW_of_union (G' := fun L _ => Nonempty (L ≃* P)) (H := fun L _ => Nonempty (L ≃* P))
    (fun _ _ ⟨e⟩ => Or.inl ⟨e.trans nativeEquivP⟩) h h

@[expose] def SporNoM12 (L : Type) [Group L] : Prop :=
  Insp7.M11Fam L ∨ Insp7.M22Fam L ∨ Insp7.M23Fam L ∨ Insp7.J2Fam L

theorem numFactW_sporNoM12
    : NumFactW SporNoM12 :=
  numFactW_of_union (G' := Insp7.M11Fam)
    (H := fun L _ => Insp7.M22Fam L ∨ Insp7.M23Fam L ∨ Insp7.J2Fam L) (fun _ _ h => h)
    numFactW_m11
    (numFactW_of_union (G' := Insp7.M22Fam) (H := fun L _ => Insp7.M23Fam L ∨ Insp7.J2Fam L)
      (fun _ _ h => h) numFactW_m22
      (numFactW_of_union (G' := Insp7.M23Fam) (H := Insp7.J2Fam) (fun _ _ h => h)
        numFactW_m23 numFactW_j2))

theorem sporSimple_of_sporSmall
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
        IsSimpleGroup (NativeSporadic.Carrier s))
    {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) (h : Insp7.SporSmall L) :
    Insp7.SporSimple (L ⧸ Subgroup.center L) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := h
  have hc := Insp7.center_eq_pCore_of_simple_quotient hq (hsimple s hs) e
  exact ⟨s, hs, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e⟩⟩

theorem resW_sporSmall
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
        IsSimpleGroup (NativeSporadic.Carrier s))
    (hM12 : ResW Insp7.M12Fam) (hrest : NumFactW SporNoM12) : ResW Insp7.SporSmall :=
  resW_cover (G' := Insp7.SporSimple) (fun _ _ _ hq h => sporSimple_of_sporSmall hsimple hq h)
    (resW_of_union (G' := Insp7.M12Fam) (H := SporNoM12)
      (fun _ _ ⟨s, hs, he⟩ => by
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl he)
        · exact Or.inl he
        · exact Or.inr (Or.inr (Or.inl he))
        · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr he))))
      hM12 (resW_of_numFactW hrest))

end InspW2

end S143

end CFSG.Quasithin
