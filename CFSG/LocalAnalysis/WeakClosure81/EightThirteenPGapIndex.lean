module

import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem index_ker_dvd_168 {B : Type} [Group B] {E : Type} [Group E] (hE : ElemAbOrderEight E)
    (W : Subgroup (MulAut E)) {X : Type} [Group X] (ψ : ↥W →* X)
    (hψ : Function.Surjective ψ) (φ : B →* X) : φ.ker.index ∣ 168 := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.1]; norm_num)
  have h168 : Nat.card (MulAut E) = 168 :=
    CFSG.GF2Type.Aschbacher1976Full.HS.card_mulAut_eq_168 hE.1 hE.2.1
      (fun x => hE.2.2 x)
  haveI : Finite (MulAut E) := Nat.finite_of_card_ne_zero (by rw [h168]; norm_num)
  haveI : Finite X := Finite.of_surjective ψ hψ
  rw [Subgroup.index_ker]
  have h1 : Nat.card φ.range ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card X ∣ Nat.card ↥W := Subgroup.card_dvd_of_surjective hψ
  have h3 : Nat.card ↥W ∣ Nat.card (MulAut E) := Subgroup.card_subgroup_dvd_card _
  exact (h1.trans (h2.trans h3)).trans (h168 ▸ dvd_rfl)

end CFSG.LocalAnalysis.WeakClosure81

end
