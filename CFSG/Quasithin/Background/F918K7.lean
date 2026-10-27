module

public import CFSG.Quasithin.Background.F918K3
public import CFSG.Quasithin.Background.F918K4
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem NSGroup.not_asB45Table
    (hX : NSGroup ↥L) (hns : ¬ IsShapeGroup ↥L) (ht : AsB45Table G L) : False := by
  have := hX.isSimple
  have := hX.isSimple.toNontrivial
  have hnc := hX.noncomm
  have hcard := hX.card
  rcases ht with ⟨⟨π, hR⟩, -⟩ | ⟨m, hm, horth, -⟩ | ⟨m, ⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨f, hsz, -⟩ | ⟨m, hm, ⟨K, _, _, _, hK, π, hR⟩, -⟩ | ⟨⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨⟨eY, heY, hw, π, hR⟩, -⟩ | ⟨⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩, -⟩ |
      ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨h2324, -⟩
  ·
    have hd : Nat.card ↥L ∣ Nat.card ↥(alternatingGroup (Fin 7)) :=
      Subgroup.card_dvd_of_surjective hR.1
    rw [card_alt 7 (by norm_num)] at hd
    exact not_nsCard_of_dvd_smooth (a := 3) (b := 2) (c := 1) (d := 1)
      (by norm_num [Nat.factorial] at hd ⊢; exact hd) hcard
  ·
    obtain ⟨K, _, _, _, hK, π, hR⟩ := horth
    exact hns (isShapeGroup_of_surjective_statedSL_two (X := ↥L) (by omega) hK π hR.1)
  · exact hX.false_of_surjective_su3 hK π hR.1
  ·
    obtain ⟨a, K, _, _, ha, hf, hK, ⟨e⟩⟩ := hsz.exists_equiv
    exact hns (Or.inr (Or.inl ⟨f, rfl, a, ha, K, inferInstance, inferInstance, hf, hK, ⟨e.symm⟩⟩))
  · exact hX.false_of_surjective_sl3 hm hK π hR.1
  · exact hX.false_of_surjective_g2derived hK π hR.1
  · exact hX.false_of_surjective_m12 heY hw π hR.1
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  · exact hX.false_of_surjective_m22 hxy π hR.1
  · exact hX.false_of_surjective_m22 hxy π hR.1
  · rcases h2324 with ⟨x, π, hR⟩ | ⟨x, π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩
    · exact hX.false_of_surjective_m23 x π hR.1
    · exact hX.false_of_surjective_m23 x π hR.1
    all_goals exact hX.false_of_surjective_m24 π hR.1

theorem NSGroup.not_asB45Part3
    (hX : NSGroup ↥L) (h3 : AsB45Part3 G L) : False := by
  obtain ⟨-, -, ⟨a, ha, K, _, _, _, hK, π, hR⟩ | ⟨hJ2, -, -⟩⟩ := h3
  · exact hX.false_of_surjective_sp4 ha hK π hR.1
  · obtain ⟨e⟩ := hJ2
    exact hX.false_of_equiv_j2 e

end CFSG.Quasithin
