module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSat
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRM6Order
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMWit
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoPThree

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Main


theorem ggQTwoRMInputOn_of_inputs {R : ℕ → Prop} (hR : ∀ m, R m → 6 ≤ m)
    (hSM : GGQTwoDSelModuleInputOn R) (hBase : GGQTwoDRMBaseInputOn R)
    (hStab : GGQTwoDRMStabInputOn R) (hZS : ZS.UseInput) : GGQTwoRMInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y K' hK'
  have hm6 : 6 ≤ m := hR m hm
  have hp : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hcfg' : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  obtain ⟨β, hβ⟩ := hSM G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  obtain ⟨hx, hAL, hfix⟩ := hBase G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  obtain ⟨hS, hsat⟩ := hStab G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hx β hβ
  have hsel := qtwoD_image_eq (by omega) hM β hβ
  obtain ⟨hC, hcomm⟩ := qtwoD_fix_com hcfg' (by omega) β hsel
  have hm1 : 1 ≤ m - 1 := by omega
  have hALW : GGWeylReflectionGroup 3 (ggAutomizer L Bs) := by
    rcases hAL with hA | hD
    · exact ⟨Fin (m - 1), CoxeterMatrix.A (m - 1),
        Or.inl ⟨m - 1, Equiv.refl _, hm1, Or.inl rfl⟩, hA⟩
    · exact ⟨Fin (m - 1), ggCoxeterMatrixD (m - 1),
        Or.inl ⟨m - 1, Equiv.refl _, hm1, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩, hD⟩
  have hJr : ∃ r ∈ ggAutomizer L Bs, GGIsReflection 3 r := by
    rcases hAL with ⟨f, hf⟩ | ⟨f, hf⟩
    · exact ⟨_, (f ((CoxeterMatrix.A (m - 1)).simple ⟨0, by omega⟩)).2, hf _⟩
    · exact ⟨_, (f ((ggCoxeterMatrixD (m - 1)).simple ⟨0, by omega⟩)).2, hf _⟩
  have hdim3 : 3 ≤ Module.finrank (ZMod 3)
      (ggLinCom (qTwoBarA B Bs L D J x β : Set (DVec m ≃ₗ[ZMod 3] DVec m))) := by
    rw [hcomm, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨U, Abar, ρ, hDat, hU⟩ := qTwoD_barData hcfg' hALW hJr hC β hdim3
  have hUtop : U = ⊤ := hU.trans hcomm
  have hfin : Module.finrank (ZMod 3) U = m := by
    rw [hUtop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hup := qTwoDRM_actionCard_le hx hS hDat
  rw [hfin] at hup
  have hrefl : ∃ t ∈ Abar, ZS.IsRefl 3 t := by
    obtain ⟨r, hrA, hrr⟩ := hJr
    have hle : ggAutomizer L Bs ≤ ggAInf 3 B Bs x L D J := le_sup_left
    have hrI : r ∈ ggAInf 3 B Bs x L D J := hle hrA
    exact ⟨_, (ρ ⟨r, hrI⟩).2, (hDat.2.2.2.2.2.1 ⟨r, hrI⟩).mp hrr⟩
  have : Finite ↥U := Subtype.finite
  have : Module.Finite (ZMod 3) ↥U := Module.Finite.of_finite
  have hFam : ZS.Family 3 Abar :=
    hZS (p := 3) (U := ↥U) (A := Abar) (by norm_num) hDat.1 hDat.2.1 hDat.2.2.1
  have hW : GGWeylReflectionGroup 3 (ggAInf 3 B Bs x L D J) :=
    ggSecFive_weyl_of_linWeyl hDat (qTwoD_family_linWeyl_of_card hm6 hfin hDat hrefl hup hFam)
  have hSat := qtwoD_saturation hcfg' (by omega) hALW β hsel hx hsat
  have hcardBs : Nat.card ↥Bs = 3 ^ m := card_bs_of_module β
  rcases hAL with hA | hD
  · refine qTwoD_rm2 hcfg' (qTwoD_witness hcfg' hx (ιL := Fin (m - 1))
      (ML := CoxeterMatrix.A (m - 1)) (Or.inl ⟨m - 1, Equiv.refl _, by omega, rfl⟩) hA hfix
      ?_ hW hSat) y K' hK'
    rw [hcardBs, Fintype.card_fin, Nat.sub_add_cancel (by omega)]
  · refine qTwoD_rm2 hcfg' (qTwoD_witness hcfg' hx (ιL := Fin (m - 1))
      (ML := ggCoxeterMatrixD (m - 1)) (Or.inr ⟨m - 1, Equiv.refl _, by omega, rfl⟩) hD hfix
      ?_ hW hSat) y K' hK'
    rw [hcardBs, Fintype.card_fin, Nat.sub_add_cancel (by omega)]

theorem ggQTwoRMInput_of_inputs (hSM : GGQTwoDSelModuleInput) (hBase : GGQTwoDRMBaseInput)
    (hStab : GGQTwoDRMStabInput) (hZS : ZS.UseInput) : GGQTwoRMInput :=
  ggQTwoRMInputOn_of_inputs (R := fun m => 7 ≤ m) (fun _ hm => by omega) hSM hBase hStab hZS

end Main

end CFSG.StandardType.QTwo

end
