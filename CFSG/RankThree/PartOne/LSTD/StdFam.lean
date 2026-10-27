module

public import CFSG.RankThree.PartOne.LSTD.HyperEq
public import CFSG.RankThree.PartOne.LSTD.PermW

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

variable {f : ℕ} {K : Type} [Field K]

section Std

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)

include h5 in
theorem std_model (hf2 : 2 ≤ f) :
    CTP.StdTriangle f (Jfun hU 0 1 ⊔ Jfun hU 1 2) (fun a b => Jfun hU (e3 a) (e3 b))
      (torusBar K f ⊓ (Jfun hU 0 1 ⊔ Jfun hU 1 2)) := by
  let e1 : ↥(Jfun hU 0 1 ⊔ Jfun hU 1 2) ≃* ↥(theta3 hU).range :=
    MulEquiv.subgroupCongr (Kbar_eq_range hU hf2)
  let e2 : ↥(unitarySU 2 f K 3) ≃* ↥(theta3 hU).range :=
    MonoidHom.ofInjective (theta3_injective hU)
  let φ : ↥(Jfun hU 0 1 ⊔ Jfun hU 1 2) ≃* ↥(unitarySU 2 f K 3) := e1.trans e2.symm
  have hφ : ∀ x : ↥(Jfun hU 0 1 ⊔ Jfun hU 1 2), theta3 hU (φ x) = (x : StatedProj _) :=
    fun x => congrArg Subtype.val (e2.apply_symm_apply (e1 x))
  refine ⟨K, inferInstance, hU, φ, fun a b hab => ⟨?_, fun x => ?_⟩, inf_le_right, fun x => ?_⟩
  · exact le_of_le_of_eq (Jfun_e3_le_range hU hab) (Kbar_eq_range hU hf2).symm
  · rw [← hφ x]
    exact theta3_mem_Jfun_iff hU hab (φ x)
  · have hx : (x : StatedProj (unitarySU 2 f K 5)) ∈
        torusBar K f ⊓ (Jfun hU 0 1 ⊔ Jfun hU 1 2) ↔ (x : StatedProj (unitarySU 2 f K 5)) ∈
          torusBar K f := ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    rw [hx, ← hφ x]
    exact theta3_mem_torusBar_iff hU h5 (φ x)

end Std

noncomputable def stdLFam [Finite K] (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) {b : StatedProj (unitarySU 2 f K 5)}
    (hb : b ∈ torusBar K f ⊓ Jfun hU 3 4) (hb1 : b ≠ 1) :
    LFam (⊤ : Subgroup (StatedProj (unitarySU 2 f K 5))) (torusBar K f) f b
      (Jfun hU 0 1 ⊔ Jfun hU 1 2) where
  W := Wmodel hU
  J := Jfun hU
  W_L _ := Subgroup.mem_top _
  W_B σ := Wmodel_mem_normalizer hU h5 σ
  J_symm := Jfun_symm hU
  J_equiv := Jfun_equiv_model hU
  J_model _ _ hab := Jfun_model hU (two_le_of_five_dvd h5) hab
  B_elem := isElementaryAbelian_torusBar hU h5
  B_card := card_torusBar hU h5 hζ
  line_card _ _ hab := by
    obtain ⟨ζ, hζ'⟩ := hζ
    exact card_torusBar_inf_Jfun hU h5 hζ' hab
  hyper_ne _ _ _ _ hab hde hne := by
    obtain ⟨ζ, hζ'⟩ := hζ
    exact hyper_ne_model hU h5 hζ' hab hde hne
  B_gen := le_antisymm (torusBar_le_lines hU h5)
    (sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left)
  disj _ _ _ _ hab hde had hae hbd hbe :=
    Jfun_le_centralizer_of_disjoint hU hab hde had hae hbd hbe
  K_eq := rfl
  b_mem := hb
  b_ne := hb1
  BK_card := card_torusBar_inf_Kbar hU h5 (two_le_of_five_dvd h5) hζ
  hyper_eq _ _ hxy := hyper_eq_model hU h5 (two_le_of_five_dvd h5) hζ hb hb1 hxy
  std := std_model hU h5 (two_le_of_five_dvd h5)

end CFSG.RankThree.PartOne.LSTD
