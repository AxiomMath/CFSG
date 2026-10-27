module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityPermModule

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

@[expose] def triSwap : Equiv.Perm (Fin TwistTag.D4.tag.rank) :=
  (Equiv.swap (1 : Fin 4) 3 : Equiv.Perm (Fin 4))

theorem triSwap_cartan (i j : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.tag.cartan (triSwap i) (triSwap j) = TwistTag.D4.tag.cartan i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem triSwap_mul_self : triSwap * triSwap = 1 := by
  ext i
  fin_cases i <;> rfl

theorem perm_cube : TwistTag.D4.perm * TwistTag.D4.perm * TwistTag.D4.perm = 1 := by
  ext i
  fin_cases i <;> rfl

theorem perm_cartan (i j : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.tag.cartan (TwistTag.D4.perm i) (TwistTag.D4.perm j) =
      TwistTag.D4.tag.cartan i j := TwistTag.D4.cartan_perm i j

section Maps

variable (L : Type) [Field L]

@[expose] noncomputable def triP : ModGL TwistTag.D4.tag L := diagramMap TwistTag.D4 L

@[expose] noncomputable def triN : ModGL TwistTag.D4.tag L := permModuleMap triSwap_cartan L

theorem triP_eq_perm : triP L = permModuleMap perm_cartan L := rfl

theorem permModuleMap_eq_one {π : Equiv.Perm (Fin TwistTag.D4.tag.rank)}
    (hπ : ∀ i j, TwistTag.D4.tag.cartan (π i) (π j) = TwistTag.D4.tag.cartan i j) (h : π = 1) :
    permModuleMap hπ L = 1 := by
  subst h
  exact permModuleMap_one L hπ

theorem permModuleMap_eq {π π' : Equiv.Perm (Fin TwistTag.D4.tag.rank)}
    (hπ : ∀ i j, TwistTag.D4.tag.cartan (π i) (π j) = TwistTag.D4.tag.cartan i j)
    (hπ' : ∀ i j, TwistTag.D4.tag.cartan (π' i) (π' j) = TwistTag.D4.tag.cartan i j)
    (h : π = π') : permModuleMap hπ L = permModuleMap hπ' L :=
  permModuleMap_congr hπ L h hπ'

theorem cartan_mul {π π' : Equiv.Perm (Fin TwistTag.D4.tag.rank)}
    (hπ : ∀ i j, TwistTag.D4.tag.cartan (π i) (π j) = TwistTag.D4.tag.cartan i j)
    (hπ' : ∀ i j, TwistTag.D4.tag.cartan (π' i) (π' j) = TwistTag.D4.tag.cartan i j) (i j) :
    TwistTag.D4.tag.cartan ((π * π') i) ((π * π') j) = TwistTag.D4.tag.cartan i j := by
  simp only [Equiv.Perm.mul_apply]
  rw [hπ, hπ']

theorem triN_mul_self : triN L * triN L = 1 := by
  rw [triN, permModuleMap_mul triSwap_cartan L triSwap_cartan
    (cartan_mul triSwap_cartan triSwap_cartan)]
  exact permModuleMap_eq_one L _ triSwap_mul_self

theorem triP_cube : triP L * triP L * triP L = 1 := by
  rw [triP_eq_perm, permModuleMap_mul perm_cartan L perm_cartan (cartan_mul perm_cartan perm_cartan),
    permModuleMap_mul (cartan_mul perm_cartan perm_cartan) L perm_cartan
      (cartan_mul (cartan_mul perm_cartan perm_cartan) perm_cartan)]
  exact permModuleMap_eq_one L _ perm_cube

theorem triP_sq : triP L * triP L = (triP L)⁻¹ := eq_inv_of_mul_eq_one_left (triP_cube L)

theorem triN_mul_triP : triN L * triP L = (triP L)⁻¹ * triN L := by
  rw [← triP_sq, triN, triP_eq_perm, permModuleMap_mul triSwap_cartan L perm_cartan
    (cartan_mul triSwap_cartan perm_cartan),
    permModuleMap_mul perm_cartan L perm_cartan (cartan_mul perm_cartan perm_cartan),
    permModuleMap_mul (cartan_mul perm_cartan perm_cartan) L triSwap_cartan
      (cartan_mul (cartan_mul perm_cartan perm_cartan) triSwap_cartan)]
  refine permModuleMap_eq L _ _ ?_
  ext i
  fin_cases i <;> rfl

theorem triN_conj_triP : triN L * triP L * (triN L)⁻¹ = (triP L)⁻¹ := by
  rw [triN_mul_triP]
  group

end Maps

end CFSG.RankThree.PartOne.TCX.Tri
