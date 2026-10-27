module

public import CFSG.Quasithin.H13.U3S1347P
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.H13.U3.S6Out Equiv

abbrev SixE6 : Type := ↥(coreMod 6)

instance sixE6CommGroup : CommGroup SixE6 :=
  { (inferInstance : Group SixE6) with
    mul_comm := fun a b => Subtype.ext (mul_comm (a : PermMod 6) (b : PermMod 6)) }

@[expose] def sixS0 : Perm (Fin 6) := swap 2 3 * swap 4 5

@[expose] def sixAlpha : Perm (Fin 6) →* Perm (Fin 6) :=
  phi.comp (MulAut.conj sixS0).toMonoidHom

theorem sixAlpha_mem_alt {σ : Perm (Fin 6)} (h : σ ∈ alternatingGroup (Fin 6)) :
    sixAlpha σ ∈ alternatingGroup (Fin 6) := by
  have h1 : sixS0 * σ * sixS0⁻¹ ∈ alternatingGroup (Fin 6) :=
    Subgroup.Normal.conj_mem inferInstance σ h sixS0
  exact phi_mem_alternatingGroup h1

@[expose] def sixAlphaA :
    ↥(alternatingGroup (Fin 6)) →* ↥(alternatingGroup (Fin 6)) :=
  MonoidHom.codRestrict (sixAlpha.comp (alternatingGroup (Fin 6)).subtype)
    (alternatingGroup (Fin 6)) (fun a => sixAlpha_mem_alt a.2)

@[expose] def sixRho : Perm (Fin 6) →* MulAut (SixE6 × SixE6) where
  toFun σ :=
    { toFun := fun x => ((coreAct 6 σ) x.1, (coreAct 6 (sixAlpha σ)) x.2)
      invFun := fun x => ((coreAct 6 σ).symm x.1, (coreAct 6 (sixAlpha σ)).symm x.2)
      left_inv := fun x => Prod.ext (by simp) (by simp)
      right_inv := fun x => Prod.ext (by simp) (by simp)
      map_mul' := fun x y => Prod.ext (map_mul _ _ _) (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun x => Prod.ext (by simp) (by simp [sixAlpha])
  map_mul' := fun σ τ => MulEquiv.ext fun x => Prod.ext (by simp) (by simp)

@[expose] def sixSwap : MulAut (SixE6 × SixE6) := MulEquiv.prodComm

@[expose] def sixGhat : Subgroup (MulAut (SixE6 × SixE6)) :=
  Subgroup.closure (Set.range sixRho ∪ {sixSwap})

@[expose] def sixLhat : Subgroup (MulAut (SixE6 × SixE6)) :=
  (alternatingGroup (Fin 6)).map sixRho

@[expose] def sixZ : SixE6 := ⟨allOnes 6, by decide⟩

@[expose] def sixDiag : Subgroup (SixE6 × SixE6) := Subgroup.zpowers (sixZ, sixZ)

@[expose] def sixFixMod (K : Subgroup (SixE6 × SixE6)) (X : Subgroup (MulAut (SixE6 × SixE6))) :
    Set (SixE6 × SixE6) :=
  {u | ∀ x ∈ X, (x : MulAut (SixE6 × SixE6)) u * u⁻¹ ∈ K}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
