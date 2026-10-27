module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NineAAAAA
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LinearAlgebra
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped commutatorElement

theorem s16h_e3_Z3NineAAAA_Kmat_o2_bot
    {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) (hLA : L ≤ A) (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥)
    {N : Subgroup (MulAut W)}
    (hKN : A ⊓ centSub (commSub (⊤ : Subgroup W) L₂) ≤ N)
    (F : N →* coordinateSemilinearGroup 3 OmegaField)
    (hFinj : ∀ a b : ↥((A ⊓ centSub (commSub (⊤ : Subgroup W) L₂)).subgroupOf N),
      F a.1 = F b.1 → a = b) :
    ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField),
      P ≤ ((A ⊓ centSub (commSub (⊤ : Subgroup W) L₂)).subgroupOf N).map F →
      (P.subgroupOf (((A ⊓ centSub (commSub (⊤ : Subgroup W) L₂)).subgroupOf N).map F)).Normal →
      IsPGroup 2 P → P = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U₂ : Subgroup W := commSub (⊤ : Subgroup W) L₂
  let K1 : Subgroup (MulAut W) := A ⊓ centSub U₂
  have hK1core : pCore 2 ↥K1 = ⊥ :=
    s16h_e3_Z3NineAAAAA_K1_pcore_bot hB (by simpa only [U₂] using hrk) hO2
  let K : Subgroup ↥N := K1.subgroupOf N
  let f : ↥K →* coordinateSemilinearGroup 3 OmegaField := F.comp K.subtype
  have hf : Function.Injective f := by
    intro a b hab
    exact hFinj a b (by simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hab)
  have hKcore : pCore 2 ↥K = ⊥ := by
    have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe hKN)
    rw [hK1core] at h
    exact (Subgroup.map_eq_bot_iff_of_injective (pCore 2 ↥K)
      (Subgroup.subgroupOfEquivOfLe hKN).injective).mp h
  intro P hPK hPN hP2
  let R : Subgroup ↥K := P.comap f
  have hR2 : IsPGroup 2 R := hP2.comap_of_injective f hf
  have hfr : f.range = K.map F := by
    rw [show f = F.comp K.subtype from rfl, MonoidHom.range_comp, Subgroup.subtype_range]
  have hPK' : P ≤ f.range := by rw [hfr]; exact hPK
  have hRnorm : R.Normal := by
    have hR_eq : R = (P.subgroupOf f.range).comap f.rangeRestrict := by
      ext x
      simp only [R, Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.coe_rangeRestrict]
    rw [hR_eq, Subgroup.normal_comap_iff_of_surjective f.rangeRestrict_surjective, hfr]
    exact hPN
  have hRbot : R = ⊥ := by
    have hRle : R ≤ pCore 2 ↥K := CFSG.LieType.BorelTits.le_pCore 2 hRnorm hR2
    exact le_bot_iff.mp (hKcore ▸ hRle)
  have hPR : P = R.map f := (Subgroup.map_comap_eq_self hPK').symm
  rw [hPR, hRbot, Subgroup.map_bot]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo