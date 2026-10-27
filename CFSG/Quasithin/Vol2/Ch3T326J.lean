module

public import CFSG.Quasithin.Vol2.Ch3T326H
public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch3T326G

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem case_d37 (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hD37 : D37) [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hV₀ : V₀ = conjClosure V₀ T)
    (hV : conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :
    (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        CFSG.Blueprint.LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 2 2 n ∧
        V₀ = conjClosure V₀ T ∧
        conjClosure V₀ T =
          conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
        (tensorNatModel 2 K).Realizes
          (V := ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
          (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) ∨
      (CFSG.Blueprint.LieModel ↥(autOn L (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) .PSL 3 2 1 ∧
        V₀ = conjClosure V₀ T ∧
        conjClosure V₀ T =
          conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
        (tensorNatModel 3 (ZMod 2)).Realizes
          (V := ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
          (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))) ⊤ ⊥) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  obtain ⟨s, hs, hsn⟩ := c.exists_t
  have hI : V₀.subgroupOf VM = ⊤ := Subgroup.subgroupOf_eq_top.mpr (hV₀.trans hV).ge
  have hVT : V₀.subgroupOf VM = orbSup (autOn T VM) (V₀.subgroupOf VM) :=
    (congrArg (fun X => X.subgroupOf VM) hV₀).trans c.orbSup_eq.symm
  have htS : conjAct VM ⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩ ∈ autOn T VM :=
    Setup.mem_autOn_iff.2 ⟨⟨s⁻¹, c.T_le_NVM (T.inv_mem hs)⟩, T.inv_mem hs, rfl⟩
  rcases hD37 ↥VM _ _ _ _ _ (c.d3Std h316) hVT _ htS (c.not_mem_normalizer hA37 hs hsn)
      (c.autOn_L₀_eq hA37 hA38 hs hsn) with ⟨n, hpsl, F, hF, hFin, hcard, hR⟩ | ⟨hpsl, hR⟩
  · exact Or.inl ⟨n, F, hF, hFin, hcard, lieModel_of_isPSL (isPSL_of_autSub_top hI hpsl), hV₀,
      hV, realizes_of_autSub_eq_top hI hR⟩
  · exact Or.inr ⟨lieModel_of_isPSL (isPSL_of_autSub_top hI hpsl), hV₀, hV,
      realizes_of_autSub_eq_top hI hR⟩

end Ctx

end CFSG.Quasithin.H13.T326
