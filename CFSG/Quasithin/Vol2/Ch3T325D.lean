module

public import CFSG.Quasithin.Vol2.Ch3T325C

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G}

theorem qhatInt_VM_le (h316 : Theorem316Statement) (c : Ctx T L V₀) :
    qhatInt (Subgroup.normalizer (L : Set G))
      (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) c.elemVM ≤ 2 := by
  obtain ⟨H, hH⟩ := c.hstar
  have hyp := c.hyp315 hH
  rw [qhatInt_congr c.elemVM c.autOn_M₀]
  rcases h316 G T c.fsu.simple c.fsu.nonabelian c.fsu.qtke c.fsu.sylow _ _ H _ c.inM hyp with
    ⟨R₀, hR₀, hR₀le, hR₀N⟩ | ⟨-, hq2, -⟩ | hq3
  · exfalso
    have hR₀p : IsPGroup 2 R₀ := (pCoreOf_isPGroup 2 _).to_le hR₀le
    obtain ⟨K, hK, hNK⟩ :=
      exists_maxTwoLocal_ge (L := Subgroup.normalizer (R₀ : Set G)) ⟨R₀, hR₀, hR₀p, rfl⟩
    have hKM : K = Subgroup.normalizer (L : Set G) :=
      c.isUniqueM_M₀.2 K ⟨hK, (le_sup_left.trans hR₀N).trans hNK⟩
    exact hH.2.1 ((le_sup_right.trans hR₀N).trans (hNK.trans hKM.le))
  · exact hq2
  · exact (qhatInt_le_qInt' _ _ _).trans hq3

theorem qhat_VM (h316 : Theorem316Statement) (c : Ctx T L V₀) :
    ∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))),
      qhatOf (V := ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
        (autOn (Subgroup.normalizer (L : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) ≤ 2 :=
  ⟨c.elemVM.1, qhatInt_VM_le h316 c⟩

end CFSG.Quasithin.H13.T325
