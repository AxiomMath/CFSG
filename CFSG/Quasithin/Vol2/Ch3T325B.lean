module

public import CFSG.Quasithin.Vol2.Ch3T325A
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G}

theorem Ctx.hyp318 (c : Ctx T L V₀) :
    Hyp318 T (Subgroup.normalizer (L : Set G)) L (conjClosure V₀ T) :=
  { inM := c.inM
    nonempty := c.hstar
    perfect := eq_oTwoUpper_of_perfect (perfect_of_mem_cComp (cComp_of_isLocal c.fsu.maximal.1))
    le_M := Subgroup.le_normalizer
    normal := le_rfl
    unique := c.uniq
    reduced := c.redV
    centralizer := c.o2 }

theorem qhatInt_V_le (h316 : Theorem316Statement) (c : Ctx T L V₀) :
    qhatInt (L ⊔ T) (conjClosure V₀ T) c.elemV ≤ 2 := by
  have h := c.hyp318
  obtain ⟨H, hH⟩ := h.nonempty
  rcases h316 G T c.fsu.simple c.fsu.nonabelian c.fsu.qtke c.fsu.sylow _ _ H _ h.inM
      (h.hyp315 c.fsu.sylow hH) with h1 | ⟨-, h2, -⟩ | h3
  · exact absurd h1 (h.not_exists_normal hH)
  · exact h2
  · exact (qhatInt_le_qInt _ _ _).trans h3

theorem qhat_V (h316 : Theorem316Statement) (c : Ctx T L V₀) :
    ∃ _ : IsMulCommutative ↥(conjClosure V₀ T),
      qhatOf (V := ↥(conjClosure V₀ T)) (autOn (L ⊔ T) (conjClosure V₀ T)) ≤ 2 :=
  ⟨c.elemV.1, qhatInt_V_le h316 c⟩

end CFSG.Quasithin.H13.T325
