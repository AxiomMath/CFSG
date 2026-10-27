module

public import CFSG.Quasithin.Background.C41PfM
public import CFSG.Quasithin.Background.C41PfG
public import CFSG.Quasithin.EmptyFaithful.SBc6Sl2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def C41Sp4Block : Prop :=
  ∀ H R M L V K : Subgroup G, C41Post H R M L V K →
    SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SmithC27.C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    IsSp4Block K →
    IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
      (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) →
    C41Case2 H R M L V K

namespace C41Pf

theorem c41InspE_of (hK0 : C41KZero G) (hA3 : A3Orbits G) (hSp : C41Sp4Block G) :
    C41InspE G := by
  intro H R M L V K hP h1 h2 hc
  obtain ⟨hA6 | hSp4, hmax⟩ := hc
  · exfalso
    have h := hP.hyp
    exact false_of_isSolvable_autOn h1 hP.le (C2Nine.conjClosure_le_M h)
      (C2Nine.perfect_conjClosure_of_hyp h)
      (fun hb => ne_bot_of_mem_cComp h.comp (eq_bot_iff.mpr ((le_conjClosure L M).trans hb.le)))
      (isSolvable_of_c27A6 hP.le_normalizer h1 hA6 hmax)
  · have hc2 := hSp H R M L V K hP h1 h2 hSp4 hmax
    obtain ⟨-, F, _, _, α, β, -, -, -, -, -, hpsl⟩ := id hc2
    have hS : IsSimpleGroup (ModO2 (conjClosure L M)) :=
      SBc6.isSimpleGroup_of_psl (by norm_num) hpsl
    exact c41Conclusion_of_case hK0 hA3 hP hS (Or.inr (Or.inl hc2))

end C41Pf

end CFSG.Quasithin
