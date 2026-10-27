module

public import CFSG.Quasithin.EmptyFaithful.S153H33
public import CFSG.Quasithin.EmptyFaithful.R3c2List

public section

namespace CFSG.Quasithin.R3c4

theorem input15333Two_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113) :
    R3c2.Input15333Two := by
  intro G _ _ T Mc M V₁ V₂ Yp I t c
  obtain ⟨z, hz, hz1, hZ⟩ := S153H.exists_generator_Z c.hyp.hyp
  exact ⟨z, S153H.lemma115Hyp_of_ctx h11 h113 c hz hz1 hZ⟩

end CFSG.Quasithin.R3c4
