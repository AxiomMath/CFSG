module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieYamC
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieBrA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_model_yamStd {D : Type} [Group D] {f : ℕ} (hf : 2 ≤ f)
    (hD : CFSG.Blueprint.LieModel D .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K) (_ : CharP K 2),
      IsSimpleGroup (Xg h) ∧ Nonempty (D ≃* Xg h) ∧
      CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Xg h) (Psy h) (Pt h) (Ln h) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  have hf1 : 1 ≤ f := by omega
  obtain ⟨hS, hY⟩ := yamStd_of_eps hF (brFD hF hf1) (brEps hF hf1) (brEps_map_Psy hF hf1)
  exact ⟨F, inferInstance, brFD hF hf1, inferInstance, hS,
    ⟨e.symm.trans (brEps hF hf1).symm⟩, hY⟩

end CFSG.Quasithin.H13.F431.Un.OL
