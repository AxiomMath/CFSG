module

public import CFSG.Milestones.ASVolI.A3L3.L3
public import CFSG.Milestones.ASVolI.A3L3.L3E
public import CFSG.Milestones.ASVolI.A3L3.L3U
public import CFSG.Milestones.ASVolI.A3L3.U3
public import CFSG.Milestones.ASVolI.A3L3.PGL2
public import CFSG.Milestones.ASVolI.A3L3.Steps
public import CFSG.Milestones.ASVolI.A3L3.StepsCartan

public section

namespace CFSG.ASVolI

theorem burnsideA315y_l3Fact : CFSG.Quasithin.A315L3Fact := by
  intro G _ L T B h hab δ p hp hp2 hL
  have hfit := burnsideA315y_fitting
  have hsteps := burnsideA315y_steps burnsideA315y_pgl2
  have hcartan := burnsideA315y_cartan
  cases δ with
  | true =>
    exact burnsideA315y_l3Case_of hfit hsteps hcartan
      (fun F _ _ p _ hF _ _ _ _ B' hD => burnsideA315y_l3_E hF B' hD)
      (fun F _ _ p _ hF _ _ _ _ => burnsideA315y_l3_cartanU hF) h hab hp hp2 hL
  | false =>
    exact burnsideA315y_u3Case hfit hsteps hcartan h hab hp hp2 hL

section Assembly


theorem burnsideA315y_A_3_15_of (hlist : CFSG.Quasithin.A23SQTKListFact)
    (hlie : burnsideA315x_LieConcrete) (hsp : CFSG.Quasithin.A315SporadicFact) : A_3_15 :=
  burnsideA315x_assembly hlist burnsideA315x_altFact burnsideA315x_l2Fact burnsideA315y_l3Fact
    burnsideA315x_l3rFact hlie hsp

end Assembly

end CFSG.ASVolI
