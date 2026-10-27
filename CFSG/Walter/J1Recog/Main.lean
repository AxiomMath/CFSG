module

public import CFSG.Walter.J1Recog.Config
public import CFSG.Walter.J1Recog.Inj

public section

namespace CFSG.Walter.J1Recog

theorem nonempty_mulEquiv_walterJ1 {G : Type} [Group G] [Finite G]
    (h : CFSG.Walter.J1.JankoHyp G) : Nonempty (G ≃* CFSG.Open.walterJ1) := by
  obtain ⟨c, f, hf, hs, h840⟩ := exists_config h
  exact nonempty_mulEquiv_of_config h.card_eq c f hf hs h840

end CFSG.Walter.J1Recog
