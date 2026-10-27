module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieA
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieI
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem l34LieFacts12631 :
    L34LieFacts12631 := by
  intro F _ _ hF Q _ _ X
  constructor
  · rintro ⟨e⟩
    have hK : IsPSL 3 2 2 ↥X :=
      ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, F, inferInstance,
        inferInstance, by rw [hF]; norm_num, ⟨e⟩⟩
    have haut := S126P31.psl34_card_aut hK
    refine ⟨S126P31.three_rank_transport X (S126P31.psl34_three_rank hK), haut, ?_, ?_, ?_⟩
    · obtain ⟨P, hPn, hPi, hIP, -⟩ := S126P31.psl34_aut_structure hK haut
      exact ⟨P, hPn, hPi, hIP⟩
    · exact S126P31.card_borel_transport X 192
        (fun T hT => S126P31.psl34_card_normalizer_sylow hK T hT)
    · exact S126P31.overgroup_transport X 3 fun T N W hT hB hNB hNK hWN hWnorm hW23 =>
        S126P31.psl34_overgroup hK T N W hT (S126P31.psl34_card_normalizer_sylow hK T hT) hB hNB
          hNK hWN hWnorm hW23
  · rintro ⟨e⟩
    exact ⟨S126P31.three_rank_transport X (S126P31.sl34_three_rank hF e),
      S126P31.sl34_card_aut_dvd hF e, S126P31.sl34_out_exp hF e,
      S126P31.card_borel_transport X 576
        (fun T hT => S126P31.sl34_card_normalizer_sylow hF e T hT),
      S126P31.overgroup_transport X 9 fun T N W hT hB hNB hNK hWN hWnorm hW23 =>
        S126P31.sl34_overgroup hF e T N W hT hB hNB hNK hWN hWnorm hW23⟩

end CFSG.Quasithin.H13
