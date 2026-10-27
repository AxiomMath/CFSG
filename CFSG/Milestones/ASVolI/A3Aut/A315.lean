module

public import CFSG.Milestones.ASVolI.A3Aut.L2
public import CFSG.Milestones.ASVolI.A3Aut.Sz
public import CFSG.Milestones.ASVolI.A3Aut.SmallLin
public import CFSG.Milestones.ASVolI.A3Aut.SmallTits
public import CFSG.Milestones.ASVolI.A3Aut.SmallD4
public import CFSG.Milestones.ASVolI.A3Aut.C5L3
public import CFSG.Milestones.ASVolI.A3Aut.C5Sp4
public import CFSG.Milestones.ASVolI.A3Aut.C5G2
public import CFSG.Milestones.ASVolI.A3Aut.C5F4
public import CFSG.Milestones.ASVolI.A3Aut.D5D4
public import CFSG.Milestones.ASVolI.A3Aut.D5U3

public section

namespace CFSG.ASVolI

theorem burnsideAut_a315LieConcrete :
    burnsideA315x_LieConcrete := by
  intro G _ L T B h hL
  rcases hL with (⟨f, hf⟩ | hTits) | ⟨m, hm, hLm⟩
  · rcases hf with ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ |
      ⟨hodd, hf, hL⟩ | ⟨hodd, hf, hL⟩
    · exact Or.inl (burnsideAut_a315_L2 h hf hL)
    · rcases Nat.lt_or_ge f 2 with h1 | h2
      · obtain rfl : f = 1 := by omega
        exact (burnsideAut_a315_L3two G L T B h hL).elim
      · exact Or.inl (burnsideAut_a315_L3 h h2 hL)
    · exact Or.inl (burnsideAut_a315_U3 h hf hL)
    · exact Or.inl (burnsideAut_a315_Sp4 h hf hL)
    · exact Or.inl (burnsideAut_a315_G2 h hf hL)
    · rcases Nat.lt_or_ge f 2 with h1 | h2
      · obtain rfl : f = 1 := by omega
        exact Or.inr (Or.inl (burnsideAut_a315_3D4two G L T B h hL))
      · exact Or.inl (burnsideAut_a315_3D4 h h2 hL)
    · exact Or.inl (burnsideAut_a315_2F4 h hodd hf hL)
    · exact Or.inl (burnsideAut_a315_Sz h hL)
  · exact Or.inr (Or.inr (burnsideAut_a315_tits G L T B h hTits))
  · rcases hm with rfl | rfl
    · exact (burnsideAut_a315_L4two G L T B h hLm).elim
    · exact (burnsideAut_a315_L5two G L T B h hLm).elim

end CFSG.ASVolI
