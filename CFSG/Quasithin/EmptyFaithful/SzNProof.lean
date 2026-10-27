module

public import CFSG.Quasithin.EmptyFaithful.SzNInput
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Native
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts134E9Proof

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Quasithin.P134

theorem input34SuzukiThreeSQTK_holds :
    Input34SuzukiThreeSQTK := by
  intro X _ _ hS hnab hSQTK h3
  have := hS
  rcases theoremCSimple X hnab hSQTK with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd⟩ |
      (⟨f, hf⟩ | hf) | ⟨n, hn, hmod⟩ | ⟨s, hs, ⟨e⟩⟩
  ·
    exfalso
    apply h3
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_alternating n (by omega)
  ·
    exfalso
    apply h3
    rcases hodd with ⟨f, hf, hmod⟩ | hmod | hmod
    · exact facts134E9_psl2OddOrder p f hp hp2 hf X hmod
    · exact facts134E9_psl3OddOrder p hp hp2 X hmod
    · exact facts134E9_psu3OddOrder p hp hp2 X hmod
  ·
    rcases hf with ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ |
      ⟨-, -, hmod⟩ | ⟨-, -, hmod⟩
    · exact (h3 (facts134E9_psl2EvenOrder f X hmod)).elim
    · exact (h3 (facts134E9_psl3EvenOrder f X hmod)).elim
    · exact (h3 (facts134E9_psu3EvenOrder f X hmod)).elim
    · exact (h3 (facts134E9_psp4EvenOrder f X hmod)).elim
    · exact (h3 (facts134E9_g2EvenOrder f X hmod)).elim
    · exact (h3 (facts134E9_d4EvenOrder f X hmod)).elim
    · exact (h3 (facts134E9_f4EvenOrder f X hmod)).elim
    · exact ⟨f, hmod⟩
  ·
    exact (h3 (facts134E9_titsOrder X hf)).elim
  ·
    exact (h3 (facts134E9_psl45Order n hn X hmod)).elim
  ·
    exfalso
    apply h3
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Nat.card_congr e.toEquiv]
      exact three_dvd_card_M11
    · rw [Nat.card_congr (e.trans F134.carrierM12Equiv).toEquiv]
      exact F134.three_dvd_card_m12
    · exact facts134E9_m22.1 X ⟨e⟩
    · exact facts134E9_m23.1 X ⟨e⟩
    · exact facts134E9_m24.1 X ⟨e⟩
    · exact facts134E9_j1Order X ⟨e⟩
    · exact facts134E9_j2.1 X ⟨e⟩
    · rw [Nat.card_congr e.toEquiv]
      show 3 ∣ Nat.card NativeSporadic.J4
      rw [CFSG.Sporadic.J4.card_J4]
      norm_num
    · exact facts134E9_hs.1 X ⟨e⟩
    · exact facts134E9_he X ⟨e⟩
    · exact facts134E9_ru.1 X ⟨e⟩

end CFSG.Quasithin
