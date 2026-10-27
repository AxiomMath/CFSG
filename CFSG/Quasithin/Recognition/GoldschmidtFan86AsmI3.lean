module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmI2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Main

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace AsmI3

theorem fanTailInputs_at (F : FanTree Γ G) :
    ∃ L : ZLab Γ G, Fan7 F L ∧ Fan65 F ∧ Fan66 F ∧ Fan517 F L ∧ Fan512 F L := by
  have h29 := sigma3Aut
  have h28 := fan28_of_sigma3PushingUp sigma3PushingUp
  have h211 : Tutte.TutteTree := Tutte.tutteTree
  have h40 := fan_4_0_main F h29
  have h33 := fan_3_3_main F h29
  have h36 := fan_3_6 F.localFacts (fan_3_2_main F h29)
  have h48 := fan48_two F h40 h28 h211
  have hXi := exists_inXi F h40 h28 h33 h48
  have hfin := zcFin F h40 h28 h33 h48
  have h51a := fan51a F h36
  have h53a := fan53a F
  have h53b := fan53b F h36
  have h53c := fan53c F h36
  have h54 := fan54 F h36
  have h55a := fan55a F h54
  have h55b := fan55b F h54
  have h55c := fan55c F h54
  have h57b := fan57bT F h53a h53b h53c h54 hfin
  have h58b := fan58b F h53a h53b h53c h54 h51a
  have h59 := fan59 F (fan51a F h36) (fan51b F h36) (fan53a F) (fan53b F h36) (fan53c F h36)
      (fan54 F h36) (fan55h1 F (fan54 F h36)) (fan55h2 F (fan54 F h36)) hfin
  have h510 := fan510 F h28 h33 h211 h53a h53b h53c h55c h58b h59
  have h511 := fan511 F h28 h33 h211 h53a h53b h53c h55c h57b h58b h59
  have h512cen := fan512cen F
  have h512a := fan512a F h510 h511
  have h512b := fan512b F h510 h511 h53a
  have h512c := fan512c F h510 h511 h53a h53b h57b
  have h513a := fan513a F h28
  have h514 := fan_5_14_of_sec4 F h28 h211 h33 h51a h53b h53c h54 h55a h55b h55c h510 h511
    h512cen h512b h512c h513a
  have h57a := fan57a F h53a h53b h54
  have h58a := fan58aT F h53a h53b h54 h51a
  have h61 := fan_6_1 F hXi h510 h511 h512b h514 h53a h53b h53c h54 h55a h55c h51a h57a h58a hfin
  have hD := lemmaD F
  have h517a := fan517a F h510 h511 h53a hXi
  have h517c := fan517c F h510 h511 h53a hXi hD
  have h513b := fan513b F h28 h36
  have h515a := fan_5_15a F h513b h510 h511 h512cen h512b
  have h515b := fan_5_15b F h513b h510 h511 h512cen h512b h515a
  have h516 := fan_5_16 F h28 h36 h510 h511 h512cen h512c h515a h515b h53b
  have h481 : Fan40 F → ∀ T₀ : Track Γ G, T₀.fixer ≠ ⊥ → ∃ T' : Track Γ G, InPiStar T' :=
    fun h40' T₀ h => (fan48_1 F h40' h28 T₀ h).imp fun _ hT' => hT'.2
  have h518 := fan_5_18_proved F h33 h36 h481 h510 h511 h512cen h512b h512c h515a h516 h517a
    h517c hD
  have h519 := fan519 F h510 h511 h514 h518
  have h62 := fan_6_2 F h519 h53a h512cen h512b h61 hD h517a h517c
  have h512d := fan512d F h62 h53b h54 h512cen
  have h63 := fan63 F hXi h61 h62 h512b h517a hD h517c
  have h64 := fan64 F hXi h61 h62 h512b h517a hD h517c
  have h65 := fan65 F h40 hXi h61 h62 h512b h512cen h517a hD h517c h33
  have h66 := fan66 F h40 h28 h211 h61 h62 h512cen
  obtain ⟨T, hT⟩ := hXi
  obtain ⟨z, hZ, hz1⟩ := AsmI2.exists_zz F h40 T.line
  obtain ⟨a, b, tL, tR, hfix⟩ := (h519 h40 T hT z hZ hz1).1
  have hba : b - a = 2 := (h519 h40 T hT z hZ hz1).2 a b tL tR hfix |>.1
  have hcore : T.line.IsCore z a (a + 2) := by
    have := hfix.core
    rwa [show b = a + 2 by omega] at this
  have hz : z ∈ Cinv G (T.line.vert (a + 1)) := h512cen h40 T z a hT hZ hz1 hcore
  have hα : valence Γ (T.line.vert (a + 1)) = 5 := by
    have h3 := h61 h40 _ z hz
    rcases F.valence (T.line.vert (a + 1)) with h | h
    · exact absurd h h3
    · exact h
  obtain ⟨L, hLz, -⟩ := P62.exists_labHyp F h40 h512b h517a hD h517c T hT a hZ hz1 hcore hα hz
  have h517 : Fan517 F L := fan517_of_lab F h40 h517a h517c L
  have h512 : Fan512 F L :=
    fan512_of_lab F h40 h512a h512b h512d L T hT a hZ hz1 hcore hα hLz
  have hXi' : ∃ T : Track Γ G, InXi T := ⟨T, hT⟩
  have h71 := fan_7_1 F L h40 h62 h63 h65 h517 hXi'
  have h72 := fan_7_2_of_fan512 h71.2.2 h512 h40 h64
  have h73 := fan_7_3 h71.1 h71.2.2 h72.2 h40 h64 h65
  have h74 := fan_7_4 h40 hXi' h62 h64 h65 h71.1 h71.2.2 h72.2 h73.2
  have h75 := fan_7_5 h40 hXi' h62 h64 h65 h71.1 h71.2.2 h72.2 h73.2
  exact ⟨L, ⟨h71.1, h71.2.1, h71.2.2, h72.1, h72.2, h73.1, h73.2, h74, h75⟩, h65, h66, h517,
    h512⟩

theorem fanTailInputs_proved : FanTailInputs :=
  fun _ _ _ _ _ F => fanTailInputs_at F

end AsmI3

end CFSG.Quasithin.Fan86
