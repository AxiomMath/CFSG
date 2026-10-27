module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828MBHolds
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR1
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR2
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR3
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Mat

theorem mb0Row2_828_proved :
    MB0Row2_828 := by
  intro V _ _ H X hXN hXe ⟨h, hX, hfX⟩
  exact mb0_row2 hXN hXe h hX hfX

theorem mb0Row3_828_proved :
    MB0Row3_828 := by
  intro V _ _ H X hXN hXe ⟨h, hX, hfX⟩
  exact mb0_row3 hXN hXe h hX hfX

theorem mb0Row4_828_proved :
    MB0Row4_828 := by
  intro V _ _ H X hXN hXe ⟨h, hX, hfX⟩
  exact mb0_row4 hXN hXe h hX hfX

theorem mb3Row2_828_proved :
    MB3Row2_828 := by
  intro V _ _ H X hXN hXe ⟨h, hX, hfX⟩
  exact mb3_row2 hXN hXe h hX hfX

theorem mb3Row3_828_proved :
    MB3Row3_828 := by
  intro V _ _ H X hXN hXe ⟨h, hX, hfX⟩
  exact mb3_row3 hXN hXe h hX hfX

theorem mb3Row4_828_proved :
    MB3Row4_828 := by
  intro V _ _ H X hXN hXe ⟨h, hX, hfX⟩
  exact mb3_row4 hXN hXe h hX hfX

theorem mb1_828_proved :
    MB1_828 := by
  intro V _ _ H X hXN hXe
  exact ⟨fun ⟨h, hX, hfX⟩ => mb1_row1 hXN hXe h hX hfX,
    fun ⟨h, hX, hfX⟩ => mb1_row2 hXN hXe h hX hfX,
    fun ⟨h, hX, hfX⟩ => mb1_row3 hXN hXe h hX hfX,
    fun ⟨h, hX, hfX⟩ => mb1_row4 hXN hXe h hX hfX⟩

theorem mB0_828_proved :
    MB0_828 :=
  mB0_828_holds mb0Row2_828_proved mb0Row3_828_proved mb0Row4_828_proved

theorem mB3_828_proved :
    MB3_828 :=
  mB3_828_holds mb3Row2_828_proved mb3Row3_828_proved mb3Row4_828_proved

end CFSG.Quasithin.H13
