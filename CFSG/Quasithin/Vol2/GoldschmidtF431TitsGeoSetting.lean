module

public import CFSG.Quasithin.Recognition.RuTypeJ47a

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits

@[expose] noncomputable def titsSetting : LieSetting.{0, 0} where
  α := RankTwoAmalgam.ofSubgroups titsH titsN
  Yb := ↥(titsH ⊔ titsN)
  ι := subCompletion titsH titsN
  hι := subCompletion_isFaithful titsH titsN
  N := ⊤
  hN := Subgroup.normal_of_characteristic ⊤
  p := 2
  hp := Nat.prime_two
  m := 8
  hm := by norm_num

@[simp] theorem titsSetting_m : titsSetting.m = 8 := rfl

@[simp] theorem titsSetting_p : titsSetting.p = 2 := rfl

@[simp] theorem titsSetting_N : titsSetting.N = ⊤ := rfl

theorem card_titsSetting_Yb :
    Nat.card titsSetting.Yb = 17971200 := by
  change Nat.card ↥(titsH ⊔ titsN) = _
  rw [titsH_sup_N]
  exact card_titsD

end CFSG.Quasithin.TitsGeo
