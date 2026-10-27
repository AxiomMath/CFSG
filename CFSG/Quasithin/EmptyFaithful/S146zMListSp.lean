module

public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

theorem three_dvd_card_alternating {S : Type} [Group S] {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8)
    (e : S ≃* alternatingGroup (Fin n)) : 3 ∣ Nat.card S := by
  have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => by simpa using congrArg Fin.val h⟩
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  interval_cases n <;> decide

theorem zm_card_nativeM23 :
    Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem three_dvd_card_sporadic
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) :
    3 ∣ Nat.card (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from CFSG.Sporadic.Mathieu.card_M11]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M12) = 95040 from CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from CFSG.Sporadic.Mathieu.card_M22]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from zm_card_nativeM23]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .M24) = 244823040 from CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .J1) = 175560 from CFSG.Sporadic.J1.card_J1]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .J2) = 604800 from CFSG.Sporadic.J2.card_J2]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from CFSG.Sporadic.J4.card_J4]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 from CFSG.Sporadic.Ru.card_Ru]
    norm_num

end CFSG.Quasithin
