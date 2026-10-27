module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Vol2.F134J1
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem noE25Config_of_mulEquiv_card {G : Type} [Group G] {N : ℕ} (hG : Nat.card G = N)
    (hN : ¬ 25 ∣ N) : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* G) :=
  noE25Config_of_not_dvd fun X _ ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, hG]
    exact hN

theorem not_twentyFive_dvd_card_alternatingGroup_fin {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    ¬ 25 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  interval_cases n <;> decide

theorem facts134Five_alt : NoE25Config fun (X : Type) [Group X] =>
    ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (X ≃* alternatingGroup (Fin n)) :=
  noE25Config_of_not_dvd fun X _ ⟨n, h5, h8, ⟨e⟩⟩ => by
    rw [Nat.card_congr e.toEquiv]
    exact not_twentyFive_dvd_card_alternatingGroup_fin h5 h8

theorem facts134Five_psl45 : ∀ n : ℕ, (n = 4 ∨ n = 5) →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL n 2 1 := by
  intro n hn
  refine noE25Config_of_not_dvd fun X _ h => ?_
  rcases hn with rfl | rfl
  · rw [CFSG.Quasithin.F420.card_of_l42 h]
    decide
  · rw [CFSG.Quasithin.F420.card_of_l52 h]
    decide

theorem card_nativeM12_bridge : Nat.card NativeSporadic.M12 = 95040 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M12.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M12.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M12.le_card_native

theorem card_nativeM22_bridge : Nat.card NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M22.le_card_native

theorem facts134Five_m11 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M11) :=
  noE25Config_of_mulEquiv_card (G := NativeSporadic.Carrier .M11)
    CFSG.ClassicalInvolution.Q3.card_m11_kernel (by decide)

theorem facts134Five_m12 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12) :=
  noE25Config_of_mulEquiv_card (G := NativeSporadic.Carrier .M12) card_nativeM12_bridge
    (by decide)

theorem facts134Five_m22 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22) :=
  noE25Config_of_mulEquiv_card (G := NativeSporadic.Carrier .M22) card_nativeM22_bridge
    (by decide)

theorem facts134Five_m23 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23) :=
  noE25Config_of_mulEquiv_card (G := NativeSporadic.Carrier .M23)
    CFSG.Sporadic.Schreier.m23_card (by decide)

theorem facts134Five_m24 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24) :=
  noE25Config_of_mulEquiv_card (G := NativeSporadic.Carrier .M24)
    CFSG.Sporadic.Mathieu.card_M24 (by decide)

theorem facts134Five_j1 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1) :=
  noE25Config_of_mulEquiv_card (G := NativeSporadic.Carrier .J1)
    CFSG.Quasithin.F134.card_carrier_J1 (by decide)

theorem facts134Five_j4 :
    NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4) :=
  noE25Config_of_mulEquiv_card (G := NativeSporadic.Carrier .J4)
    CFSG.Sporadic.J4.card_J4 (by norm_num)

end CFSG.Quasithin.S146zY
