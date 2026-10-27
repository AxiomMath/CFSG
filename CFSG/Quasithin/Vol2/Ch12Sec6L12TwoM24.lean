module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Transport
public import CFSG.Quasithin.H13.LocDblProfY
public import CFSG.Quasithin.H13.LocDblProfSmall
public import CFSG.Quasithin.H13.LocDblProfSextet
public import CFSG.Quasithin.H13.LocDblProfM24
public import CFSG.Quasithin.H13.LocDblM24Facts

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13.LocDbl CFSG.Quasithin.H13.LocDbl.M24Prof
open CFSG.Quasithin.H13.LocDbl.M24Facts

theorem a6LocM24_holds :
    A6LocM24 := by
  intro X _ _ ⟨e⟩ Y F h
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hYj, hFj⟩ := a6Config_card h
  have hF32 : 32 ≤ Nat.card F := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hFj
    rw [hm] at hlt ⊢
    have h5 : 5 ≤ m := by
      by_contra hm5
      push Not at hm5
      have : 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h5
  haveI : Finite ↥NativeSporadic.M24 := Finite.of_equiv X e.toEquiv
  have h' := a6Config_map_mulEquiv e h
  have hF' : 32 ≤ Nat.card (F.map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hF32
  have hnorm := h'.2.2.2.2.1
  have hnormal2 := normal2_of_a6Config h'
  have hnofix := nofix_of_a6Config h' hF' m24_stab_two
  obtain ⟨j', -, hY'⟩ := card_of_a6Config_of_le h' hF'
  have hprof : ProfileOK (F.map e.toMonoidHom) := m24_profile _ h'.2.2.2.1 hF'
  have h9 : 9 ∣ Nat.card (Y.map e.toMonoidHom) := by
    rw [hY']
    exact Dvd.dvd.mul_right (by norm_num) _
  have h5 : 5 ∣ Nat.card (Y.map e.toMonoidHom) := by
    rw [hY']
    exact Dvd.dvd.mul_right (by norm_num) _
  rcases hprof with ⟨h0, h2⟩ | ⟨h0, h4⟩ | h4 | h8
  · exact false_of_small hnorm h9 hnormal2 hnofix (Or.inl rfl) h0 (by omega)
  · exact false_of_small hnorm h9 hnormal2 hnofix (Or.inr rfl) h0 (by omega)
  · exact false_of_sextet hnorm hY' hnormal2 hnofix m24_fix3 h4
  · exact false_of_eight hnorm h9 hnormal2 h5 m24_fix5 h8

end CFSG.Quasithin.H13.K1262Two
