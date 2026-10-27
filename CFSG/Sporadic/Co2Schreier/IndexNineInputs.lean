module

public import CFSG.Sporadic.Co2Schreier.IndexNineWords

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier.IndexNineData

@[expose] def co2IdxNineX3Check (_ : Unit := ()) : Bool :=
  eqA 2300 (wordArr cArrs nineX3Sig) (idA 2300)

@[expose] def co2IdxNineY3Check (_ : Unit := ()) : Bool :=
  eqA 2300 (wordArr cArrs nineY3Sig) (idA 2300)

@[expose] def co2IdxNineCommCheck (_ : Unit := ()) : Bool :=
  eqA 2300 (wordArr cArrs (nineXYSig)) (wordArr cArrs (nineYXSig))

@[expose] def co2IdxNineXNeCheck (_ : Unit := ()) : Bool :=
  !eqA 2300 (wordArr cArrs nineXSig) (idA 2300)

@[expose] def co2IdxNineYNeCheck (_ : Unit := ()) : Bool :=
  !eqA 2300 (wordArr cArrs nineYSig) (idA 2300)

@[expose] def co2IdxNineYXCheck (_ : Unit := ()) : Bool :=
  !eqA 2300 (wordArr cArrs nineYSig) (wordArr cArrs nineXSig)

@[expose] def co2IdxNineYX2Check (_ : Unit := ()) : Bool :=
  !eqA 2300 (wordArr cArrs nineYSig) (wordArr cArrs (nineX2Sig))

@[expose] def co2IdxNinePtAt (w : List ℕ) (p : ℕ) : ℕ :=
  (ninePt w ⟨p % 63, Nat.mod_lt _ (by norm_num)⟩).val

@[expose] def co2IdxNineXPermCheck (_ : Unit := ()) : Bool :=
  ((List.range 63).map (co2IdxNinePtAt nineXPos)).Nodup

@[expose] def co2IdxNineYPermCheck (_ : Unit := ()) : Bool :=
  ((List.range 63).map (co2IdxNinePtAt nineYPos)).Nodup

@[expose] def co2IndexNineWordCheck (_ : Unit := ()) : Bool :=
  co2IdxNineX3Check () && co2IdxNineY3Check () && co2IdxNineCommCheck () &&
    co2IdxNineXNeCheck () && co2IdxNineYNeCheck () && co2IdxNineYXCheck () &&
    co2IdxNineYX2Check () && co2IdxNineXPermCheck () && co2IdxNineYPermCheck ()

theorem co2IdxNine_eqA_false {t u : Array ℕ} (h : (!eqA 2300 t u) = true) :
    eqA 2300 t u = false := by
  cases hh : eqA 2300 t u <;> simp_all

theorem co2IndexNineWordCheck_spec (h : co2IndexNineWordCheck () = true) :
    eqA 2300 (wordArr cArrs nineX3Sig) (idA 2300) = true ∧
    eqA 2300 (wordArr cArrs nineY3Sig) (idA 2300) = true ∧
    eqA 2300 (wordArr cArrs nineXYSig) (wordArr cArrs nineYXSig) = true ∧
    eqA 2300 (wordArr cArrs nineXSig) (idA 2300) = false ∧
    eqA 2300 (wordArr cArrs nineYSig) (idA 2300) = false ∧
    eqA 2300 (wordArr cArrs nineYSig) (wordArr cArrs nineXSig) = false ∧
    eqA 2300 (wordArr cArrs nineYSig) (wordArr cArrs nineX2Sig) = false := by
  simp only [co2IndexNineWordCheck, co2IdxNineX3Check, co2IdxNineY3Check,
    co2IdxNineCommCheck, co2IdxNineXNeCheck, co2IdxNineYNeCheck, co2IdxNineYXCheck,
    co2IdxNineYX2Check, Bool.and_eq_true, Bool.not_eq_true, and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, co2IdxNine_eqA_false h.2.2.2.1,
    co2IdxNine_eqA_false h.2.2.2.2.1, co2IdxNine_eqA_false h.2.2.2.2.2.1,
    co2IdxNine_eqA_false h.2.2.2.2.2.2.1⟩

end CFSG.Sporadic.Co2Schreier

end

