
module


public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
import Certificates.Kernel.LocalQT.Lat.C4058
import CFSG.Certificates.Kernel.LocalQTA7KSound

public section

namespace Certificates

open CFSG.KD.LQT.C4058 CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
open Equiv CFSG.QuasithinUnique.Unc25K1.Six in
theorem certificate4058 : (latGens.all (fun G => CFSG.QuasithinUnique.Vol2Native.A312L.Seven.closedH (G.map R7.enc) (CFSG.QuasithinUnique.Vol2Native.A312L.Seven.elts G)) = true)
    ∧ (latGens.map (fun G => (CFSG.QuasithinUnique.Vol2Native.A312L.Seven.elts G).size) =
          [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520])
    ∧ (∀ x : P7, Perm.sign x = 1 → ∃ p ∈ dcSets, R7.enc x ∈ p.2)
    ∧ (reps.all (fun r => isLatCheck (dGens ++ [r])) = true)
    ∧ (latGens.all (fun G₁ => latGens.all fun G₂ => isLatCheck (G₁ ++ G₂)) = true) :=
  ⟨List.all_eq_true.2 fun G hG =>
      closed7_sound C CFSG.KD.LQT.C4058.inj G ((allA_eq_true _ _).1 k1 G hG),
    sizes7_sound C CFSG.KD.LQT.C4058.inj latGens k2,
    cover7_sound C CFSG.KD.LQT.C4058.inj dGens reps k3,
    List.all_eq_true.2 fun r hr =>
      isLat7_sound C CFSG.KD.LQT.C4058.inj (dGens ++ [r]) latGens ((allA_eq_true _ _).1 k4 r hr),
    List.all_eq_true.2 fun G₁ h₁ => List.all_eq_true.2 fun G₂ h₂ =>
      isLat7_sound C CFSG.KD.LQT.C4058.inj (G₁ ++ G₂) latGens
        ((allA_eq_true _ _).1 ((allA_eq_true _ _).1 k5 G₁ h₁) G₂ h₂)⟩

end Certificates
