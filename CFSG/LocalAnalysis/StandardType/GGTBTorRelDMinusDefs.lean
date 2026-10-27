module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega

public section

namespace CFSG.StandardType

namespace RelDMinus

open CFSG.Assembly TableBSymp

variable (K : Type) [Field K] (m : ℕ)

@[expose] noncomputable def torusGL : (Fin m → Kˣ) →* GL (LargeEvenMinusIdx m) K :=
  blockInl.comp (TauCeti.diagGL.comp pairedHom)

theorem torusGL_apply (x : Fin m → Kˣ) :
    torusGL K m x = blockInl (TauCeti.diagGL (pairedUnits x)) :=
  rfl

@[expose] noncomputable def primeTorusGL (p : ℕ) : Subgroup (GL (LargeEvenMinusIdx m) K) :=
  ((powMonoidHom p : (Fin m → Kˣ) →* (Fin m → Kˣ)).ker).map (torusGL K m)

theorem mem_primeTorusGL {p : ℕ} {g : GL (LargeEvenMinusIdx m) K} :
    g ∈ primeTorusGL K m p ↔ ∃ x : Fin m → Kˣ, x ^ p = 1 ∧ torusGL K m x = g := by
  simp [primeTorusGL, MonoidHom.mem_ker]

end RelDMinus

end CFSG.StandardType
