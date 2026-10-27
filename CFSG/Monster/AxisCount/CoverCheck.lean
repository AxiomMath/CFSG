module

public import Certificates.Certificate6006

public section

namespace CFSG.Monster.AxisCount.Cert

theorem orbitOK_0 : CoverOrbits 0 :=
  Certificates.certificate6006.1

theorem orbitOK_1 : CoverOrbits 1 :=
  Certificates.certificate6006.2.1

theorem orbitOK_2 : CoverOrbits 2 :=
  Certificates.certificate6006.2.2.1

theorem orbitOK_3 : CoverOrbits 3 :=
  Certificates.certificate6006.2.2.2.1

theorem orbitOK_4 : CoverOrbits 4 :=
  Certificates.certificate6006.2.2.2.2.1

theorem orbitOK_5 : CoverOrbits 5 :=
  Certificates.certificate6006.2.2.2.2.2.1

theorem orbitOK_6 : CoverOrbits 6 :=
  Certificates.certificate6006.2.2.2.2.2.2.1

theorem orbitOK_7 : CoverOrbits 7 :=
  Certificates.certificate6006.2.2.2.2.2.2.2.1

theorem orbitOK_8 : CoverOrbits 8 :=
  Certificates.certificate6006.2.2.2.2.2.2.2.2.1

theorem orbitOK_9 : CoverOrbits 9 :=
  Certificates.certificate6006.2.2.2.2.2.2.2.2.2.1

theorem orbitOK_10 : CoverOrbits 10 :=
  Certificates.certificate6006.2.2.2.2.2.2.2.2.2.2.1

theorem orbitOK_11 : CoverOrbits 11 :=
  Certificates.certificate6006.2.2.2.2.2.2.2.2.2.2.2

theorem orbitOK_all : ∀ i : Fin 12, CoverOrbits i
  | ⟨0, _⟩ => orbitOK_0
  | ⟨1, _⟩ => orbitOK_1
  | ⟨2, _⟩ => orbitOK_2
  | ⟨3, _⟩ => orbitOK_3
  | ⟨4, _⟩ => orbitOK_4
  | ⟨5, _⟩ => orbitOK_5
  | ⟨6, _⟩ => orbitOK_6
  | ⟨7, _⟩ => orbitOK_7
  | ⟨8, _⟩ => orbitOK_8
  | ⟨9, _⟩ => orbitOK_9
  | ⟨10, _⟩ => orbitOK_10
  | ⟨11, _⟩ => orbitOK_11
  | ⟨n + 12, h⟩ => absurd h (by omega)

end CFSG.Monster.AxisCount.Cert
