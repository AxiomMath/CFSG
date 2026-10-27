
module


public import Certificates.Certificate6110
public import CFSG.Sporadic.Recognition.LyonsModelStage

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open Equiv Equiv.Perm Subgroup

theorem tabCheck_eq_true : tabCheck = true :=
  Certificates.certificate6110.1

theorem coverCheck_eq_true : coverCheck = true :=
  Certificates.certificate6110.2.1

theorem structCheck_eq_true : structCheck = true :=
  Certificates.certificate6110.2.2.1

theorem cp1Check_eq_true : cp1Check = true :=
  Certificates.certificate6110.2.2.2.1

theorem invCheck_eq_true : invCheck = true :=
  Certificates.certificate6110.2.2.2.2.1

theorem markCheck_eq_true : markCheck = true :=
  Certificates.certificate6110.2.2.2.2.2.1

theorem cp3Fact_of_certificate : Cp3Fact :=
  Certificates.certificate6110.2.2.2.2.2.2

theorem modelChecks_of_certificate : ModelChecks :=
  ⟨tabCheck_eq_true, coverCheck_eq_true, structCheck_eq_true, cp1Check_eq_true,
    invCheck_eq_true, markCheck_eq_true, cp3Fact_of_certificate⟩

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
