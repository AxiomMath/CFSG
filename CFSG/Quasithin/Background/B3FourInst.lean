module

public import CFSG.Quasithin.Background.B3Four3
public meta import CFSG.Quasithin.Background.B3Defs
public meta import CFSG.Quasithin.Background.B3FourData
public import Certificates.Certificate8061
public import CFSG.Assembly.QuasithinDefs
public meta import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.B1
public meta import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B1Solvable
public meta import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Quasithin.Background.B3Facts
public import CFSG.Quasithin.Background.B3Q
public meta import CFSG.Quasithin.Background.B3Q
public meta import CFSG.Quasithin.Background.B3VMod

public section

namespace CFSG.Quasithin.B3

theorem chkL6_u0 : chkL6 Mod.u0 = true :=
  Certificates.certificate8061.1
theorem chkL6_ut0 : chkL6 Mod.ut0 = true :=
  Certificates.certificate8061.2.1
theorem chkG6_u0 : chkG6 Mod.u0 = true :=
  Certificates.certificate8061.2.2.1
theorem chkG6_ut0 : chkG6 Mod.ut0 = true :=
  Certificates.certificate8061.2.2.2

theorem chkL6_of_mem
    {k : Mod} (hk : k = Mod.u0 ∨ k = Mod.ut0) : chkL6 k = true := by
  rcases hk with rfl | rfl
  · exact chkL6_u0
  · exact chkL6_ut0

theorem chkG6_of_mem
    {k : Mod} (hk : k = Mod.u0 ∨ k = Mod.ut0) : chkG6 k = true := by
  rcases hk with rfl | rfl
  · exact chkG6_u0
  · exact chkG6_ut0

end CFSG.Quasithin.B3
