module

public import CFSG.Quasithin.EmptyFaithful.S151S9TThreeDFact
public import CFSG.Quasithin.EmptyFaithful.S151S9UDef

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.S151S9U

structure ThreeDFacts : Prop where
  j2 : ThreeDLocFor .J2
  m12 : ThreeDLocFor .M12
  m22 : ThreeDLocFor .M22
  m23 : 
    ThreeDLocFor .M23
  mld22 : MLDAt .M22
  mld23 : 
    MLDAt .M23

end CFSG.Quasithin.S151S9T
