module

public import Certificates.Data.Kernel.P0Vis

public section

namespace CFSG.KC.P0Vis

@[expose] def glenOK (rows : List VRow) : Bool :=
  rows.all fun row => row.2.all fun c => Nat.ble c.1.length 16

end CFSG.KC.P0Vis

end
