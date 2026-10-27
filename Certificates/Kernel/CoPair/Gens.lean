module

public import Certificates.Data.Kernel.CoPair
public import CFSG.Certificates.Kernel.Common.HexNat
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair CFSG.Monster.Existence.CoPair.Native

@[expose] def MXText : String := include_str "mx.hex"

@[expose] def MYText : String := include_str "my.hex"

@[expose] def TXText : String := include_str "tx.hex"

@[expose] def TYText : String := include_str "ty.hex"

@[expose] noncomputable def MX : Nat := by hex_nat MXText 144 9711576600543555938

@[expose] noncomputable def MY : Nat := by hex_nat MYText 144 2280303840861968132

@[expose] noncomputable def TX : Nat := by hex_nat TXText 4608 13717357438714071269

@[expose] noncomputable def TY : Nat := by hex_nat TYText 4608 1017830190977853223

theorem rowsX : rowsOK MX xWordN = true := by quickRfl

theorem rowsY : rowsOK MY yWordN = true := by quickRfl

theorem tabX : tabOK MX TX = true := by quickRfl

theorem tabY : tabOK MY TY = true := by quickRfl

end CertificateChecks.KernelCoPair

end
