module

public import CFSG.GH74.Generic.S45.PerfWitData
public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.GH74.Generic.S45.PerfWitData
public meta import CFSG.Sporadic.SmallOddCore.J3Data
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.J2Data
import Certificates.Kernel.Sporadic.OddCore.PerfWit5148

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.GH74.Generic.S45 in
theorem certificate5148 : ((j3Rows.all fun r => r.centOrder != 1920 || perfWitOK 6156 r.centGens j3PerfWit2A) = true)
    ∧ ((mclRows.all fun r => r.centOrder != 40320 || perfWitOK 275 r.centGens mclPerfWitIn) = true)
    ∧ ((mclRows.all fun r => r.centOrder != 7920 || perfWitOK 275 r.centGens mclPerfWitOut) = true)
    ∧ ((j2Rows.all fun r => r.centOrder != 1920 || perfWitOK 315 r.centGens j2PerfWit2A) = true) :=
  ⟨KernelSpor.PerfWit5148.j3, KernelSpor.PerfWit5148.mclIn, KernelSpor.PerfWit5148.mclOut,
    KernelSpor.PerfWit5148.j2⟩

end Certificates
