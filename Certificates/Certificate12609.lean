
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Q
import CFSG.Sporadic.Schreier.J4SNative
import CFSG.Sporadic.Schreier.J4SCols
import CFSG.Sporadic.Schreier.J4SElevenData
import CFSG.Sporadic.J4.QTNative
import Certificates.Data.J4M2.QStruct
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4GamData
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4GamData
import Certificates.Kernel.J4M2.C12609
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.Schreier.J4SEleven
import CFSG.Sporadic.J4.QT2LocCntProof

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2.Wilson.Coordinator in
theorem certificate12609 : ∀ p ∈ CFSG.Quasithin.J4M2.Qgrp, p ∉ Q8set →
    ∃ i : Fin 7, ∃ w ∈ C0p, ∃ q ∈ Q8set, w * p * w⁻¹ = rRep i * q := KernelJ4M2.c12609

end Certificates
