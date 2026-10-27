module

public import CFSG.RankThree.Co2.X9Facts
import Certificates.Kernel.Co2X9.Facts
import CFSG.RankThree.Co2.CmWords

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.Co2

theorem certificate8111 : CFSG.RankThree.Co2.X9Facts := by
  obtain ⟨h9, hc, hne, hd, hsq, hcen, hf, hf9, he, he1⟩ := KernelSpor.Co2X9.x9Facts
  have hk : ∀ k : Fin xWords9.size, (k : ℕ) < 4 := fun k =>
    k.2.trans_eq KernelSpor.Co2X9.xWords9_size
  refine ⟨fun k => ?_, hc, hne, fun k => ?_, hsq, hcen, ⟨wordMat f9W, wordMat_mem_Cm hf, hf9⟩,
    ⟨wordMat e1W, wordMat_mem_Cm he, he1⟩⟩
  · have := h9 k (hk k)
    rwa [getElem!_pos xWords9 (k : ℕ) k.2] at this
  · have := hd k (hk k)
    rwa [getElem!_pos xWords9 (k : ℕ) k.2] at this

end Certificates
