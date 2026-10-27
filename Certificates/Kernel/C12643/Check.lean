module

public import Certificates.Kernel.C12643.LinesD
public import Certificates.Kernel.C12643.Brute
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelC12643

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155

theorem ks155OK_K : ks155OK () = true := by
  have hB := bruteOK_of bfs5a.1 bfs5a.2 bfs5c.1 bfs5c.2 bfs7.1 bfs7.2 bfsE.1 bfsE.2
    (fun k hk => okSplit (ok5aG k (g5a_size ▸ hk))) (fun k hk => okSplit (ok5cG k (g5c_size ▸ hk)))
    (fun k hk => okSplit (ok7G k (g7_size ▸ hk))) (fun k hk => okSplit (okEG k (gE_size ▸ hk)))
    (fun k hk => cm5aG k (g5a_size ▸ hk)) (fun k hk => cm5cG k (g5c_size ▸ hk))
    (fun k hk => cm7G k (g7_size ▸ hk)) (fun k hk => (cmEG k (gE_size ▸ hk)).1)
    (okSplit okx5a) (okSplit okx5c) (okSplit okx7) (okSplit oke1)
  unfold ks155OK
  rw [eltsOK_K, enumsOK_K, hB, linesOK_K, dOK_K]
  rfl

end CertificateChecks.KernelC12643

end
