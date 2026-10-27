module

public import CFSG.Milestones.ASVolI.F48.D43.Lin
import Certificates.Kernel.D43.Key0
import Certificates.Kernel.D43.Key1
import Certificates.Kernel.D43.Key2
import Certificates.Kernel.D43.Key3
import Certificates.Kernel.D43.Key4
import Certificates.Kernel.D43.Key5
import Certificates.Kernel.D43.Key6
import Certificates.Kernel.D43.Key7
import Certificates.Kernel.D43.RowsA
import Certificates.Kernel.D43.RowsB
import Certificates.Kernel.D43.RowsC
import Certificates.Kernel.D43.Ord
import Certificates.Kernel.D43.Bind
import CFSG.Certificates.Kernel.D43.KeySound

public section

open CFSG.ASVolI CFSG.KC.D43 CertificateChecks.KernelD43

namespace Certificates

open CFSG CFSG.ASVolI CFSG.Blueprint.Chevalley in
theorem certificate7800 : ∀ (K : Type) [Field K] (ω : K), Nat.card K = 27 → ω ^ 3 = ω + 1 →
    ∀ h : Fin 8 → ModGL Tag.D4 K,
      (∀ k, (h k : Module.End K (RootModule Tag.D4 K)) = burnsideF48d_genEnd ω k) →
      ∃ ρ : ↥(Subgroup.closure (Set.range h)) →* Equiv.Perm (Fin 26572),
        ∀ k (p : Fin 26572), ((ρ ⟨h k, Subgroup.subset_closure ⟨k, rfl⟩⟩ p : Fin 26572) : ℕ) =
          (burnsideF48d_gen k)[p.val]! := by
  intro K _ ω hK hω h hh
  have hrows : ∀ k < 8, rowsOK (RL.getD k []) k = true := by
    intro k hk
    interval_cases k
    exacts [rows0, rows1, rows2, rows3, rows4, rows5, rows6, rows7]
  have hch : ∀ k < 8, ∀ c < 104, keyChunk KT (RL.getD k []) (tabAt GX.F k) c = true := by
    intro k hk
    interval_cases k
    exacts [keys0, keys1, keys2, keys3, keys4, keys5, keys6, keys7]
  obtain ⟨hwf, hdist⟩ := ord_spec (O := OT) (ordChunks_spec ordAll)
  obtain ⟨ρ, hρ⟩ := exists_ρ_of_checks (T := fun k p => tabAt GX.F k p) hrows
    (fun k hk p hp => keyChunks_spec (hch k hk) hp) hwf hdist ω hK hω h hh
  exact ⟨ρ, fun k p => (hρ k p).trans (gen_tab k.2 p.2).symm⟩

end Certificates
