module

public import Certificates.Kernel.J2Cover.AutChain
public import Certificates.Data.Kernel.Census.Packed

public section

namespace CertificateChecks.KernelCensus.J2K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelJ2Cover

@[expose] noncomputable def inP (P : Nat) : Bool :=
  siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 P

@[expose] noncomputable def uP : Nat :=
  0x4d251309347e633a994ce6b3896c965f1993caa433995cde5d2091c6a53249b47a231b8e48a5918844521d1689c4a3b06794560500733fa13177c441f8fd7b435ef0c79c2a09057d3eddb0780c0dacf47fc3dd8e077b89f2f1753ad92e77442dbadf683b9a2f072321cacc6d36d9cd76c3d59ea95e2f9c2e36ab6574dc4eae1d2de5ab0d6ead632b980c159b4968d35633554ca62a9d8ebd5fa8960b15230988bb47ae5a89c5b28142af4b2c94aa64fa1196a849a212a984528d328d4da49209155a39287b45a5cfc9a401e4ee9e41998e28739224fa74461d50c6f429b8f47c399fd025c3c1d8d06931160d86d29208ac60309acc6642d154a6702497c986a27194bc4a2e99c824b2295c8c5928150b62a221349e4715908a235100846e221c0e4743b1e8d88016078b05a2e120c06232219203a1f0505c302f0d0f07c3f1405052100888c2425130d01c1e03064361c19854060b0609c12070404c0a01068000802

@[expose] noncomputable def inRP (P : Nat) : Bool := inP P || inP (pc 315 9 uP P)

end CertificateChecks.KernelCensus.J2K

end
