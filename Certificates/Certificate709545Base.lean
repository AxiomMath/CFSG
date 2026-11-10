module

public import Certificates.Data.OmegaSevenMax.Defs
public import Certificates.Data.OmegaSevenMax.RootCodes

@[expose] public section

namespace Certificates.OmegaSevenMax

def rootSetV : Finset V := (rootCodes.map decV).toFinset

def hV (j : Fin 6) : V → V := rxV (decV 1) ∘ rxV (decV (3 ^ (j.val + 1)))

def pairWord (L : List (V × V)) : V → V := L.foldr (fun x f => rxV x.1 ∘ rxV x.2 ∘ f) id

def hWord (w : List (Fin 6)) : V → V := w.foldr (fun j f => hV j ∘ f) id

end Certificates.OmegaSevenMax

namespace Certificates


end Certificates

public section

namespace Certificates

end Certificates

end

namespace Certificates


end Certificates

end
