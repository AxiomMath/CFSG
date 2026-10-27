module

public import CFSG.LocalAnalysis.StandardType.GGL45NtAssembly
public import CFSG.LocalAnalysis.StandardType.GGL45NtAutAsm
public import CFSG.LocalAnalysis.StandardType.GGL45NtSimp
public import CFSG.LocalAnalysis.StandardType.GGL45FamCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45E67Core (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R),
    commutator K = ⊤ → ∀ (ψ : MulAut K) (E : Subgroup (MulAut K)),
      GGL45TorusKGHyp p lab I F θ ψ E → GGL45TorusH123 p I θ ψ E

theorem ggL45TorusHKnownFormsOn_e67_of_core
    (hcore : GGL45NtOn GGL45FamE67 GGL45E67Core) : GGL45TorusHKnownFormsOn GGL45FamE67 := by
  have h4 : GGL45NtH4On GGL45FamE67 :=
    ggL45NtH4On_of_aut (ggL45NtSimpOn_all _) (ggL45NtAutOn_notD4Three.antitone
      fun _ _ h hD => by
        rcases h.2 with h' | h' | h' <;> rw [h'] at hD <;> exact absurd hD.1 (by decide))
  exact (hcore.and h4).mono fun _ _ _ _ _ _ _ h K _ _ θ hK _ ψ E hyp =>
    ggL45TorusH_of_parts (h.1 K θ hK ψ E hyp) (h.2 K θ hK ψ E hyp)

end CFSG.StandardType
